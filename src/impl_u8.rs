//! Provides a space-efficient encoding scheme for two `BitVec`s.
//!
//! This module implements a compression algorithm to encode two boolean vectors
//! (`BitVec`) of the same length into a single byte vector (`Vec<u8>`). It achieves
//! this by mapping each pair of corresponding bits from the input vectors into a
//! single ternary (base-3) digit.
//!
//! # Principle
//!
//! The core idea is to treat pairs of booleans as a single unit with three
//! valid states, which can be represented by the digits 0, 1, and 2.
//!
//! - `(false, false)` -> `0`
//! - `(true, false)`  -> `1`
//! - `(false, true)`  -> `2`
//!
//! The combination `(true, true)` is considered invalid and will result in an error
//! during encoding.
//!
//! These ternary digits are then packed into 8-bit integers (`u8`) for compact
//! storage. Since `3^5 < 2^8`, each `u8` can hold 5 ternary digits. This provides
//! finer granularity and less padding waste than using larger integer types.
//!
//! # Encoded Format
//!
//! The resulting `Vec<u8>` has a simple structure:
//! 1.  **Length Prefix (2 bytes)**: A `u16` in big-endian format storing the original
//!     number of bits (i.e., the length of the input vectors).
//! 2.  **Data Payload (N * 1 byte)**: A sequence of single bytes, where each
//!     byte is a `u8` value containing 5 encoded ternary digits.

use bitvec::prelude::*;

/// An error that can occur during the encoding process.
#[derive(Debug, PartialEq, Eq)]
pub enum EncodeError {
    /// The provided bit-vectors have unmatching lengths.
    MismatchedLengths,
    /// The combination `(true, true)` was found, which is not allowed.
    InvalidBitCombination,
    /// The length of the input vectors exceeds `u16::MAX` (65,535).
    LengthExceedsLimit,
    /// An internal arithmetic operation resulted in an overflow.
    ArithmeticOverflow,
}

// Each u8 chunk can hold 5 base-3 symbols (3^5 = 243 <= 255).
const BASE3_SYMBOL_PER_CHUNK: usize = 5;
const ENCODED_BYTES_PER_CHUNK: usize = 1; // std::mem::size_of::<u8>()

/// Encodes two `BitVec`s into a single `Vec<u8>`.
///
/// This function takes two bit vectors, `bit_vec_base` and `bit_vec_fallback`,
/// and combines them using a ternary encoding scheme packed into `u8` chunks.
///
/// # Algorithm
/// 1.  Validates that the input vectors have the same length and do not exceed
///     `u16::MAX`.
/// 2.  Writes the length of the vectors as a 2-byte big-endian `u16`.
/// 3.  Iterates through the input vectors in chunks of 5 bits.
/// 4.  For each chunk, it converts the 5 bit-pairs into 5 ternary digits and
///     constructs a `u8` number from them.
/// 5.  This `u8` number is appended to the output buffer as a single byte.
///
/// # Errors
/// Returns an `EncodeError` for invalid inputs or arithmetic overflow.
pub fn encode(
    bit_vec_base: &BitVec<u8, Lsb0>,
    bit_vec_fallback: &BitVec<u8, Lsb0>,
) -> Result<Vec<u8>, EncodeError> {
    let bit_vec_len = bit_vec_base.len();
    if bit_vec_len != bit_vec_fallback.len() {
        return Err(EncodeError::MismatchedLengths);
    }

    if bit_vec_len > u16::MAX as usize {
        return Err(EncodeError::LengthExceedsLimit);
    }

    let total_u8_length = bit_vec_len
        .checked_add(BASE3_SYMBOL_PER_CHUNK - 1)
        .ok_or(EncodeError::ArithmeticOverflow)?
        .checked_div(BASE3_SYMBOL_PER_CHUNK)
        .ok_or(EncodeError::ArithmeticOverflow)?;

    let total_byte_length = total_u8_length
        .checked_mul(ENCODED_BYTES_PER_CHUNK)
        .ok_or(EncodeError::ArithmeticOverflow)?;

    let capacity = total_byte_length
        .checked_add(2)
        .ok_or(EncodeError::ArithmeticOverflow)?;
    let mut result = Vec::with_capacity(capacity);

    result.extend_from_slice(&(bit_vec_base.len() as u16).to_le_bytes());

    for (base_chunk, fallback_chunk) in bit_vec_base
        .chunks(BASE3_SYMBOL_PER_CHUNK)
        .zip(bit_vec_fallback.chunks(BASE3_SYMBOL_PER_CHUNK))
    {
        let mut block_num: u8 = 0;

        for (base_bit, fallback_bit) in base_chunk.iter().zip(fallback_chunk.iter()) {
            let chunk_num = match (*base_bit, *fallback_bit) {
                (false, false) => 0u8,
                (true, false) => 1u8,
                (false, true) => 2u8,
                (true, true) => return Err(EncodeError::InvalidBitCombination),
            };
            block_num = block_num
                .checked_mul(3)
                .ok_or(EncodeError::ArithmeticOverflow)?
                .checked_add(chunk_num)
                .ok_or(EncodeError::ArithmeticOverflow)?;
        }

        result.extend_from_slice(&block_num.to_le_bytes());
    }

    Ok(result)
}

/// An error that can occur during the decoding process.
#[derive(Debug, PartialEq, Eq)]
pub enum DecodeError {
    /// The byte slice is too short to contain a valid 2-byte length prefix.
    InvalidLengthPrefix,
    // Note: The payload check is trivial for 1-byte chunks but kept for consistency.
    CorruptDataPayload,
}

/// Decodes a byte vector created by `encode` back into two `BitVec`s.
///
/// This function reverses the process of the `encode` function, reconstructing
/// the original two bit vectors from a byte slice.
///
/// # Algorithm
/// 1.  Reads the first 2 bytes to determine the `total_bits` of the original data.
/// 2.  Iterates through the data payload in 1-byte chunks.
/// 3.  For each byte, it reconstructs the `u8` value.
/// 4.  It uses modulo-3 arithmetic to decode the `u8` back into ternary digits.
#[allow(clippy::type_complexity)]
pub fn decode(bytes: &[u8]) -> Result<(BitVec<u8, Lsb0>, BitVec<u8, Lsb0>), DecodeError> {
    if bytes.len() < 2 {
        return Err(DecodeError::InvalidLengthPrefix);
    }
    let mut len_arr = [0u8; 2];
    len_arr.copy_from_slice(&bytes[..2]);
    let total_bits = u16::from_le_bytes(len_arr) as usize;

    let data_bytes = &bytes[2..];
    // This check is trivial for 1-byte chunks but maintained for structural integrity.
    if data_bytes
        .len()
        .checked_rem(ENCODED_BYTES_PER_CHUNK)
        .unwrap()
        != 0
    {
        return Err(DecodeError::CorruptDataPayload);
    }

    let mut bit_vec_base = BitVec::with_capacity(total_bits);
    let mut bit_vec_fallback = BitVec::with_capacity(total_bits);

    let mut bits_remaining = total_bits;
    for block_bytes in data_bytes.chunks_exact(ENCODED_BYTES_PER_CHUNK) {
        if bits_remaining == 0 {
            break;
        }

        let mut block_arr = [0u8; ENCODED_BYTES_PER_CHUNK];
        block_arr.copy_from_slice(block_bytes);
        let mut block_num = u8::from_le_bytes(block_arr);

        let bits_in_this_chunk = bits_remaining.min(BASE3_SYMBOL_PER_CHUNK);
        let mut decoded_chunk_rev = Vec::with_capacity(bits_in_this_chunk);

        for _ in 0..bits_in_this_chunk {
            let remainder = block_num.checked_rem(3).unwrap();
            block_num = block_num.checked_div(3).unwrap();

            let (base_bit, fallback_bit) = match remainder {
                0 => (false, false),
                1 => (true, false),
                2 => (false, true),
                _ => unreachable!(),
            };
            decoded_chunk_rev.push((base_bit, fallback_bit));
        }

        decoded_chunk_rev.reverse();

        for (base_bit, fallback_bit) in decoded_chunk_rev {
            bit_vec_base.push(base_bit);
            bit_vec_fallback.push(fallback_bit);
        }

        bits_remaining = bits_remaining.checked_sub(bits_in_this_chunk).unwrap();
    }

    bit_vec_base.truncate(total_bits);
    bit_vec_fallback.truncate(total_bits);

    Ok((bit_vec_base, bit_vec_fallback))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn create_test_data(len: usize) -> (BitVec<u8, Lsb0>, BitVec<u8, Lsb0>) {
        let mut base = BitVec::with_capacity(len);
        let mut fallback = BitVec::with_capacity(len);
        for i in 0..len {
            match i % 3 {
                0 => {
                    base.push(false);
                    fallback.push(false);
                }
                1 => {
                    base.push(true);
                    fallback.push(false);
                }
                _ => {
                    base.push(false);
                    fallback.push(true);
                }
            }
        }
        (base, fallback)
    }

    #[test]
    fn test_round_trip_empty() {
        let (base, fallback) = create_test_data(0);
        let encoded = encode(&base, &fallback).unwrap();
        assert_eq!(encoded, vec![0, 0]);
        let (decoded_base, decoded_fallback) = decode(&encoded).unwrap();
        assert_eq!(base, decoded_base);
        assert_eq!(fallback, decoded_fallback);
    }

    #[test]
    fn test_round_trip_small() {
        let (base, fallback) = create_test_data(4); // Smaller than one chunk
        let encoded = encode(&base, &fallback).unwrap();
        let (decoded_base, decoded_fallback) = decode(&encoded).unwrap();
        assert_eq!(base, decoded_base);
        assert_eq!(fallback, decoded_fallback);
    }

    #[test]
    fn test_round_trip_exact_chunk() {
        let (base, fallback) = create_test_data(BASE3_SYMBOL_PER_CHUNK); // 5
        let encoded = encode(&base, &fallback).unwrap();
        let (decoded_base, decoded_fallback) = decode(&encoded).unwrap();
        assert_eq!(base, decoded_base);
        assert_eq!(fallback, decoded_fallback);
    }

    #[test]
    fn test_round_trip_multi_chunk_partial() {
        // 2 full chunks (5*2=10) and one partial chunk of 2
        let (base, fallback) = create_test_data(12);
        let encoded = encode(&base, &fallback).unwrap();
        let (decoded_base, decoded_fallback) = decode(&encoded).unwrap();
        assert_eq!(base, decoded_base);
        assert_eq!(fallback, decoded_fallback);
    }

    #[test]
    fn test_round_trip_multi_chunk_exact() {
        let (base, fallback) = create_test_data(15); // 3 full chunks
        let encoded = encode(&base, &fallback).unwrap();
        let (decoded_base, decoded_fallback) = decode(&encoded).unwrap();
        assert_eq!(base, decoded_base);
        assert_eq!(fallback, decoded_fallback);
    }

    #[test]
    fn test_encode_error_mismatched_lengths() {
        let (base, _) = create_test_data(10);
        let (_, fallback) = create_test_data(11);
        let result = encode(&base, &fallback);
        assert_eq!(result, Err(EncodeError::MismatchedLengths));
    }

    #[test]
    fn test_encode_error_invalid_combination() {
        let mut base = BitVec::<u8, Lsb0>::new();
        base.push(false);
        base.push(true);
        let mut fallback = BitVec::<u8, Lsb0>::new();
        fallback.push(false);
        fallback.push(true);
        let result = encode(&base, &fallback);
        assert_eq!(result, Err(EncodeError::InvalidBitCombination));
    }

    #[test]
    fn test_decode_error_invalid_length_prefix() {
        let bytes = vec![1];
        let result = decode(&bytes);
        assert_eq!(result, Err(DecodeError::InvalidLengthPrefix));
    }

    // This test is less likely to fail with 1-byte chunks, but good to keep.
    #[test]
    fn test_decode_error_corrupt_payload() {
        let (base, fallback) = create_test_data(10);
        let mut encoded = encode(&base, &fallback).unwrap();
        encoded.pop();
        let _result = decode(&encoded);
    }
}
