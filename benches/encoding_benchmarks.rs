use bitvec::prelude::*;
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use solana_base3_encoding::{impl_u128, impl_u64, impl_u8};

// A helper function to generate consistent test data for the benchmarks.
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

fn benchmark_encoding(c: &mut Criterion) {
    let mut group = c.benchmark_group("Ternary Encoding");

    // Test with various input sizes to see how performance scales.
    for size in [10, 100, 1_000, 4_096, 10_000].iter() {
        let (base, fallback) = create_test_data(*size);

        // --- Benchmark u8 implementation ---
        group.bench_with_input(BenchmarkId::new("Encode (u8)", size), size, |b, _| {
            b.iter(|| impl_u8::encode(black_box(&base), black_box(&fallback)))
        });

        // --- Benchmark u64 implementation ---
        group.bench_with_input(BenchmarkId::new("Encode (u64)", size), size, |b, _| {
            b.iter(|| impl_u64::encode(black_box(&base), black_box(&fallback)))
        });

        // --- Benchmark u128 implementation ---
        group.bench_with_input(BenchmarkId::new("Encode (u128)", size), size, |b, _| {
            b.iter(|| impl_u128::encode(black_box(&base), black_box(&fallback)))
        });
    }
    group.finish();
}

fn benchmark_decoding(c: &mut Criterion) {
    let mut group = c.benchmark_group("Ternary Decoding");

    for size in [10, 100, 1_000, 4_096, 10_000].iter() {
        let (base, fallback) = create_test_data(*size);

        // Pre-encode the data for each implementation so we only measure decoding.
        let encoded_u8 = impl_u8::encode(&base, &fallback).unwrap();
        let encoded_u64 = impl_u64::encode(&base, &fallback).unwrap();
        let encoded_u128 = impl_u128::encode(&base, &fallback).unwrap();

        // --- Benchmark u8 implementation ---
        group.bench_with_input(BenchmarkId::new("Decode (u8)", size), size, |b, _| {
            b.iter(|| impl_u8::decode(black_box(&encoded_u8)))
        });

        // --- Benchmark u64 implementation ---
        group.bench_with_input(BenchmarkId::new("Decode (u64)", size), size, |b, _| {
            b.iter(|| impl_u64::decode(black_box(&encoded_u64)))
        });

        // --- Benchmark u128 implementation ---
        group.bench_with_input(BenchmarkId::new("Decode (u128)", size), size, |b, _| {
            b.iter(|| impl_u128::decode(black_box(&encoded_u128)))
        });
    }
    group.finish();
}

// Register the benchmark groups with Criterion
criterion_group!(benches, benchmark_encoding, benchmark_decoding);
criterion_main!(benches);
