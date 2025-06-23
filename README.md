# base3-encoding-tests

Tests to encode two bit vectors into base3 encodings for the purpose of Solana
alpenglow certificates.

The encoding/decoding functions are implemented using u8, u64, and u128 blocks.
To compare the performance of these three encoding/decoding functions, run
`cargo bench` after cloning the repository.

For bit vectors of length 4096, we have the following results:

```
Machine Specs:
CPU: AMD EPYC 9354P (64) @ 3.797GHz
GPU: c2:00.0 Matrox Electronics Systems Ltd. Integrated Matrox G200eW3 Graphics Controlle
Memory: 1812MiB / 773197MiB
```

```
Ternary Encoding/Encode (u8)/4096
                        time:   [10.090 µs 10.095 µs 10.099 µs]
Found 5 outliers among 100 measurements (5.00%)
  4 (4.00%) low mild
  1 (1.00%) high mild
Ternary Encoding/Encode (u64)/4096
                        time:   [8.1956 µs 8.1962 µs 8.1968 µs]
Found 2 outliers among 100 measurements (2.00%)
  1 (1.00%) low mild
  1 (1.00%) high mild
Ternary Encoding/Encode (u128)/4096
                        time:   [11.372 µs 11.374 µs 11.376 µs]
Found 15 outliers among 100 measurements (15.00%)
  3 (3.00%) low severe
  3 (3.00%) low mild
  4 (4.00%) high mild
  5 (5.00%) high severe

Ternary Decoding/Decode (u8)/4096
                        time:   [33.096 µs 33.111 µs 33.127 µs]
Found 1 outliers among 100 measurements (1.00%)
  1 (1.00%) high mild
Ternary Decoding/Decode (u64)/4096
                        time:   [27.125 µs 27.135 µs 27.146 µs]
Found 4 outliers among 100 measurements (4.00%)
  2 (2.00%) low mild
  2 (2.00%) high mild
Ternary Decoding/Decode (u128)/4096
                        time:   [38.147 µs 38.157 µs 38.167 µs]
Found 3 outliers among 100 measurements (3.00%)
  2 (2.00%) low mild
  1 (1.00%) high mild
```

