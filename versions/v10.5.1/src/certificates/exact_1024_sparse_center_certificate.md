# Exact 1024-bit Sparse-Center Certificate

- seed: `20260701`
- r: `512`
- z bit positions: `[2, 30, 38, 66]`
- Hamming weight: `4`
- candidate set size: `10668000`
- log2 candidate set size: `23.346786`
- bit lengths: p=511, q=513, n=1024
- Fermat iteration bit length: `510`

Checks:

```json
{
  "p_is_prime": true,
  "q_is_prime": true,
  "n_equals_pq": true,
  "center_A_equals_half_sum": true,
  "shell_identity_A2_minus_n_equals_B2": true,
  "z_equals_A_minus_2r": true,
  "z_hamming_weight": 4,
  "n_bit_length_exact_1024": true
}
```

The full decimal values are in `exact_1024_sparse_center_certificate.json` and the LaTeX appendix snippet is in `exact_1024_sparse_center_certificate.tex`.
