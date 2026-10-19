# Protected-layer inverse-trace prime-seed screen

This script implements the auxiliary diagnostic described in Section
`Protected-Layer Inverse-Trace Prime-Seed Screen` of the v5.10.16 draft.

For an odd modulus `n`, it computes the protected layer

```text
r_min = min r with 2^(2r) >= n
R     = 2*r_min
x     = 2R
M     = 2^x = 2^(2R)
a     = n^(-1) mod M
```

For every seed `s0`, usually prime seeds, it computes

```text
alpha0(s0)  = -s0^2 * a mod M
lambda0(s0) = (alpha0(s0)*n + s0^2) / M
```

Then it checks whether `lambda0=1`, whether `lambda0` is a square `u^2`, and
whether the associated gcd tests reveal a non-trivial factor.

This is a bounded diagnostic/statistical screen, not a complete factorization
algorithm.

## Recommended PowerShell launch

```powershell
mkdir logs -ErrorAction SilentlyContinue
mkdir stats -ErrorAction SilentlyContinue

python .\inverse_trace_prime_seed_screen.py `
  --n $RSA260 `
  --seed-mode primes `
  --seed-bound 1000000 `
  --u-bound 1000000 `
  --near-square-top 20 `
  --csv ".\stats\rsa260_inverse_trace_hits.csv" `
  --json-summary ".\stats\rsa260_inverse_trace_summary.json" `
  --tee-log ".\logs\rsa260_inverse_trace_prime_seed.log"
```

## Parameters

- `--n`: odd modulus. Accepts decimal, hex, or `@file`.
- `--r-min`: manually override `r_min`.
- `--R`: manually override `R`; default is `2*r_min`.
- `--x`: manually override the modulus exponent; default is `2R`.
- `--seed-mode`: `primes`, `odd-primes`, `integers`, or `odd-integers`.
- `--seed-bound`: inclusive upper bound for seeds.
- `--max-seeds`: stop after this many generated seeds.
- `--u-bound`: only gcd-test square hits with `u <= u_bound`.
- `--csv`: write CSV output. By default only hits are written.
- `--csv-all`: write every seed row to CSV.
- `--json-summary`: write summary and hits to JSON.
- `--near-square-top`: record the closest values of `lambda0` to a square.
- `--progress-every`: print progress every N seeds.
- `--tee-log`: duplicate output to terminal and log file.
- `--tee-append`: append to the log instead of overwriting.

## Interpretation

A positive output is directly verifiable. A negative output is expected for
RSA-like moduli under polynomially bounded seed and multiplier budgets. The
main purpose is to collect statistics at the protected layer `x=2R`.
- `--allow-odd-x`: permit an odd manually supplied `--x`; the default protected layer is even and is the intended mode.
