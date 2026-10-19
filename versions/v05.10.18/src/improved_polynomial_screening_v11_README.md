# Improved Dyadic-Shell Screening v11

This version adds built-in tee logging.

## New logging switches

```text
--tee-log PATH      write the same stdout/stderr output both to the terminal and to PATH
--tee-append        append to --tee-log instead of overwriting it
```

This is useful on Windows/PowerShell because you no longer need:

```powershell
2>&1 | Tee-Object -FilePath .\screening.log
```

The script itself can now duplicate the output.

## Recommended PowerShell launch: square-multiplier scan

```powershell
python .\improved_polynomial_screening_v11.py `
  --n $N `
  --square-multiplier-scan `
  --u-bound 64 `
  --full-range `
  --partial-fx `
  --factor-method sympy `
  --trial-bound 1000000 `
  --tail-top-per-u 16 `
  --parallel `
  --workers 4 `
  --quiet `
  --tee-log ".\logs\screening_v11.log"
```

## RSA-260 example

```powershell
$RSA260 = "22112825529529666435281085255026230927612089502470015394413748319128822941402001986512729726569746599085900330031400051170742204560859276357953757185954298838958709229238491006703034124620545784566413664540684214361293017694020846391065875914794251435144458199"

mkdir logs -ErrorAction SilentlyContinue

python .\improved_polynomial_screening_v11.py `
  --n $RSA260 `
  --square-multiplier-scan `
  --u-bound 64 `
  --full-range `
  --partial-fx `
  --factor-method sympy `
  --trial-bound 1000000 `
  --tail-top-per-u 16 `
  --parallel `
  --workers 4 `
  --quiet `
  --tee-log ".\logs\rsa260_square_multiplier_v11.log"
```

## RSA-270 / RSA-896 style example

```powershell
mkdir logs -ErrorAction SilentlyContinue

python .\improved_polynomial_screening_v11.py `
  --n $RSA270 `
  --square-multiplier-scan `
  --u-bound 64 `
  --full-range `
  --partial-fx `
  --factor-method sympy `
  --trial-bound 1000000 `
  --tail-top-per-u 16 `
  --parallel `
  --workers 4 `
  --quiet `
  --tee-log ".\logs\rsa270_square_multiplier_v11.log"
```

## More conservative launch

Use a smaller multiplier bound and fewer tail pairs:

```powershell
python .\improved_polynomial_screening_v11.py `
  --n $N `
  --square-multiplier-scan `
  --u-bound 16 `
  --full-range `
  --partial-fx `
  --factor-method sympy `
  --trial-bound 1000000 `
  --tail-top-per-u 8 `
  --parallel `
  --workers 4 `
  --quiet `
  --tee-log ".\logs\screening_conservative_v11.log"
```

## Heavier launch

Use a larger multiplier bound and more ranked tail points:

```powershell
python .\improved_polynomial_screening_v11.py `
  --n $N `
  --square-multiplier-scan `
  --u-bound 256 `
  --full-range `
  --partial-fx `
  --factor-method sympy `
  --trial-bound 1000000 `
  --tail-top-per-u 32 `
  --parallel `
  --workers 4 `
  --quiet `
  --tee-log ".\logs\screening_heavy_v11.log"
```

## Append to an existing log

```powershell
python .\improved_polynomial_screening_v11.py `
  --n $N `
  --square-multiplier-scan `
  --u-bound 64 `
  --full-range `
  --partial-fx `
  --factor-method sympy `
  --trial-bound 1000000 `
  --tail-top-per-u 16 `
  --parallel `
  --workers 4 `
  --quiet `
  --tee-log ".\logs\screening_v11.log" `
  --tee-append
```

## Legacy lambda = 1 scan

To reproduce the older one-dimensional scan without square multipliers:

```powershell
python .\improved_polynomial_screening_v11.py `
  --n $N `
  --full-range `
  --partial-fx `
  --factor-method sympy `
  --trial-bound 1000000 `
  --parallel `
  --workers 4 `
  --quiet `
  --tee-log ".\logs\legacy_lambda1_v11.log"
```

## Notes

- `--tee-log` duplicates stdout and stderr to the terminal and log file.
- `--quiet` suppresses per-pair detail but still prints `RUN START`, `SUMMARY`, and `RUN END`.
- The square-multiplier layer scans representatives

  \[
  F_{x,u}=u^2 2^x-n
  \]

  with \(\lambda=u^2\).
- The scan remains a bounded diagnostic screen, not a completeness certificate.
- Positive outputs are verified by exact arithmetic and gcd tests.
