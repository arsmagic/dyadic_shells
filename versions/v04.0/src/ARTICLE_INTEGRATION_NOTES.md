# v0.4 Integration Notes

Recommended changes to the article draft:

1. **Section 9:** Use a per-candidate diagnostic score `T_A` and a maximum statistic `T_max`, rather than only aggregate score `T`. This avoids signal dilution when the candidate set is large.
2. **False-positive bound:** Include the union-bound estimate `Pr(false full hit) <= |A| * product_m |QR(m)|/m` under the random-residue model.
3. **Empirical table:** Insert `tables/diagnostics_table.tex` after the theoretical diagnostic bound.
4. **Sieve section:** State clearly that the sieve keeps candidates for which `A^2 - alpha n` is a quadratic residue modulo each small prime. It must not require the expression to be zero modulo the prime.
5. **Sieve benchmark:** Insert `tables/sieve_table.tex` after the survival-rate proposition.
6. **Appendix:** Insert `tables/example_1024_certificate.tex` and refer to the full JSON certificate.
7. **Terminology:** Use `center-compressible semiprimes`, `positive controls`, `weak-generator audit`, and `random-residue model`. Avoid `absolute resistance` claims.
8. **Small-alpha theorem:** State factor recovery via `gcd(A+s,n)` and `gcd(A-s,n)`; coefficients are structural witnesses, not needed for the GCD recovery itself.
