"""dyadic_diagnostic.py
Textbook companion script — Chapter 2, "The Binary 'Passport' of a Number:
Two-Adic Valuation and the Valence Identity" (Practice & Reproducibility
Laboratory).

This is the self-contained teaching code printed in Chapter 2. It implements
the two-adic valuation nu2(x) (the number of trailing zero bits of x) without
external packages, and a diagnostic diagnose_shell(n, r, s, alpha) that:

  1. checks the dyadic-triple identity (2^r)^2 - s^2 = alpha * n,
  2. checks the valence identity nu2(alpha) == 2 * nu2(s),
  3. attempts gcd(2^r - s, n) and reports a non-trivial factor pair if found.

As the chapter text states explicitly, this is a self-contained textbook
exercise deliberately illustrating that identity validity, the valence
check, and successful non-trivial factor recovery are three distinct
conditions (a passing valence check does not imply a passing identity, and
a passing identity does not imply a non-trivial gcd). It is not presented
as a byte-for-byte reproduction of a file inside a specific archived Zenodo
source package. The corresponding research-grade two-adic admissibility
material lives on the v5.10.18 Zenodo record and in this repository's
``versions/v05.10.18/src/`` folder, archived byte-for-byte with that record.

Series concept DOI (always latest): https://doi.org/10.5281/zenodo.20306132
Chapter 2 cites the record (Dyadic Shells v5.10.18): https://doi.org/10.5281/zenodo.20484456
"""

from math import gcd


def nu2(n: int) -> int:
    if n == 0:
        raise ValueError("nu2(0) is infinite")
    n = abs(n)
    return (n & -n).bit_length() - 1


def diagnose_shell(n: int, r: int, s: int, alpha: int):
    if n <= 1 or n % 2 == 0 or r < 1:
        raise ValueError("Need odd n > 1 and r >= 1")
    if not (0 < abs(s) < (1 << r)) or alpha <= 0:
        raise ValueError("Degenerate or out-of-range parameters")
    value = (1 << (2 * r)) - s * s
    valid = (value == alpha * n)
    valence_ok = (nu2(alpha) == 2 * nu2(s))
    factor = gcd((1 << r) - s, n) if valid else None
    nontrivial = factor is not None and 1 < factor < n
    return valid, valence_ok, (factor, n // factor) if nontrivial else None


if __name__ == "__main__":
    assert nu2(24) == 3 and nu2(-40) == 3
    assert diagnose_shell(15, 2, 1, 1) == (True, True, (3, 5))
    assert diagnose_shell(15, 4, 4, 16) == (True, True, (3, 5))
    assert diagnose_shell(15, 4, 1, 17) == (True, True, None)
    assert diagnose_shell(15, 4, 4, 8) == (False, False, None)
    print("nu2(24) =", nu2(24), " nu2(-40) =", nu2(-40))
    print("diagnose_shell(15, 2, 1, 1)  =", diagnose_shell(15, 2, 1, 1))
    print("diagnose_shell(15, 4, 4, 16) =", diagnose_shell(15, 4, 4, 16))
    print("diagnose_shell(15, 4, 1, 17) =", diagnose_shell(15, 4, 1, 17))
    print("diagnose_shell(15, 4, 4, 8)  =", diagnose_shell(15, 4, 4, 8))
    print("All Chapter 2 laboratory assertions passed.")
