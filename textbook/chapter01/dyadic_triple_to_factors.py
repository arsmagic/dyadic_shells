"""dyadic_triple_to_factors.py
Textbook companion script — Chapter 1, "From Pierre de Fermat to Maurice
Kraitchik: Geometry of Semiprime Numbers" (Practice & Reproducibility
Laboratory).

This is the self-contained teaching code printed in Chapter 1. It verifies
a candidate dyadic triple (r, s, alpha) against an odd modulus n, i.e. checks

    (2^r)^2 - s^2 = alpha * n

and, if the identity holds, extracts a non-trivial divisor via
gcd(2^r - s, n) when one exists. As the chapter text states explicitly:
this routine illustrates the verification step of Chapter 1's Figure 3
("Dyadic triple verification is not the same task as discovering a
factor-revealing triple") — it is pedagogical code for the book, not a
byte-for-byte reproduction of any file inside a specific archived Zenodo
source package. The corresponding research-grade scanners that search for
(r, s, alpha) triples live under this repository's versioned ``src/``
folders (e.g. ``versions/v11.0.3/src/dyadic_kz_scan.py``,
``versions/v11.5.17/src/dyadic_kz_scan.py``), which are archived
byte-for-byte with their respective Zenodo records.

Series concept DOI (always latest): https://doi.org/10.5281/zenodo.20306132
Chapter 1 cites the record: https://doi.org/10.5281/zenodo.23432486
"""

from math import gcd


def extract_factors(r: int, s: int, alpha: int, n: int):
    if r < 0 or n < 3 or n % 2 == 0:
        raise ValueError("Expected r >= 0 and odd n >= 3")
    anchor = 1 << r
    if anchor * anchor - s * s != alpha * n:
        raise ValueError("The proposed triple fails the identity")
    g = gcd(anchor - s, n)
    return (g, n // g) if 1 < g < n else None


if __name__ == "__main__":
    assert extract_factors(2, 1, 1, 15) == (3, 5)
    assert extract_factors(4, 1, 17, 15) is None
    print("extract_factors(2, 1, 1, 15)  =", extract_factors(2, 1, 1, 15))
    print("extract_factors(4, 1, 17, 15) =", extract_factors(4, 1, 17, 15))
    print("All Chapter 1 laboratory assertions passed.")
