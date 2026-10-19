# Dyadic Shells — Structural Diagnostics for Semiprime / RSA Factorization Screening

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20306132.svg)](https://doi.org/10.5281/zenodo.20306132)

A solo preprint series by **Arsen A. Khachatryan** (ORCID [0009-0006-7629-3833](https://orcid.org/0009-0006-7629-3833), SibarS Labs) on
*dyadic-shell* structural diagnostics in semiprime arithmetic and weak-key analysis — representing a semiprime
`n = pq` through a dyadic anchor (`2^(2r) - s^2 = alpha*n`, later the anchored sparse-offset form `2^r + Z`) and
studying exact, calibrated screens for hypothesised generator defects. The work is **not** a general attack on RSA;
positive controls are planted by the author.

Every version in this repository is archived and citable on **Zenodo**. The directory
[`versions/`](./versions) mirrors the release history; each version folder has a `README.md` that points to its
Zenodo record and lists all archived files, and — where available — commits the accompanying source code.

## Versions

The concept DOI **[10.5281/zenodo.20306132](https://doi.org/10.5281/zenodo.20306132)** always resolves to the newest
version. The nine releases of the cycle:

| Version | Date | Record (version DOI) | Folder | Topic |
|---|---|---|---|---|
| **4.0** | 2026-05-23 | [10.5281/zenodo.20350133](https://doi.org/10.5281/zenodo.20350133) | [versions/v04.0](./versions/v04.0) | Dyadic-shell framework; structured-prime diagnostics |
| **5.10.18** | 2026-06-01 | [10.5281/zenodo.20484456](https://doi.org/10.5281/zenodo.20484456) | [versions/v05.10.18](./versions/v05.10.18) | Two-adic admissibility; trivial-branch obstructions |
| **6.5.7** | 2026-06-11 | [10.5281/zenodo.20636900](https://doi.org/10.5281/zenodo.20636900) | [versions/v06.5.7](./versions/v06.5.7) | Two-adic obstruction theory; algebraic limits |
| **7.1.5** | 2026-06-16 | [10.5281/zenodo.20710574](https://doi.org/10.5281/zenodo.20710574) | [versions/v07.1.5](./versions/v07.1.5) | Composition & quadratic recombination of triples |
| **8.5.5** | 2026-06-27 | [10.5281/zenodo.20951187](https://doi.org/10.5281/zenodo.20951187) | [versions/v08.5.5](./versions/v08.5.5) | Shell correspondences & equivalence relations |
| **9.2.2** | 2026-06-28 | [10.5281/zenodo.20999427](https://doi.org/10.5281/zenodo.20999427) | [versions/v09.2.2](./versions/v09.2.2) | Base-shell diagnostics for congruences of squares |
| **10.5.1** | 2026-08-22 | [10.5281/zenodo.22055615](https://doi.org/10.5281/zenodo.22055615) | [versions/v10.5.1](./versions/v10.5.1) | Center-compressible semiprimes; benchmarks |
| **11.0.3** | 2026-10-04 | [10.5281/zenodo.23135512](https://doi.org/10.5281/zenodo.23135512) | [versions/v11.0.3](./versions/v11.0.3) | Anchored sparse-offset screening; exact sieve null model |
| **11.5.17** | 2026-10-17 | [10.5281/zenodo.23432486](https://doi.org/10.5281/zenodo.23432486) | [versions/v11.5.17](./versions/v11.5.17) | **Latest** — FP-MITM beyond the lattice; cost-model auditor |

All nine records are cross-linked on Zenodo (`continues` / `isContinuedBy`) so a reader can walk the series in either
direction from any entry point.

## Repository layout

```
README.md                 this index
CITATION.cff              cite the series (concept DOI = always latest)
versions/
  v04.0/ … v11.5.17/       one folder per release
    README.md             version metadata, DOI, and links to every file on Zenodo
    src/                  accompanying source code (where committed)
Test logs/                heavy v11-era diagnostic test logs (reference)
```

## Code availability

The source code and data for each version are permanently archived on its Zenodo record and linked from that
version's `README.md`. Code committed directly in this repository: **v4.0, v5.10.18, v9.2.2, v10.5.1, v11.0.3, v11.5.17**
(under their `src/` folders). **v6.5.7** and **v8.5.5** are theory papers with no accompanying code; **v7.1.5**'s
code is linked on its Zenodo record. Every version's files remain archived and linked on its Zenodo record.

## How to cite the series

Cite the concept DOI to reference the series as a whole (resolves to the latest version), or a version DOI for a
specific release (see each version folder).

```bibtex
@misc{khachatryan_dyadicshell,
  author       = {Khachatryan, Arsen A.},
  title        = {Dyadic Shells: Structural Diagnostics in Semiprime Arithmetic (preprint series)},
  howpublished = {Zenodo},
  doi          = {10.5281/zenodo.20306132},
  url          = {https://doi.org/10.5281/zenodo.20306132}
}
```

## Scope note

Three earlier iterations that precede release 4 (Zenodo records 20306133, 20327298, 20342553) are superseded and are
deliberately **not** part of this cycle; they are not referenced here.

## License

Creative Commons Attribution–NonCommercial 4.0 International (CC BY-NC 4.0), as for the preprints themselves.
