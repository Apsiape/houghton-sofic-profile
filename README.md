# Houghton's group H_3 has superpolynomial sofic profile

Seth Douglas and Nidhal Mghirbi — November 2026, version 1.3.0.

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23027624.svg)](https://doi.org/10.5281/zenodo.23027624)

[Read the manuscript](paper.pdf) · [TeX source](paper.tex) ·
[Lean core and scope](lean/README.md) · [Certificate checks](verification/README.md)

## Abstract

How many points does a permutation model of a group need? Cornulier's sofic profile measures the size needed to imitate a fixed finite piece at a given accuracy. We show that Houghton's finitely presented elementary amenable group on three rays has a finite piece with superpolynomial profile. The unconditional lower exponent is one divided by one plus the base-two logarithm of 107; the upper bound is exponential in the square root of the accuracy parameter times its logarithm.

The lower bound uses entropy carried by approximately commuting copies of the symmetric group on three letters, with polynomial commutator fillings certified by a doubling self-similarity. A stronger sweep criterion charges a whole ordered suffix at once and rounds permutations in Hamming distance. Conditionally, a quadratic Dehn function, or a quadratic bound for block coherence with at most three letters per position, gives a square-root lower exponent, matching the upper exponent up to a logarithm. We prove an all-scale quadratic lower bound for block coherence; its quadratic upper bound remains open.

Every homomorphism from a Houghton group on at least three rays to a group of polynomial sofic profile kills the finitary alternating subgroup. We locate the error in Cornulier's extension estimate and prove a corrected bound that depends on scale. We also give unitary lower bounds, unitary models smaller than our permutation models, a polynomial Dehn-function upper bound, and a direct proof that every finite piece of a Baumslag-Solitar group has at most linear profile.

This repository contains the preprint, its source, finite certificate checks and a Lean 4 core.
The Lean core proves the printed profile bounds of Theorem 1.1 (with upper constant 7000), Theorems 3.1–3.3
and other printed results, the profile-only part of Corollary 1.2
and, conditionally on the explicit premise `PermSectorBound`, the H₃ finitary-three-cycle-kernel conclusion of Corollary 1.3, using only Lean's three standard axioms and passing the leanchecker and nanoda
kernel checkers. [lean/README.md](lean/README.md) and Appendix C give the exact scope, what is not
formalized and the build commands; this is a formal core, not verification of the whole paper or peer review.

## License and citation

The manuscript and repository content are available under **CC BY 4.0**.
The software and machine-readable certificates are additionally available under
the **MIT License**, at your option; see [RIGHTS.md](RIGHTS.md) for the scope.

Please cite Seth Douglas and Nidhal Mghirbi, *Houghton's group H_3 has
superpolynomial sofic profile* (2026), version 1.3.0,
[doi:10.5281/zenodo.23027624](https://doi.org/10.5281/zenodo.23027624) (all versions).
[CITATION.cff](CITATION.cff) provides
machine-readable citation metadata. Tagged releases archive the corresponding
manuscript and verification artifacts together.

The v1.2.0 archive is [doi:10.5281/zenodo.23875978](https://doi.org/10.5281/zenodo.23875978).
The DOI above is the all-versions DOI, which identifies the evolving work. The v1.1.2 archive is
[doi:10.5281/zenodo.23070869](https://doi.org/10.5281/zenodo.23070869), the v1.1.1 archive is
[doi:10.5281/zenodo.23065750](https://doi.org/10.5281/zenodo.23065750), the v1.1.0 archive is
[doi:10.5281/zenodo.23048875](https://doi.org/10.5281/zenodo.23048875), and the v1.0.0 archive is
[doi:10.5281/zenodo.23027625](https://doi.org/10.5281/zenodo.23027625).

## Reproduce

Requires Python 3.10+, a TeX distribution with the packages listed in paper.tex
and Lean 4.30.0 for the existing certificate checks. No third-party Python package is needed.

With Lean 4.30.0 on PATH, from the repository root:

    python build.py
    python verification/check.py

The second command checks the distributed certificates and scalar recurrences,
regenerates their Lean transcription, and runs their kernel checks. For the separate
Lean 4.35.0 core, see [lean/README.md](lean/README.md).

Generated TeX build files stay in build/; paper.pdf is the canonical output.
The bibliography is embedded in paper.tex. The version 1.3.0 version DOI will be
recorded after minting; the DOI above remains the all-versions DOI.

## Companions

[Causal quantum-channel simulation: memory beyond entropy](https://github.com/Apsiape/causal-quantum-memory)
uses these group results for operational memory lower bounds; its all-versions DOI is
[doi:10.5281/zenodo.23027626](https://doi.org/10.5281/zenodo.23027626).
[Amenable groups with nearly exponential sofic profile, and quantum channels that need nearly linear memory](https://github.com/Apsiape/configuration-lamps)
applies the counting criterion close to its ceiling; its all-versions DOI is
[doi:10.5281/zenodo.23050302](https://doi.org/10.5281/zenodo.23050302).
Each manuscript can be built independently from its own repository.
