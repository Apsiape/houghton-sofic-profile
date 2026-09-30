# Houghton's group H_3 has superpolynomial sofic profile

Seth Douglas and Nidhal Mghirbi — September 2026.

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23027624.svg)](https://doi.org/10.5281/zenodo.23027624)

[Read the manuscript](paper.pdf) · [TeX source](paper.tex) ·
[Verification scope](verification/README.md)

Houghton's finitely presented elementary amenable group H_3 has a finite chunk
with superpolynomial sofic profile. The paper proves quantitative lower bounds,
constructs permutation and unitary models, and gives a scale-dependent correction
to the extension estimate discussed in the text. The upper sofic bound applies
to every fixed finite chunk of H_3. Buffered collection also yields the full
Dehn-function upper bound 400 n^4(1 + A*(4n+2)) = O(n^(log2(107)+4)); this does not change the sharper
far-commutator estimate used for the profile exponents.
The explicit area bound is 135 M^(log2(107)), giving sofic lower exponent
1/(log2(107)+1) and squared-defect unitary exponent 1/(2log2(107)+1).
Its auxiliary-relator certificate archive is independently checked over the
original five relators. A separate unweighted certificate archive checks the
full five-image endomorphism and the M^11 bound.
Every homomorphism from H_m (m >= 3) to a group with polynomial sofic profile
kills the finitary alternating subgroup. Its image has commutator subgroup of
order at most two and an abelian subgroup of index at most 2^floor((m-1)/2). Combined
with Cornulier's independent theorem, this applies to Bir_K(X) for absolutely
irreducible finite-dimensional varieties over any field, and excludes embeddings.
Finite-dimensional unitary representations also kill that alternating subgroup;
their irreducible dimensions are exactly 1 and 2^floor((m-1)/2). A finite Pauli
image attains the latter and makes the abelian-subgroup index bound sharp.
Every nontrivial normal subgroup of H_m contains the finitary alternating subgroup.
Thus a homomorphic image is either a faithful copy of H_m or a residually finite,
virtually abelian quotient. Noninjectivity, polynomial chunk profile, bounded
chunk profile, residual finiteness and killing that alternating subgroup are
equivalent conditions on the homomorphism and its image.
The phase-spreading construction also has a sharp M^(-3) squared-defect law
within its fixed regions; no matching lower bound for arbitrary models is claimed.
The lower bound applies to any group in which finitely many relations make many
displaced copies of S_3 commute cheaply (a general counting criterion); work in
preparation applies it to groups with nearly exponential sofic profile. The paper
also proves directly Cornulier's assertion that every chunk of every
Baumslag-Solitar group has at most linear profile, which his argument derived from
the extension theorem, with a lower bound of 2r for some chunk when the group is
not residually finite.

This repository contains the preprint, its source, and scoped verification
artifacts. The manuscript is the authority for exact statements and hypotheses;
the automated checks do not constitute full formal verification or peer review.

## License and citation

The manuscript and repository content are available under **CC BY 4.0**.
The software and machine-readable certificates are additionally available under
the **MIT License**, at your option; see [RIGHTS.md](RIGHTS.md) for the scope.

Please cite Seth Douglas and Nidhal Mghirbi, *Houghton's group H_3 has
superpolynomial sofic profile* (2026), version 1.1.2,
[doi:10.5281/zenodo.23027624](https://doi.org/10.5281/zenodo.23027624) (all versions).
[CITATION.cff](CITATION.cff) provides
machine-readable citation metadata. Tagged releases archive the corresponding
manuscript and verification artifacts together.

The DOI above is the all-versions DOI, which identifies the evolving work. The v1.1.2 archive is
[doi:10.5281/zenodo.23070869](https://doi.org/10.5281/zenodo.23070869), the v1.1.1 archive is
[doi:10.5281/zenodo.23065750](https://doi.org/10.5281/zenodo.23065750), the v1.1.0 archive is
[doi:10.5281/zenodo.23048875](https://doi.org/10.5281/zenodo.23048875), and the v1.0.0 archive is
[doi:10.5281/zenodo.23027625](https://doi.org/10.5281/zenodo.23027625).

## Reproduce

Requires Python 3.10+, a TeX distribution with the packages listed in paper.tex,
and (for formal checks) Lean 4.30.0. No third-party Python package is needed.

    python build.py
    python verification/check.py

The second command checks the distributed certificates, regenerates their Lean
transcription, and runs the Lean kernel checks. It does not prove the entire paper.
Generated TeX build files stay in build/; paper.pdf is the canonical output.
The bibliography is embedded in paper.tex.

## Companions

[Causal quantum-channel simulation: memory beyond entropy](https://github.com/Apsiape/causal-quantum-memory)
uses these group results for operational memory lower bounds; its all-versions DOI is
[doi:10.5281/zenodo.23027626](https://doi.org/10.5281/zenodo.23027626).
[Amenable groups with nearly exponential sofic profile, and quantum channels that need nearly linear memory](https://github.com/Apsiape/configuration-lamps)
applies the counting criterion close to its ceiling; its all-versions DOI is
[doi:10.5281/zenodo.23050302](https://doi.org/10.5281/zenodo.23050302).
Each manuscript can be built independently from its own repository.
