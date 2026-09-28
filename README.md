# Houghton's group H_3 has superpolynomial sofic profile

Seth Douglas and Nidhal Mghirbi — September 2026.

[Read the manuscript](paper.pdf) · [TeX source](paper.tex) ·
[Verification scope](verification/README.md)

Houghton's finitely presented elementary amenable group H_3 has a finite chunk
with superpolynomial sofic profile. The paper proves quantitative lower bounds,
constructs permutation and unitary models, and gives a scale-dependent correction
to the extension estimate discussed in the text. The upper sofic bound applies
to every fixed finite chunk of H_3. Buffered collection also yields the full
Dehn-function upper bound O(n^(log2(130)+4)); this does not change the sharper
far-commutator estimate used for the profile exponents.
Combined with Cornulier's independent polynomial-profile theorem for birational
groups, the lower bound also excludes embeddings of H_3 (and H_m, m >= 3) into
Bir_K(X) for absolutely irreducible finite-dimensional varieties over any field.
This corollary is stated without a separate priority claim.

This is a **private release candidate**, not an announced publication.
The manuscript is the authority for exact statements and hypotheses. Licenses
and the joint public-release decision remain pending; see [RIGHTS.md](RIGHTS.md).

## Reproduce

Requires Python 3.10+, a TeX distribution with the packages listed in paper.tex,
and (for formal checks) Lean 4.30.0. No third-party Python package is needed.

    python build.py
    python verification/check.py

The second command checks the distributed certificates, regenerates their Lean
transcription, and runs the Lean kernel checks. It does not prove the entire paper.
Generated TeX build files stay in build/; paper.pdf is the canonical output.
The bibliography is embedded in paper.tex.

## Companion

[Causal quantum-channel simulation: memory beyond entropy](https://github.com/Apsiape/causal-quantum-memory)
uses these group results for operational memory lower bounds. Each manuscript
can be built without the private research workspace. Companion links require
access while the repositories remain private.
