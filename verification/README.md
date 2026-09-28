# Verification scope

Run from the repository root:

    python verification/check.py

Lean is pinned to 4.30.0. Python uses only its standard library. All checks are
finite and have explicit per-command timeouts. The selected certificate kernel
check is allowed ten minutes; runtime depends on the machine.

## What is checked

- **scalarcheck.py:** exact rational margin in the constant-750 sector bound,
  including the integer threshold for its logarithm estimate. The entropy
  inequality and the analytic lower bound on ln(2) remain proof inputs.
- **collectioncheck.py:** finite ray-action checks for the buffered collection
  identities, local Coxeter rewrites through 24 generators, and recursive
  insertion on 120 deterministic test words. These are transcription regressions;
  the arbitrary-word argument and its area bound are the manuscript's proof.
- **Independent Python certificate verifier:** all 40 distributed certificates,
  including recursion instances through n = 5. Targets are recomputed from the
  definitions; the verifier imports no code from the certificate builder.
- **Certificate provenance for reweighting:** the five relator-image cell
  histograms are recomputed from the archive and compared with the substitution
  matrix. Exact rational arithmetic checks its weight inequality.
- **Lean FreeReduction.lean:** free reduction preserves every multiplicative
  interpretation satisfying associativity, identity and inverse-letter
  cancellation. Relator-cell certificates accepted by the checker evaluate to
  the identity whenever the five defining relators do. These are universal
  soundness statements, not sampled checks.
- **Lean Certificates.lean:** the 15 core finite certificates with at most 21
  cells are transcribed
  mechanically from the archive, with freely reduced conjugators. Each
  reduction step is checked by the kernel using decidable equality. The target
  transcription is supplied by the independent Python definition of the words;
  the correspondence of those definitions with manuscript notation is still
  a human-readable boundary. The exported finite lists also have checked
  lengths. The longer core certificates (including the large relator images)
  and recursion examples remain Python-only. The generator's explicit size
  cutoff makes this coverage boundary reproducible.
- **Lean Arithmetic.lean:** integer-scaled matrix inequalities, rational
  constants after clearing denominators, and an all-depth induction for the
  stated recurrence hypotheses, plus the exact insertion-cost recurrence and
  integer logarithm threshold used in the constant-750 bound.
  The geometric derivation of those recurrences
  is not a premise-free Lean theorem.

The Lean files use neither proof placeholders nor native evaluation as a proof
oracle. The abstract soundness proofs use propositional extensionality; concrete
checks and induction may also use Lean's standard quotient and choice principles. They introduce
no mathematical axioms specific to these papers.

## Not formally verified

The presentation theorem for H_3, the all-n conversion from word certificates to
the complete area and Dehn-function theorems, the entropy/stability/sector arguments, the corner
and unitary constructions, the sofic-profile theorem and the extension correction
are not fully formalized in Lean. The certificate checker verifies triviality
under the relator assumptions; a van Kampen-area semantics is not defined in Lean.

Neither successful numerical tests nor a successful Lean arithmetic file should
be cited as formal certification of the whole manuscript.

## Regeneration

The archived certificate file has SHA-256:

    e87870172a0c66d4c0b15db16ae6a7d93f3b9528e3a34144a4d54632dbecf352

From verification/certificates/, run:

    python build_all.py
    python verify.py

Rebuilding may change the gzip container timestamp without changing its decoded
certificate data. From the repository root, regenerate the Lean transcription:

    python verification/generate_lean.py

See certificates/README.md for the cells, definitions and larger optional finite
recursion instances. Those larger runs are not part of the default release check.
