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
  It also verifies the integer inequality giving the sofic prefactor 1/1280.
- **fluxcheck.py:** exact region-cardinality regressions at five sizes and finite
  evaluations of the restricted flux bounds. The universal phase inequality and
  asymptotic limit are proved in the manuscript, not by sampling.
- **othergroupscheck.py:** the margin proposition (exact rational brackets at eight
  margins, a grid down to 2^-40, and the constants of the analytic chain); the
  lattice-area lower bound on the Dehn function (commutator structure for m up to
  25 and signed areas); the Baumslag-Solitar tile construction (exact conjugacy of
  the cut cycles, defect counts, and all reduced words with at most three stable
  letters and bounded a-exponents at eight parameter sets, with auxiliary words checked reduced and
  nontrivial in SL_2(Z)); the vanishing of [t a t^-1, a] in all homomorphisms of
  BS(2,3) to S_5 and S_6. These are finite regressions; the general statements are
  proved in the manuscript.
- **cornercheck.py:** the corner models of the upper bounds, which the quadratic
  lower bound on far-commutator area also uses. For M = 5,...,16 it builds the colour
  permutations from the manuscript's recursion and follows every relator from every
  clock: r_1, r_2, r_3, r_5 act trivially, r_4 acts as R_M at the corner clock only,
  gamma is a three-cycle everywhere, and at each of the (M-4)(M-3)/2 clocks with
  i + j >= M + 3 the far commutator C_(2M-1) acts as a three-cycle. A negative
  control removes tau from the recursion and must break r_4. The all-M statement is
  proved in the manuscript.
- **collectioncheck.py:** finite ray-action checks for the buffered collection
  identities, local Coxeter rewrites through 24 generators, and recursive
  insertion on 120 deterministic test words. It charges original-relator cells
  (one for a square, four for a braid, the certified far-area bound for a
  commutation), and checks five complete buffered relator traces with inverse
  letters against the explicit 400 n^4 F_n ledger. These are transcription regressions;
  the arbitrary-word argument and its area bound are the manuscript's proof.
- **representationcheck.py:** exact ray commutators and Clifford monomial matrices
  for m = 3,...,11, including anticommutation, joint-sign patterns and the rank of
  the parity commutator form. It uses only integer phases, not floating point.
  These finite regressions do not prove the all-m quotient presentation,
  irreducible-dimension classification or sharp index theorem.
  It also checks the right-action commutator and conjugation identities used in
  the normal-subgroup proof, with an inverse-cycle negative control. These
  finite tests do not prove simplicity of the infinite alternating group.
- **Independent Python certificate verifier:** all 40 distributed certificates,
  including recursion instances through n = 5. Targets are recomputed from the
  definitions; the verifier imports no code from the certificate builder.
- **Certificate provenance for reweighting:** the five relator-image cell
  histograms are recomputed from the archive and compared with the substitution
  matrix. Exact rational arithmetic checks its weight inequality.
- **verify107.py:** independently recomputes all 25 targets in the auxiliary
  certificate archive (7,366 original-relator cells, including recursion through
  k = 8), checks both auxiliary and expanded lists, reconstructs the 107 matrix,
  and checks the integer weights, rule costs and characteristic polynomial.
  It imports no builder code. The builder keeps the derived r6 atomic during
  substitution, then expands its nine original cells at final export.
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
  integer logarithm threshold used in the constant-750 bound, and the conditional
  aggregation 5 + 3 + 360 <= 400 for the Dehn-function ledger.
  The geometric derivation of those recurrences
  is not a premise-free Lean theorem.
- **Lean Auxiliary107.lean:** the integer weight bounds and conditional
  all-depth recurrence. **Certificates107.lean** kernel-checks the eight
  nonrecursive certificates of at most 21 original cells from the auxiliary archive.
  The longer image/rule lists are checked in independent Python, not Lean.
  Arithmetic.lean also verifies the independent multiplier-130 recurrence.

The Lean files use neither proof placeholders nor native evaluation as a proof
oracle. The abstract soundness proofs use propositional extensionality; concrete
checks and induction may also use Lean's standard quotient and choice principles. They introduce
no mathematical axioms specific to these papers.

## Not formally verified

The presentation theorem for H_3, the all-n conversion from word certificates to
the complete area and Dehn-function theorems, the entropy/stability/sector arguments, the corner
and unitary constructions, the sofic-profile theorem, the extension correction, the finite-certificate criterion and the
Baumslag-Solitar theorem are not formalized in Lean. The certificate checker verifies triviality
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

The deterministic auxiliary archive `certificates107.json.gz` has SHA-256:

    f63563a1f8e1f8cde46620ccefd1085840c35198b10e6f4bc568f39354693149

Regenerate from the repository root with:

    python verification/certificates/build107.py
    python verification/certificates/verify107.py
    python verification/generate_lean.py --aux107
