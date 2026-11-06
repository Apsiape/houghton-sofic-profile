import FiniteLean.QIT.Entropy.SSAFinal
import Houghton.Analysis.SSAUnconditional
import FiniteLean.QIT.RelEntConvex
import FiniteLean.QIT.Integral

/-!
# Unconditional Theorem 1.1 and Corollary 1.2

Joint convexity `QIT.relEnt_jointlyConvex_of` (given `QIT.IntegralRep`), the integral
representation `QIT.integralRep`, and `QIT.relEnt_unitary_conj` discharge the two interface
`Prop`s of `SSAInterface` (`qrelEnt`/`qmlog` are definitionally `QIT.relEnt`/`QIT.mlog`).
-/

namespace Houghton

/-- **Theorem 1.1** (Douglas–Mghirbi), unconditional. -/
theorem theorem_1_1_final (r : ℝ) (hr : 2 ≤ r) :
    ∃ m : ℕ, profile E_H r = m ∧
      (2:ℝ) ^ (r ^ (1 / (Real.logb 2 107 + 1)) / 1280 - 1 / 16) ≤ m ∧
      (2:ℝ) ^ (r ^ ((1:ℝ) / 12) / 270 - 1 / 16) ≤ m ∧
      (m : ℝ) ≤ 2 ^ (7000 * √r * Real.logb 2 r) :=
  theorem_1_1_SSA qit_commutingPinchingSSA r hr

/-- **Corollary 1.2** (Douglas–Mghirbi), unconditional. -/
theorem corollary_1_2_final :
    ∀ k C : ℝ, ∃ r : ℝ, 2 ≤ r ∧ ∃ m : ℕ, profile E_H r = m ∧ C * r ^ k < m :=
  corollary_1_2_SSA qit_commutingPinchingSSA

/-- **Proposition `prop:dimension-perm`** with exactly the target signature, unconditional. -/
theorem dimension_perm {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (φ : F →* Equiv.Perm Ω) (δ : ℝ) (hrel : ∀ i, dH (φ (rel i)) 1 ≤ δ)
    (hγ : 1/2 ≤ dH (φ γ) 1) (N A : ℕ) (hN : 1 ≤ N) (hA : AstarLE (3 * N) A)
    (hδ : (10:ℝ)^8 * N * max 1 A * δ ≤ 1) :
    (N : ℝ) / 16 ≤ Real.logb 2 (Fintype.card Ω) :=
  dimension_perm_of_SSA qit_commutingPinchingSSA φ δ hrel hγ N A hN hA hδ

end Houghton
