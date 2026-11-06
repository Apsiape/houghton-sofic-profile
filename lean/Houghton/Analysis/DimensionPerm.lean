import Houghton.Analysis.S3Pairs
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Proposition `prop:dimension-perm`

`PermSectorBound` is the analytic input: the permutation-matrix case of the "in particular" clause of
Theorem `thm:phase-robust` (together with its bounds `â_i² ≤ (4/3)∑_{j>i} κ(c_i,c_j)²`,
`b̂_i² ≤ (4/3)∑_{j≠i} κ(x_i,c_j)²`).  For permutation matrices `‖P_g - P_h‖₂² = 2 dH g h`, so the
hypotheses below give `Δ_i ≥ 1/2 ≥ 49/100` and `â_i², b̂_i² ≤ (8/3)/40000 < 10⁻⁴`.
-/

universe u

namespace Houghton

open Finset Equiv

/-- Permutation form of the phase-robust sector bound (Theorem `thm:phase-robust`). -/
def PermSectorBound : Prop :=
  ∀ (Ω : Type u) [Fintype Ω] [DecidableEq Ω] (N : ℕ) (c x : Fin N → Perm Ω),
    (∀ i, c i ^ 3 = 1) → (∀ i, x i ^ 2 = 1) → (∀ i, x i * c i * x i = (c i)⁻¹) →
    (∀ i, (1 : ℝ) / 8 ≤ dH (c i) 1) →
    (∀ i, ∑ j ∈ univ.filter (· ≠ i), dH (c i * c j) (c j * c i) ≤ 1 / 40000) →
    (∀ i, ∑ j ∈ univ.filter (· ≠ i), dH (x i * c j) (c j * x i) ≤ 1 / 40000) →
    (N : ℝ) / 16 ≤ Real.logb 2 (Fintype.card Ω)

/-- **Proposition `prop:dimension-perm`**, assuming the sector bound `PermSectorBound`. -/
theorem dimension_perm_of_sectorBound (hS : PermSectorBound.{u}) {Ω : Type u} [Fintype Ω]
    [DecidableEq Ω] (φ : F →* Equiv.Perm Ω) (δ : ℝ) (hrel : ∀ i, dH (φ (rel i)) 1 ≤ δ)
    (hγ : 1/2 ≤ dH (φ γ) 1) (N A : ℕ) (hN : 1 ≤ N) (hA : AstarLE (3 * N) A)
    (hδ : (10:ℝ)^8 * N * max 1 A * δ ≤ 1) :
    (N : ℝ) / 16 ≤ Real.logb 2 (Fintype.card Ω) := by
  have hδ' : (10 : ℝ) ^ 8 * N * max 1 (A : ℝ) * δ ≤ 1 := by
    simpa [Nat.cast_max] using hδ
  obtain ⟨c, x, h1, h2, h3, h4, h5, h6⟩ := exists_local_S3 φ δ hrel hγ N A hN hA hδ'
  exact hS Ω N c x h1 h2 h3 h4 h5 h6

end Houghton
