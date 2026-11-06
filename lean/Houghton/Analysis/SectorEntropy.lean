import FiniteLean.QIT.Entropy.Scalar
import Houghton.Analysis.DimensionPerm
import Houghton.Analysis.Sector
import Mathlib.Analysis.Real.Sqrt

/-!
# The classical (Shannon) part of the phase-robust sector bound

The "Sectors" paragraph of the proof of Theorem `thm:phase-robust`: if a probability vector `p` on
`(ℤ/3)^N` has much mass on nontrivial labels in each coordinate and is nearly invariant under each
coordinate flip `ω ↔ ω²` (Bhattacharyya coefficient near `1`), then its Shannon entropy is large.

We use the chain rule `H(Z) = ∑ᵢ H(Zᵢ | Z_{<i})` (as an exact identity, by induction on `N`)
instead of `H(Z) ≥ ∑ᵢ H(Zᵢ | Z_{-i})`; the Bhattacharyya coefficient of a marginal is at least that
of the joint law (Cauchy–Schwarz), so the paper's estimate goes through.  We also replace the
paper's inequality `1 - h₂(t) ≤ (1 - 2√(t(1-t)))/ln 2` by the weaker
`1 - h₂(t) ≤ 2(1 - 2√(t(1-t)))/ln 2`, which follows from `log x ≤ x - 1` (there is ample room).

`PermSectorDistribution` is the remaining (quantum) input: the existence of the sector distribution
with an entropy upper bound.  It implies `PermSectorBound`, hence `prop:dimension-perm`.
-/

universe u

namespace Houghton

open Finset Equiv

/-- **Remaining analytic input** (the quantum part of Theorem `thm:phase-robust`, permutation case):
the joint sector distribution `p` of the embedded shifts `Cᵢ` exists, with
`H(p) ≤ log₂ D + ∑ᵢ G(âᵢ²)`, `Pr(Zᵢ ≠ 1) ≥ (Δᵢ² - âᵢ²)/3` and Bhattacharyya coefficient
`∑_z √(p(z) p(z⁽ⁱ⁾)) ≥ 1 - b̂ᵢ²/2`, evaluated at `Δᵢ² ≥ 1/4`, `âᵢ², b̂ᵢ² ≤ 1/15000`. -/
def PermSectorDistribution : Prop :=
  ∀ (Ω : Type u) [Fintype Ω] [DecidableEq Ω] (N : ℕ) (c x : Fin N → Perm Ω),
    (∀ i, c i ^ 3 = 1) → (∀ i, x i ^ 2 = 1) → (∀ i, x i * c i * x i = (c i)⁻¹) →
    (∀ i, (1 : ℝ) / 8 ≤ dH (c i) 1) →
    (∀ i, ∑ j ∈ univ.filter (· ≠ i), dH (c i * c j) (c j * c i) ≤ 1 / 40000) →
    (∀ i, ∑ j ∈ univ.filter (· ≠ i), dH (x i * c j) (c j * x i) ≤ 1 / 40000) →
    ∃ p : (Fin N → Fin 3) → ℝ, (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1 ∧
      (∑ z, ent (p z)) / Real.log 2 ≤ Real.logb 2 (Fintype.card Ω) + N / 1000 ∧
      (∀ i, 83 / 1000 ≤ ∑ z ∈ univ.filter (fun z => z i ≠ 0), p z) ∧
      (∀ i, 1 - 1 / 30000 ≤ ∑ z, Real.sqrt (p z * p (flipAt i z)))

theorem permSectorBound_of_distribution (h : PermSectorDistribution.{u}) :
    PermSectorBound.{u} := by
  intro Ω _ _ N c x h1 h2 h3 h4 h5 h6
  obtain ⟨p, hp0, hp1, hH, hs, hb⟩ := h Ω N c x h1 h2 h3 h4 h5 h6
  have main := Ent_ge N p hp0
  have hEnt : Ent p = ∑ z, ent (p z) := by simp [Ent, hp1, ent_one]
  have hsi : ∀ i, 83 / 1000 ≤ sAt i p := by
    intro i
    have := hs i
    simp only [sum_filter, ne_eq, ite_not] at this
    exact this
  have hdi : ∀ i, dAt i p ≤ 1 / 30000 := by
    intro i
    have e : ∀ z, (if z i = 0 then 0 else p z - Real.sqrt (p z * p (flipAt i z))) =
        p z - Real.sqrt (p z * p (flipAt i z)) := by
      intro z
      split_ifs with hz
      · have hf : flipAt i z = z := by
          simp only [flipAt, hz]
          rw [show fl 0 = 0 from rfl, ← hz, Function.update_eq_self]
        rw [hf, Real.sqrt_mul_self (hp0 z), sub_self]
      · rfl
    simp only [dAt, e, sum_sub_distrib, hp1]
    linarith [hb i]
  have hl2 := log_two_gt_half
  have hl2pos : 0 < Real.log 2 := by linarith
  have hsum : (N : ℝ) * (Real.log 2 * (83 / 1000) - 2 * (1 / 30000)) ≤ ∑ z, ent (p z) := by
    rw [← hEnt]
    refine le_trans ?_ main
    have : ∀ i ∈ (univ : Finset (Fin N)),
        Real.log 2 * (83 / 1000) - 2 * (1 / 30000) ≤ Real.log 2 * sAt i p - 2 * dAt i p := by
      intro i _
      have := hsi i
      have := hdi i
      nlinarith
    calc (N : ℝ) * (Real.log 2 * (83 / 1000) - 2 * (1 / 30000))
        = ∑ _i : Fin N, (Real.log 2 * (83 / 1000) - 2 * (1 / 30000)) := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum this
  rw [div_le_iff₀ hl2pos] at hH
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have key : Real.log 2 * ((N : ℝ) / 16) ≤ Real.log 2 * Real.logb 2 (Fintype.card Ω) := by
    nlinarith [mul_nonneg hN0 (le_of_lt (sub_pos.mpr hl2))]
  exact le_of_mul_le_mul_left key hl2pos

/-- **Proposition `prop:dimension-perm`**, assuming only the sector distribution
`PermSectorDistribution` (the quantum part of `thm:phase-robust`). -/
theorem dimension_perm_of_sectorDistribution (hS : PermSectorDistribution.{u}) {Ω : Type u}
    [Fintype Ω] [DecidableEq Ω] (φ : F →* Equiv.Perm Ω) (δ : ℝ)
    (hrel : ∀ i, dH (φ (rel i)) 1 ≤ δ) (hγ : 1/2 ≤ dH (φ γ) 1) (N A : ℕ) (hN : 1 ≤ N)
    (hA : AstarLE (3 * N) A) (hδ : (10:ℝ)^8 * N * max 1 A * δ ≤ 1) :
    (N : ℝ) / 16 ≤ Real.logb 2 (Fintype.card Ω) :=
  dimension_perm_of_sectorBound (permSectorBound_of_distribution hS) φ δ hrel hγ N A hN hA hδ

end Houghton
