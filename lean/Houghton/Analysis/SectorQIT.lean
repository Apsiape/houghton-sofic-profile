import FiniteLean.QIT.Entropy.Basic
import Houghton.Analysis.SectorFourier
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Reduction of the sector entropy bound to strong subadditivity

Fourier picture of the proof of Theorem `thm:phase-robust`: on `ℂ^{(ℤ/3)^N × Ω}` the state is
`ρ̂ = Y Y* / (9^N D)` with `Y_{(χ,α),ω} = M_χ(α, ω)` (unitarily equivalent to the paper's
`ρ = VV*/D`, the Fourier transform turning the commuting shifts `C_i` into the diagonal label
projections), the twirl by `C_i` is the dephasing `pinch (labelProj i)`, and the full twirl is the
joint dephasing `pinchAll labelProj`, whose block weights are the sector distribution `pSec`.

`QIT_CommutingPinchingSSA` is the textbook input (strong subadditivity in the form of commuting
conditional expectations).  The three elementary spectral facts `SubStateEntropy`,
`SubTwirlEntropy`, `SubSectorEntropy` are stated here as `Prop`s and proved in
`SectorSpectral` (A, C) and `SectorTwirl`/`SectorGen` (B); the end result is
`Houghton.dimension_perm_of_SSA` in `SectorGen`.
-/

universe u

namespace Houghton

open Finset Equiv Matrix ComplexConjugate

section Concrete

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω] {N : ℕ}

/-- `Y_{(χ,α),ω} = M_χ(α, ω)`. -/
noncomputable def Ymat (c : Fin N → Perm Ω) : Matrix ((Fin N → Fin 3) × Ω) Ω ℂ :=
  fun p ω => Msec c p.1 p.2 ω

/-- The state `ρ̂ = Y Y* / (9^N D)`. -/
noncomputable def rhoSec (c : Fin N → Perm Ω) :
    Matrix ((Fin N → Fin 3) × Ω) ((Fin N → Fin 3) × Ω) ℂ :=
  (((9 : ℝ) ^ N * Fintype.card Ω)⁻¹ : ℝ) • (Ymat c * (Ymat c)ᴴ)

/-- Projection onto the label `a` in coordinate `i`. -/
noncomputable def labelProj (i : Fin N) (a : Fin 3) :
    Matrix ((Fin N → Fin 3) × Ω) ((Fin N → Fin 3) × Ω) ℂ :=
  Matrix.diagonal fun p => if p.1 i = a then 1 else 0

lemma labelProj_family (i : Fin N) : IsProjFamily (labelProj (Ω := Ω) i) where
  herm a := by
    rw [labelProj, diagonal_conjTranspose]
    congr 1
    funext p
    by_cases h : p.1 i = a <;> simp [h]
  orth a b := by
    rw [labelProj, labelProj, diagonal_mul_diagonal]
    split_ifs with hab
    · subst hab
      congr 1
      funext p
      split_ifs <;> simp
    · rw [← diagonal_zero]
      congr 1
      funext p
      by_cases h1 : p.1 i = a
      · simp [h1, hab]
      · simp [h1]
  sum_one := by
    ext p q
    rw [Matrix.sum_apply]
    simp only [labelProj, diagonal_apply, one_apply]
    by_cases hpq : p = q
    · subst hpq
      simp [sum_ite_eq]
    · simp [hpq]

lemma labelProj_comm (i j : Fin N) (a b : Fin 3) :
    labelProj (Ω := Ω) i a * labelProj j b = labelProj j b * labelProj i a := by
  simp only [labelProj, diagonal_mul_diagonal, mul_comm]

lemma rhoSec_density (c : Fin N → Perm Ω) (hD : 0 < Fintype.card Ω) : IsDensity (rhoSec c) := by
  have hK : (0 : ℝ) < 9 ^ N * Fintype.card Ω := by positivity
  refine ⟨?_, ?_, ?_⟩
  · -- Hermitian
    unfold rhoSec
    rw [IsHermitian, conjTranspose_smul, conjTranspose_mul, conjTranspose_conjTranspose]
    congr 1
  · intro v
    have e : star v ⬝ᵥ (rhoSec c *ᵥ v) =
        (((9 : ℝ) ^ N * Fintype.card Ω)⁻¹ : ℝ) • (star ((Ymat c)ᴴ *ᵥ v) ⬝ᵥ ((Ymat c)ᴴ *ᵥ v)) := by
      rw [rhoSec, smul_mulVec, dotProduct_smul, ← mulVec_mulVec, dotProduct_mulVec,
        star_mulVec, conjTranspose_conjTranspose]
    rw [e, Complex.real_smul, Complex.re_ofReal_mul]
    refine mul_nonneg (inv_nonneg.mpr hK.le) ?_
    simp only [dotProduct, Complex.re_sum, Pi.star_apply]
    refine sum_nonneg fun ω _ => ?_
    have : (star (((Ymat c)ᴴ *ᵥ v) ω) * ((Ymat c)ᴴ *ᵥ v) ω).re =
        Complex.normSq (((Ymat c)ᴴ *ᵥ v) ω) := by
      rw [show star (((Ymat c)ᴴ *ᵥ v) ω) = conj (((Ymat c)ᴴ *ᵥ v) ω) from rfl,
        ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    rw [this]
    exact Complex.normSq_nonneg _
  · -- trace
    rw [rhoSec, trace_smul]
    have htr : (Ymat c * (Ymat c)ᴴ).trace = ((9 : ℝ) ^ N * Fintype.card Ω : ℝ) := by
      rw [← sum_nsq_Msec c, Complex.ofReal_sum]
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, Ymat]
      rw [Fintype.sum_prod_type]
      refine sum_congr rfl fun χ _ => ?_
      simp only [nsq, Complex.ofReal_sum]
      refine sum_congr rfl fun α _ => sum_congr rfl fun ω _ => ?_
      rw [show star (Msec c χ α ω) = conj (Msec c χ α ω) from rfl, Complex.mul_conj]
    rw [htr, Complex.real_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hK.ne', Complex.ofReal_one]

/-- (A) `S(ρ̂) ≥ log D`: `ρ̂ = YY*/(9^N D)` with `Y*Y = 9^N I`, so its eigenvalues are
`0` and `1/D`. -/
def SubStateEntropy : Prop :=
  ∀ (Ω : Type u) [Fintype Ω] [DecidableEq Ω] (N : ℕ) (c : Fin N → Perm Ω),
    0 < Fintype.card Ω → Real.log (Fintype.card Ω) ≤ vN (rhoSec c)

/-- (B) Single-twirl bound: one dephasing moves weight `w ≤ 1/7500` out of `ran ρ̂` into a block of
rank `≤ 2D`, so `S ≤ log D + h(w) + w log 2 ≤ log D + 1/200` (the paper's `G(â²)`). -/
def SubTwirlEntropy : Prop :=
  ∀ (Ω : Type u) [Fintype Ω] [DecidableEq Ω] (N : ℕ) (c x : Fin N → Perm Ω),
    (∀ i, c i ^ 3 = 1) → (∀ i, x i ^ 2 = 1) → (∀ i, x i * c i * x i = (c i)⁻¹) →
    (∀ i, (1 : ℝ) / 8 ≤ dH (c i) 1) →
    (∀ i, ∑ j ∈ univ.filter (· ≠ i), dH (c i * c j) (c j * c i) ≤ 1 / 40000) →
    (∀ i, ∑ j ∈ univ.filter (· ≠ i), dH (x i * c j) (c j * x i) ≤ 1 / 40000) →
    ∀ i, vN (pinch (labelProj i) (rhoSec c)) ≤ Real.log (Fintype.card Ω) + 1 / 200

/-- (C) The fully dephased state is block diagonal with block weights `pSec`, so its entropy is at
least the Shannon entropy of `pSec`. -/
def SubSectorEntropy : Prop :=
  ∀ (Ω : Type u) [Fintype Ω] [DecidableEq Ω] (N : ℕ) (c : Fin N → Perm Ω),
    0 < Fintype.card Ω →
      ∑ z, ent (pSec c z) ≤ vN (pinchAll (fun i => labelProj i) (rhoSec c))

end Concrete

theorem permSectorEntropy_of_QIT (hQ : QIT_CommutingPinchingSSA.{u})
    (hA : SubStateEntropy.{u}) (hB : SubTwirlEntropy.{u}) (hC : SubSectorEntropy.{u}) :
    PermSectorEntropy.{u} := by
  intro Ω _ _ N c x h1 h2 h3 h4 h5 h6
  have hl2 := log_two_gt_half
  have hl2pos : 0 < Real.log 2 := by linarith
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have h0 : ∑ z, ent (pSec c z) = 0 := by
      rw [Fintype.sum_unique]
      rcases Nat.eq_zero_or_pos (Fintype.card Ω) with hD | hD
      · simp [pSec, hD, ent]
      · have := sum_pSec c hD
        rw [Fintype.sum_unique] at this
        rw [this, ent_one]
    rw [h0, zero_div, Nat.cast_zero, zero_div, add_zero]
    rcases Nat.eq_zero_or_pos (Fintype.card Ω) with hD | hD
    · simp [hD]
    · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hD)
  · have hD0 : Fintype.card Ω ≠ 0 := by
      intro h0
      have := h4 ⟨0, hN⟩
      rw [dH_eq, h0, Nat.cast_zero, div_zero] at this
      norm_num at this
    have hD := Nat.pos_of_ne_zero hD0
    set L := Real.log (Fintype.card Ω) with hL
    have hSSA := hQ ((Fin N → Fin 3) × Ω) (Fin 3) N (fun i => labelProj i)
      (fun k => labelProj_family k) (fun k l _ a b => labelProj_comm k l a b) (rhoSec c)
      (rhoSec_density c hD)
    have hA' := hA Ω N c hD
    have hB' := hB Ω N c x h1 h2 h3 h4 h5 h6
    have hC' := hC Ω N c hD
    have hsumB : ∑ k : Fin N, vN (pinch (labelProj k) (rhoSec c)) ≤ N * (L + 1 / 200) := by
      calc ∑ k : Fin N, vN (pinch (labelProj k) (rhoSec c)) ≤ ∑ _k : Fin N, (L + 1 / 200) :=
            sum_le_sum fun k _ => hB' k
        _ = N * (L + 1 / 200) := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hent : ∑ z, ent (pSec c z) ≤ L + N / 200 := by
      have : vN (pinchAll (fun i => labelProj i) (rhoSec c)) ≤ L + N / 200 := by
        have h' : ((N : ℝ) - 1) * L ≤ ((N : ℝ) - 1) * vN (rhoSec c) :=
          mul_le_mul_of_nonneg_left hA' (by linarith)
        nlinarith
      linarith
    rw [div_le_iff₀ hl2pos, Real.logb, add_mul, div_mul_cancel₀ _ hl2pos.ne']
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith [mul_nonneg hN0 (le_of_lt (sub_pos.mpr hl2))]

/-- **Proposition `prop:dimension-perm`** from strong subadditivity for commuting pinchings and the
three elementary spectral facts (A)–(C). -/
theorem dimension_perm_of_QIT (hQ : QIT_CommutingPinchingSSA.{u}) (hA : SubStateEntropy.{u})
    (hB : SubTwirlEntropy.{u}) (hC : SubSectorEntropy.{u}) {Ω : Type u} [Fintype Ω]
    [DecidableEq Ω] (φ : F →* Equiv.Perm Ω) (δ : ℝ) (hrel : ∀ i, dH (φ (rel i)) 1 ≤ δ)
    (hγ : 1/2 ≤ dH (φ γ) 1) (N A : ℕ) (hN : 1 ≤ N) (hA' : AstarLE (3 * N) A)
    (hδ : (10:ℝ)^8 * N * max 1 A * δ ≤ 1) :
    (N : ℝ) / 16 ≤ Real.logb 2 (Fintype.card Ω) :=
  dimension_perm_of_sectorEntropy (permSectorEntropy_of_QIT hQ hA hB hC) φ δ hrel hγ N A hN hA' hδ

end Houghton
