import FiniteLean.QIT.KroneckerLift
import FiniteLean.QIT.JointConvexity
import FiniteLean.QIT.Interfaces

/-!
# J4: joint convexity of the relative entropy, assuming the integral representation

`relEnt_jointlyConvex_of (hI : IntegralRep)`: the target statement, given step J3
(`QIT.IntegralRep`, proved in `QIT/Integral.lean`).  For each `s > 0` the integrand
`Re ⟪vec 1, (L (R + s L)⁻¹ L - (1 + s)⁻¹ L) vec 1⟫` with `L = ρ ⊗ₖ 1`, `R = 1 ⊗ₖ σᵀ` is jointly
convex in `(ρ, σ)` by J1 (`jointlyConvex_conjTranspose_inv_mul` with `A = L`, `B = R + s L`), and
the inequality is integrated over `s ∈ (0, ∞)`.
-/

namespace QIT

open Matrix MeasureTheory
open scoped ComplexOrder Kronecker

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The integrand of `IntegralRep` for the pair `(L, R)`, at `v = vec 1`. -/
noncomputable def integrand (L R : Matrix (n × n) (n × n) ℂ) (s : ℝ) : ℝ :=
  (dotProduct (star vecOne)
    (Matrix.mulVec (L * (R + (s : ℂ) • L)⁻¹ * L - ((1 + s)⁻¹ : ℂ) • L) vecOne)).re

theorem rsmul_eq {m : Type} (c : ℝ) (M : Matrix m m ℂ) : c • M = (c : ℂ) • M := by
  ext i j; simp [Complex.real_smul]

/-- Pointwise joint convexity of the integrand (J1 with `A = L`, `B = R + s L`). -/
theorem integrand_convex {L₁ L₂ R₁ R₂ : Matrix (n × n) (n × n) ℂ} (hL₁ : L₁.PosDef)
    (hL₂ : L₂.PosDef) (hR₁ : R₁.PosDef) (hR₂ : R₂.PosDef) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {s : ℝ} (hs : 0 ≤ s) :
    integrand (t • L₁ + (1 - t) • L₂) (t • R₁ + (1 - t) • R₂) s ≤
      t * integrand L₁ R₁ s + (1 - t) * integrand L₂ R₂ s := by
  have hB : ∀ {L R : Matrix (n × n) (n × n) ℂ}, L.PosDef → R.PosDef →
      (R + (s : ℂ) • L).PosDef := fun hL hR =>
    hR.add_posSemidef (hL.posSemidef.smul (by exact_mod_cast hs))
  have hJ := jointlyConvex_conjTranspose_inv_mul L₁ L₂ (hB hL₁ hR₁) (hB hL₂ hR₂) ht0 ht1
  have hc : (t • L₁ + (1 - t) • L₂)ᴴ = t • L₁ + (1 - t) • L₂ := by
    rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul, star_trivial, star_trivial,
      hL₁.isHermitian.eq, hL₂.isHermitian.eq]
  rw [hL₁.isHermitian.eq, hL₂.isHermitian.eq, hc] at hJ
  have hBc : t • (R₁ + (s : ℂ) • L₁) + (1 - t) • (R₂ + (s : ℂ) • L₂) =
      (t • R₁ + (1 - t) • R₂) + (s : ℂ) • (t • L₁ + (1 - t) • L₂) := by
    simp only [rsmul_eq]
    module
  rw [hBc] at hJ
  have h := qf_nonneg vecOne hJ
  set c : ℂ := ((1 + s)⁻¹ : ℂ)
  set X₁ := L₁ * (R₁ + (s : ℂ) • L₁)⁻¹ * L₁
  set X₂ := L₂ * (R₂ + (s : ℂ) • L₂)⁻¹ * L₂
  set X := (t • L₁ + (1 - t) • L₂) *
    ((t • R₁ + (1 - t) • R₂) + (s : ℂ) • (t • L₁ + (1 - t) • L₂))⁻¹ * (t • L₁ + (1 - t) • L₂)
  have hid : t • (X₁ - c • L₁) + (1 - t) • (X₂ - c • L₂) - (X - c • (t • L₁ + (1 - t) • L₂)) =
      t • X₁ + (1 - t) • X₂ - X := by
    simp only [rsmul_eq]
    module
  have e : ∀ (L R : Matrix (n × n) (n × n) ℂ), integrand L R s =
      qf vecOne (L * (R + (s : ℂ) • L)⁻¹ * L - c • L) := fun L R => rfl
  rw [e, e, e]
  have := qf_nonneg vecOne hJ
  rw [← hid, qf_sub, qf_add, qf_smul, qf_smul] at this
  linarith

/-- **Joint convexity of the Umegaki relative entropy**, given the integral representation J3. -/
theorem relEnt_jointlyConvex_of (hI : IntegralRep) {ρ₁ ρ₂ σ₁ σ₂ : Matrix n n ℂ}
    (h₁ : ρ₁.PosDef) (h₂ : ρ₂.PosDef) (k₁ : σ₁.PosDef) (k₂ : σ₂.PosDef) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    relEnt (t • ρ₁ + (1 - t) • ρ₂) (t • σ₁ + (1 - t) • σ₂) ≤
      t * relEnt ρ₁ σ₁ + (1 - t) * relEnt ρ₂ σ₂ := by
  have hρ := PosDef.convexComb h₁ h₂ ht0 ht1
  have hσ := PosDef.convexComb k₁ k₂ ht0 ht1
  have rep : ∀ {ρ σ : Matrix n n ℂ}, ρ.PosDef → σ.PosDef →
      IntegrableOn (integrand (liftL ρ) (liftR σ)) (Set.Ioi 0) ∧
        relEnt ρ σ = ∫ s in Set.Ioi (0 : ℝ), integrand (liftL ρ) (liftR σ) s := by
    intro ρ σ hρ hσ
    obtain ⟨hint, heq⟩ := hI (liftL_posDef hρ) (liftR_posDef hσ) (liftL_liftR_commute ρ σ)
      vecOne
    exact ⟨hint, (relEnt_eq_qf hρ hσ).trans heq⟩
  obtain ⟨i0, e0⟩ := rep hρ hσ
  obtain ⟨i1, e1⟩ := rep h₁ k₁
  obtain ⟨i2, e2⟩ := rep h₂ k₂
  rw [e0, e1, e2, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (i1.const_mul t) (i2.const_mul (1 - t))]
  refine setIntegral_mono_on i0 ((i1.const_mul t).add (i2.const_mul (1 - t))) measurableSet_Ioi
    fun s hs => ?_
  rw [liftL_combo, liftR_combo]
  exact integrand_convex (liftL_posDef h₁) (liftL_posDef h₂) (liftR_posDef k₁) (liftR_posDef k₂)
    ht0 ht1 (le_of_lt hs)

end QIT
