import FiniteLean.QIT.Basic

/-!
# Joint convexity of the relative entropy: blueprint and first layer

Route (integral representation + Schur complements; no operator Jensen needed):

* (J1, proved here) `jointlyConvex_conjTranspose_inv_mul`: `(A, B) ↦ Aᴴ B⁻¹ A` is jointly
  matrix-convex on `{B > 0}` (Schur complement of `[[B, A], [Aᴴ, Aᴴ B⁻¹ A]] ≥ 0`).
* (J2, pending) Kronecker lift: `L_ρ = ρ ⊗ₖ 1` and `R_σ = 1 ⊗ₖ σᵀ` commute, are positive definite,
  and `relEnt ρ σ = Re ⟪vec 1, (L_ρ log L_ρ - L_ρ log R_σ) vec 1⟫`.
* (J3, pending) Integral representation, for commuting positive definite `L, R`:
  `L (log L - log R) = ∫₀^∞ (L (R + s L)⁻¹ L - (1 + s)⁻¹ L) ds`
  (scalar identity `p (log p - log q) = ∫₀^∞ (p² / (q + s p) - p / (1 + s)) ds` in a joint
  eigenbasis).
* (J4) For each `s ≥ 0`, `(L, R) ↦ L (R + s L)⁻¹ L` is J1 with `A = L`, `B = R + s L` (affine in
  `(L, R)`), and `L/(1+s)` is linear; integrating gives joint convexity of `relEnt`.

The pending steps J2–J4 are not yet stated in Lean; no axioms are used.
-/

namespace QIT

open Matrix
open scoped ComplexOrder

variable {m k : Type} [Fintype m] [DecidableEq m] [Fintype k]

omit [Fintype m] [DecidableEq m] in
/-- Real convex combinations of positive definite matrices are positive definite. -/
theorem PosDef.convexComb {B₁ B₂ : Matrix m m ℂ} (h₁ : B₁.PosDef) (h₂ : B₂.PosDef) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (t • B₁ + (1 - t) • B₂).PosDef := by
  have e : ∀ (c : ℝ) (M : Matrix m m ℂ), c • M = (c : ℂ) • M := fun c M => by
    ext i j; simp [Complex.real_smul]
  rw [e, e]
  rcases ht0.lt_or_eq with ht | ht
  · refine (h₁.smul (by exact_mod_cast ht)).add_posSemidef (h₂.posSemidef.smul ?_)
    exact_mod_cast sub_nonneg.2 ht1
  · subst ht
    simpa using h₂

/-- **J1.** `(A, B) ↦ Aᴴ B⁻¹ A` is jointly matrix-convex on `{B > 0}`. -/
theorem jointlyConvex_conjTranspose_inv_mul (A₁ A₂ : Matrix m k ℂ) {B₁ B₂ : Matrix m m ℂ}
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (t • (A₁ᴴ * B₁⁻¹ * A₁) + (1 - t) • (A₂ᴴ * B₂⁻¹ * A₂) -
      (t • A₁ + (1 - t) • A₂)ᴴ * (t • B₁ + (1 - t) • B₂)⁻¹ * (t • A₁ + (1 - t) • A₂)).PosSemidef := by
  classical
  have e : ∀ (c : ℝ) {p q : Type} (M : Matrix p q ℂ), c • M = (c : ℂ) • M := fun c _ _ M => by
    ext i j; simp [Complex.real_smul]
  have hB := PosDef.convexComb hB₁ hB₂ ht0 ht1
  let _ := hB₁.isUnit.invertible
  let _ := hB₂.isUnit.invertible
  let _ := hB.isUnit.invertible
  have hM : ∀ (A : Matrix m k ℂ) {B : Matrix m m ℂ} (hB : B.PosDef) [Invertible B],
      (fromBlocks B A Aᴴ (Aᴴ * B⁻¹ * A)).PosSemidef := by
    intro A B hB _
    rw [Matrix.PosDef.fromBlocks₁₁ A _ hB, sub_self]
    exact PosSemidef.zero
  have h1 := (hM A₁ hB₁).smul (show (0 : ℂ) ≤ (t : ℂ) by exact_mod_cast ht0)
  have h2 := (hM A₂ hB₂).smul (show (0 : ℂ) ≤ ((1 - t : ℝ) : ℂ) by exact_mod_cast sub_nonneg.2 ht1)
  have hsum := h1.add h2
  rw [fromBlocks_smul, fromBlocks_smul, fromBlocks_add, ← e, ← e, ← e, ← e, ← e, ← e, ← e, ← e]
    at hsum
  have hc : (t • A₁ + (1 - t) • A₂)ᴴ = t • A₁ᴴ + (1 - t) • A₂ᴴ := by
    rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul, star_trivial, star_trivial]
  refine (Matrix.PosDef.fromBlocks₁₁ (t • A₁ + (1 - t) • A₂) _ hB).1 ?_
  rw [hc]
  exact hsum

end QIT
