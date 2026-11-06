import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.VecNotation
import FiniteLean.GroupTheory.Permutations.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

/-!
# Normalized Hamming distance on permutations

Elementary properties of `Houghton.dH`: it is a bi-invariant pseudometric, products and powers
are Lipschitz, and relations can be "transported in measure": a word of area at most `n`
has `dH (φ w) 1 ≤ n δ` when every relator has defect at most `δ`.
-/

namespace Houghton

open Finset Equiv

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

lemma perm_apply_inv {X : Type*} (f : Perm X) (x : X) : f (f⁻¹ x) = x := by simp

/-- Number of points on which two permutations differ. -/
def hc (g h : Perm Ω) : ℕ := (univ.filter fun x => g x ≠ h x).card

lemma dH_eq (g h : Perm Ω) : dH g h = (hc g h : ℝ) / Fintype.card Ω := rfl

lemma hc_comm (g h : Perm Ω) : hc g h = hc h g := by
  unfold hc
  congr 1
  ext x
  simp [ne_comm]

lemma hc_triangle (g h k : Perm Ω) : hc g k ≤ hc g h + hc h k := by
  unfold hc
  calc (univ.filter fun x => g x ≠ k x).card
      ≤ ((univ.filter fun x => g x ≠ h x) ∪ (univ.filter fun x => h x ≠ k x)).card := by
        apply card_le_card
        intro x
        simp only [mem_filter, mem_union, mem_univ, true_and]
        intro hx
        by_contra hc'
        push Not at hc'
        exact hx (hc'.1.trans hc'.2)
    _ ≤ _ := card_union_le _ _

lemma hc_mul_left (k g h : Perm Ω) : hc (k * g) (k * h) = hc g h := by
  unfold hc
  congr 1
  ext x
  simp [Perm.mul_apply]

lemma hc_mul_right (k g h : Perm Ω) : hc (g * k) (h * k) = hc g h := by
  unfold hc
  have : (univ.filter fun x => (g * k) x ≠ (h * k) x) =
      (univ.filter fun y => g y ≠ h y).image k.symm := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_image]
    simp only [Perm.mul_apply]
    constructor
    · intro hx
      exact ⟨k x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [this, card_image_of_injective _ k.symm.injective]

lemma hc_self (g : Perm Ω) : hc g g = 0 := by
  simp [hc]

lemma dH_nonneg (g h : Perm Ω) : 0 ≤ dH g h :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma dH_self (g : Perm Ω) : dH g g = 0 := by
  simp [dH_eq, hc_self]

lemma dH_comm (g h : Perm Ω) : dH g h = dH h g := by
  simp only [dH_eq, hc_comm g h]

lemma dH_triangle (g h k : Perm Ω) : dH g k ≤ dH g h + dH h k := by
  simp only [dH_eq]
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast hc_triangle g h k

lemma dH_mul_left (k g h : Perm Ω) : dH (k * g) (k * h) = dH g h := by
  simp only [dH_eq, hc_mul_left]

lemma dH_mul_right (k g h : Perm Ω) : dH (g * k) (h * k) = dH g h := by
  simp only [dH_eq, hc_mul_right]

lemma dH_mul_self_left (k g : Perm Ω) : dH (k * g) k = dH g 1 := by
  simpa using dH_mul_left k g 1

lemma dH_mul_le (g₁ g₂ h₁ h₂ : Perm Ω) : dH (g₁ * g₂) (h₁ * h₂) ≤ dH g₁ h₁ + dH g₂ h₂ := by
  calc dH (g₁ * g₂) (h₁ * h₂) ≤ dH (g₁ * g₂) (g₁ * h₂) + dH (g₁ * h₂) (h₁ * h₂) :=
        dH_triangle _ _ _
    _ = dH g₂ h₂ + dH g₁ h₁ := by rw [dH_mul_left, dH_mul_right]
    _ = dH g₁ h₁ + dH g₂ h₂ := add_comm _ _

lemma dH_pow_le (g h : Perm Ω) (m : ℕ) : dH (g ^ m) (h ^ m) ≤ m * dH g h := by
  induction m with
  | zero => simp [dH_self]
  | succ m ih =>
    rw [pow_succ, pow_succ]
    calc dH (g ^ m * g) (h ^ m * h) ≤ dH (g ^ m) (h ^ m) + dH g h := dH_mul_le _ _ _ _
      _ ≤ m * dH g h + dH g h := by linarith
      _ = ((m + 1 : ℕ) : ℝ) * dH g h := by rw [Nat.cast_succ, add_mul, one_mul]

lemma dH_conj (k g : Perm Ω) : dH (k * g * k⁻¹) 1 = dH g 1 := by
  calc dH (k * g * k⁻¹) 1 = dH (k * g * k⁻¹) (k * 1 * k⁻¹) := by simp
    _ = dH (k * g) (k * 1) := dH_mul_right _ _ _
    _ = dH g 1 := dH_mul_left _ _ _

lemma dH_inv_one (g : Perm Ω) : dH g⁻¹ 1 = dH g 1 := by
  calc dH g⁻¹ 1 = dH (g * g⁻¹) (g * 1) := (dH_mul_left _ _ _).symm
    _ = dH 1 g := by simp
    _ = dH g 1 := dH_comm _ _

/-- Commutator defect as distance of the commutator to the identity. -/
lemma dH_comm_eq (g h : Perm Ω) : dH (g * h) (h * g) = dH (g * h * g⁻¹ * h⁻¹) 1 := by
  calc dH (g * h) (h * g) = dH (g * h * (h * g)⁻¹) (h * g * (h * g)⁻¹) :=
        (dH_mul_right _ _ _).symm
    _ = dH (g * h * g⁻¹ * h⁻¹) 1 := by
        rw [mul_inv_cancel, mul_inv_rev, ← mul_assoc]

/-- Moving `z` past a product `x * y` costs at most two interchanges. -/
lemma dH_mul_commutes (x y z : Perm Ω) :
    dH (x * y * z) (z * (x * y)) ≤ dH (x * z) (z * x) + dH (y * z) (z * y) := by
  calc dH (x * y * z) (z * (x * y)) ≤ dH (x * y * z) (x * z * y) + dH (x * z * y) (z * (x * y)) :=
        dH_triangle _ _ _
    _ = dH (y * z) (z * y) + dH (x * z) (z * x) := by
        congr 1
        · rw [mul_assoc, mul_assoc, dH_mul_left]
        · rw [← mul_assoc, dH_mul_right]
    _ = _ := add_comm _ _

lemma dH_commutes_mul (z x y : Perm Ω) :
    dH (z * (x * y)) (x * y * z) ≤ dH (z * x) (x * z) + dH (z * y) (y * z) := by
  rw [dH_comm, dH_comm (z * x), dH_comm (z * y)]
  exact dH_mul_commutes x y z

/-! ### Transport in measure -/



/-! ### Exact rounding of approximate involutions and of approximate order-three elements -/

/-- Keep `A` on its fixed points and `2`-cycles, and replace it by the identity elsewhere. -/
def roundInvFun (A : Perm Ω) (x : Ω) : Ω := if A (A x) = x then A x else x

omit [Fintype Ω] in
lemma roundInvFun_involutive (A : Perm Ω) : Function.Involutive (roundInvFun A) := by
  intro x
  unfold roundInvFun
  by_cases h : A (A x) = x
  · simp [h]
  · simp [h]

/-- The involution obtained by rounding `A`. -/
def roundInv (A : Perm Ω) : Perm Ω := (roundInvFun_involutive A).toPerm _

omit [Fintype Ω] in
lemma roundInv_apply (A : Perm Ω) (x : Ω) :
    roundInv A x = if A (A x) = x then A x else x := rfl

omit [Fintype Ω] in
lemma roundInv_mul_self (A : Perm Ω) : roundInv A * roundInv A = 1 := by
  ext x
  simp only [Perm.mul_apply, Perm.one_apply]
  exact roundInvFun_involutive A x

omit [Fintype Ω] in
lemma roundInv_sq (A : Perm Ω) : roundInv A ^ 2 = 1 := by
  rw [pow_two, roundInv_mul_self]

lemma hc_roundInv (A : Perm Ω) : hc (roundInv A) A ≤ hc (A * A) 1 := by
  unfold hc
  apply card_le_card
  intro x
  simp only [mem_filter, mem_univ, true_and]
  simp only [roundInv_apply, Perm.mul_apply, Perm.one_apply]
  intro hx h
  exact hx (by simp [h])

lemma dH_roundInv (A : Perm Ω) : dH (roundInv A) A ≤ dH (A * A) 1 := by
  simp only [dH_eq]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast hc_roundInv A

/-- Keep `C` on its fixed points and `3`-cycles, and replace it by the identity elsewhere. -/
def round3 (C : Perm Ω) : Perm Ω where
  toFun x := if C (C (C x)) = x then C x else x
  invFun x := if C (C (C x)) = x then C⁻¹ x else x
  left_inv x := by
    by_cases h : C (C (C x)) = x
    · simp [h]
    · simp [h]
  right_inv x := by
    by_cases h : C (C (C x)) = x
    · have h' : C (C (C (C⁻¹ x))) = C⁻¹ x := by
        rw [perm_apply_inv]
        exact Perm.eq_inv_iff_eq.mpr h
      simp only [h, ite_true]
      rw [ite_eq_left h', perm_apply_inv]
    · simp [h]

omit [Fintype Ω] in
lemma round3_apply (C : Perm Ω) (x : Ω) :
    round3 C x = if C (C (C x)) = x then C x else x := rfl

omit [Fintype Ω] in
lemma round3_pow_three (C : Perm Ω) : round3 C ^ 3 = 1 := by
  ext x
  simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply]
  by_cases h : C (C (C x)) = x
  · simp only [round3_apply, h, ite_true]
  · simp only [round3_apply, h, ite_false]

lemma hc_round3 (C : Perm Ω) : hc (round3 C) C ≤ hc (C ^ 3) 1 := by
  unfold hc
  apply card_le_card
  intro x
  simp only [mem_filter, mem_univ, true_and]
  simp only [round3_apply, pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply]
  intro hx h
  exact hx (by simp [h])

lemma dH_round3 (C : Perm Ω) : dH (round3 C) C ≤ dH (C ^ 3) 1 := by
  simp only [dH_eq]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast hc_round3 C

omit [Fintype Ω] in
/-- If `S, T` are involutions, the rounding `C₀` of `C = S T` is inverted by `S`. -/
lemma round3_conj (S T : Perm Ω) (hS : S * S = 1) (hT : T * T = 1) :
    S * round3 (S * T) * S = (round3 (S * T))⁻¹ := by
  set C := S * T with hCdef
  have hSS : ∀ z, S (S z) = z := fun z => by
    simpa [Perm.mul_apply] using congrArg (fun p : Perm Ω => p z) hS
  have hTT : ∀ z, T (T z) = z := fun z => by
    simpa [Perm.mul_apply] using congrArg (fun p : Perm Ω => p z) hT
  -- `C (S z) = S (C⁻¹ z)`
  have hCinv : ∀ z, C⁻¹ z = T (S z) := by
    intro z
    rw [Perm.inv_eq_iff_eq, hCdef, Perm.mul_apply, hTT, hSS]
  have key : ∀ z, C (S z) = S (C⁻¹ z) := by
    intro z
    rw [hCinv, hCdef, Perm.mul_apply]
  have key3 : ∀ z, C (C (C (S z))) = S (C⁻¹ (C⁻¹ (C⁻¹ z))) := by
    intro z
    rw [key, key, key]
  ext y
  simp only [Perm.mul_apply]
  rw [eq_comm, Perm.inv_eq_iff_eq]
  by_cases hy : C (C (C y)) = y
  · -- `y` lies on a short cycle
    have hy3 : C⁻¹ (C⁻¹ (C⁻¹ y)) = y := by
      conv_lhs => rw [← hy]
      simp
    have hSy : C (C (C (S y))) = S y := by rw [key3, hy3]
    have hCy : C (C y) = C⁻¹ y := by
      rw [Perm.eq_inv_iff_eq]
      exact hy
    have hgood : C (C (C (C⁻¹ y))) = C⁻¹ y := by simpa using hCy
    rw [round3_apply C (S y), ite_eq_left hSy, key, hSS, round3_apply, ite_eq_left hgood]
    simp
  · have hSy : ¬ C (C (C (S y))) = S y := by
      intro h
      apply hy
      rw [key3] at h
      have h' : C⁻¹ (C⁻¹ (C⁻¹ y)) = y := by
        have := congrArg S h
        rwa [hSS, hSS] at this
      have h3 := congrArg (fun z => C (C (C z))) h'
      simp only [perm_apply_inv] at h3
      exact h3.symm
    rw [round3_apply C (S y), ite_eq_right hSy, hSS, round3_apply, ite_eq_right hy]

end Houghton
