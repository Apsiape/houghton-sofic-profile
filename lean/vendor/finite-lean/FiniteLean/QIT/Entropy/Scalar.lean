import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.VecNotation

namespace Houghton
open Finset Equiv
/-- `η(x) = -x log x` (natural logarithm); this is `Real.negMulLog`. -/
noncomputable def ent (x : ℝ) : ℝ := -(x * Real.log x)

/-- The flip `ω ↔ ω²` of a `ℤ/3`-label (`0 ↦ 0, 1 ↦ 2, 2 ↦ 1`). -/
def fl : Fin 3 → Fin 3 := ![0, 2, 1]

/-- Flip the `i`-th label. -/
def flipAt {n : ℕ} (i : Fin n) (z : Fin n → Fin 3) : Fin n → Fin 3 :=
  Function.update z i (fl (z i))

/-- Unnormalized Shannon entropy in nats: `∑ η(p z) - η(∑ p z)`. -/
noncomputable def Ent {n : ℕ} (p : (Fin n → Fin 3) → ℝ) : ℝ :=
  ∑ z, ent (p z) - ent (∑ z, p z)

/-- Mass of the nontrivial labels in coordinate `i`. -/
noncomputable def sAt {n : ℕ} (i : Fin n) (p : (Fin n → Fin 3) → ℝ) : ℝ :=
  ∑ z, if z i = 0 then 0 else p z

/-- Bhattacharyya defect of the flip in coordinate `i`. -/
noncomputable def dAt {n : ℕ} (i : Fin n) (p : (Fin n → Fin 3) → ℝ) : ℝ :=
  ∑ z, if z i = 0 then 0 else p z - Real.sqrt (p z * p (flipAt i z))

lemma ent_one : ent 1 = 0 := by simp [ent]

lemma mul_log_le_mul_log {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a * Real.log a ≤ a * Real.log b := by
  rcases ha.eq_or_lt with h | h
  · subst h; simp
  · exact mul_le_mul_of_nonneg_left (Real.log_le_log h hab) ha

lemma ent_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : ent (a + b) ≤ ent a + ent b := by
  have h1 := mul_log_le_mul_log ha (le_add_of_nonneg_right hb : a ≤ a + b)
  have h2 := mul_log_le_mul_log hb (le_add_of_nonneg_left ha : b ≤ a + b)
  have e : (a + b) * Real.log (a + b) = a * Real.log (a + b) + b * Real.log (a + b) :=
    add_mul _ _ _
  simp only [ent]
  linarith

/-- `-u log u ≥ u log 2 - u log S - u (2u/S - 1)`, from `log x ≤ x - 1` at `x = 2u/S`. -/
lemma ent_ge (u S : ℝ) (hu : 0 ≤ u) (hS : 0 < S) :
    u * Real.log 2 - u * Real.log S - u * (2 * u / S - 1) ≤ ent u := by
  rcases hu.eq_or_lt with h | h
  · subst h; simp [ent]
  · have hl : Real.log (2 * u / S) = Real.log 2 + Real.log u - Real.log S := by
      rw [Real.log_div (by positivity) hS.ne', Real.log_mul (by norm_num) h.ne']
    have hle := Real.log_le_sub_one_of_pos (show 0 < 2 * u / S by positivity)
    rw [hl] at hle
    have hm := mul_le_mul_of_nonneg_left hle h.le
    have e : u * (Real.log 2 + Real.log u - Real.log S) =
        u * Real.log 2 + u * Real.log u - u * Real.log S := by ring
    simp only [ent]
    linarith

/-- Two-point estimate: `(u+w) h(u/(u+w)) ≥ (u+w) ln 2 - 2 (√u - √w)²` (nats). -/
lemma pair_bound (u w : ℝ) (hu : 0 ≤ u) (hw : 0 ≤ w) :
    Real.log 2 * (u + w) - 2 * (u + w - 2 * (Real.sqrt u * Real.sqrt w)) ≤
      ent u + ent w - ent (u + w) := by
  rcases (add_nonneg hu hw).eq_or_lt with h | hS
  · have hu0 : u = 0 := by linarith
    have hw0 : w = 0 := by linarith
    subst hu0; subst hw0; simp [ent]
  · have h1 := ent_ge u (u + w) hu hS
    have h2 := ent_ge w (u + w) hw hS
    have ha : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu
    have hb : Real.sqrt w ^ 2 = w := Real.sq_sqrt hw
    have hab : (u - w) ^ 2 ≤ 2 * (u + w - 2 * (Real.sqrt u * Real.sqrt w)) * (u + w) := by
      have e : 2 * (Real.sqrt u ^ 2 + Real.sqrt w ^ 2 - 2 * (Real.sqrt u * Real.sqrt w)) *
          (Real.sqrt u ^ 2 + Real.sqrt w ^ 2) - (Real.sqrt u ^ 2 - Real.sqrt w ^ 2) ^ 2 =
          ((Real.sqrt u - Real.sqrt w) ^ 2) ^ 2 := by ring
      rw [ha, hb] at e
      nlinarith [sq_nonneg ((Real.sqrt u - Real.sqrt w) ^ 2)]
    have key : u * (2 * u / (u + w) - 1) + w * (2 * w / (u + w) - 1) ≤
        2 * (u + w - 2 * (Real.sqrt u * Real.sqrt w)) := by
      have e : u * (2 * u / (u + w) - 1) + w * (2 * w / (u + w) - 1) = (u - w) ^ 2 / (u + w) := by
        field_simp
        ring
      rw [e, div_le_iff₀ hS]
      exact hab
    have e2 : (u + w) * Real.log (u + w) = u * Real.log (u + w) + w * Real.log (u + w) :=
      add_mul _ _ _
    simp only [ent] at h1 h2 ⊢
    linarith

lemma triple_bound (m u w : ℝ) (hm : 0 ≤ m) (hu : 0 ≤ u) (hw : 0 ≤ w) :
    Real.log 2 * (u + w) - 2 * (u + w - 2 * (Real.sqrt u * Real.sqrt w)) ≤
      ent m + ent u + ent w - ent (m + u + w) := by
  have h1 := pair_bound u w hu hw
  have h2 := ent_add_le hm (add_nonneg hu hw)
  rw [← add_assoc] at h2
  linarith

lemma sum_cons3 {n : ℕ} (F : (Fin (n + 1) → Fin 3) → ℝ) :
    ∑ z, F z = ∑ a : Fin 3, ∑ z' : Fin n → Fin 3, F (Fin.cons a z') := by
  rw [← (Fin.consEquiv (fun _ => Fin 3)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma flipAt_succ_cons {n : ℕ} (i : Fin n) (a : Fin 3) (z' : Fin n → Fin 3) :
    flipAt i.succ (Fin.cons a z' : Fin (n + 1) → Fin 3) = Fin.cons a (flipAt i z') := by
  simp only [flipAt, Fin.cons_succ]
  exact (Fin.cons_update ..).symm

lemma flipAt_zero_cons {n : ℕ} (a : Fin 3) (z' : Fin n → Fin 3) :
    flipAt 0 (Fin.cons a z' : Fin (n + 1) → Fin 3) = Fin.cons (fl a) z' := by
  simp only [flipAt, Fin.cons_zero]
  exact Fin.update_cons_zero _ _ _

/-- **Chain-rule estimate.** `H(p) ≥ ∑ᵢ (ln 2 · sᵢ - 2 dᵢ)` (nats, unnormalized). -/
theorem Ent_ge : ∀ (n : ℕ) (p : (Fin n → Fin 3) → ℝ), (∀ z, 0 ≤ p z) →
    ∑ i, (Real.log 2 * sAt i p - 2 * dAt i p) ≤ Ent p
  | 0, p, _ => by simp [Ent]
  | n + 1, p, hp => by
    let q : Fin 3 → (Fin n → Fin 3) → ℝ := fun a z' => p (Fin.cons a z')
    have hq0 : ∀ a z', 0 ≤ q a z' := fun a z' => hp _
    let m : Fin 3 → ℝ := fun a => ∑ z', q a z'
    have hm0 : ∀ a, 0 ≤ m a := fun a => sum_nonneg (fun z' _ => hq0 a z')
    have ih : ∀ a, ∑ i, (Real.log 2 * sAt i (q a) - 2 * dAt i (q a)) ≤ Ent (q a) :=
      fun a => Ent_ge n (q a) (hq0 a)
    -- decomposition of the entropy
    have hEnt : Ent p = ∑ a, Ent (q a) +
        (ent (m 0) + ent (m 1) + ent (m 2) - ent (m 0 + m 1 + m 2)) := by
      simp only [Ent]
      rw [sum_cons3 (fun z => ent (p z)), sum_cons3 (fun z => p z)]
      simp only [Fin.sum_univ_three, sum_sub_distrib]
      ring
    -- coordinate `0`
    have hs0 : sAt 0 p = m 1 + m 2 := by
      simp only [sAt]
      rw [sum_cons3]
      simp [Fin.sum_univ_three, m, q]
    have hd0 : dAt 0 p = m 1 + m 2 - 2 * ∑ z', Real.sqrt (q 1 z' * q 2 z') := by
      have fl1 : fl 1 = 2 := rfl
      have fl2 : fl 2 = 1 := rfl
      have e : ∀ z' : Fin n → Fin 3, Real.sqrt (p (Fin.cons 2 z') * p (Fin.cons 1 z')) =
          Real.sqrt (p (Fin.cons 1 z') * p (Fin.cons 2 z')) := fun z' => by rw [mul_comm]
      simp only [dAt]
      rw [sum_cons3, Fin.sum_univ_three]
      simp [flipAt_zero_cons, fl1, fl2, sum_sub_distrib, m, q, e]
      ring
    have hcs : ∑ z', Real.sqrt (q 1 z' * q 2 z') ≤ Real.sqrt (m 1) * Real.sqrt (m 2) := by
      calc ∑ z', Real.sqrt (q 1 z' * q 2 z') = ∑ z', Real.sqrt (q 1 z') * Real.sqrt (q 2 z') :=
            sum_congr rfl (fun z' _ => Real.sqrt_mul (hq0 1 z') _)
        _ ≤ _ := Real.sum_sqrt_mul_sqrt_le univ (hq0 1) (hq0 2)
    have hT0 : Real.log 2 * sAt 0 p - 2 * dAt 0 p ≤
        ent (m 0) + ent (m 1) + ent (m 2) - ent (m 0 + m 1 + m 2) := by
      have := triple_bound (m 0) (m 1) (m 2) (hm0 0) (hm0 1) (hm0 2)
      rw [hs0, hd0]
      linarith
    -- the other coordinates
    have hsucc : ∀ i : Fin n, Real.log 2 * sAt i.succ p - 2 * dAt i.succ p =
        ∑ a, (Real.log 2 * sAt i (q a) - 2 * dAt i (q a)) := by
      intro i
      have hs : sAt i.succ p = ∑ a, sAt i (q a) := by
        simp only [sAt]
        rw [sum_cons3]
        simp [q]
      have hd : dAt i.succ p = ∑ a, dAt i (q a) := by
        simp only [dAt]
        rw [sum_cons3]
        simp [q, flipAt_succ_cons]
      rw [hs, hd, mul_sum, mul_sum, ← sum_sub_distrib]
    rw [Fin.sum_univ_succ, hEnt]
    simp only [hsucc]
    rw [sum_comm]
    have := sum_le_sum (fun a (_ : a ∈ univ) => ih a)
    linarith


end Houghton
