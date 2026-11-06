import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Analysis.Matrix.Spectrum
import FiniteLean.QIT.Entropy.SSAPinch
import Mathlib.Tactic.Module

/-!
# Pinchings as compositions of binary pinchings

Step (2) of the SSA chain, in a root-of-unity-free form: for a single projection `P`, the binary
pinching `X ↦ PXP + (1-P)X(1-P)` is the average `(X + RXR)/2` of two unitary conjugations
(`R = 1 - 2P`), and the pinching by a complete family `{P_a}` is the composition of the binary
pinchings by the `P_a`.  Hence monotonicity under all binary pinchings implies monotonicity under
all pinchings.
-/

universe u

namespace Houghton

open Finset Matrix

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Binary pinching. -/
noncomputable def binPinch (P X : Matrix ι ι ℂ) : Matrix ι ι ℂ := P * X * P + (1 - P) * X * (1 - P)

/-- The binary pinching is the average of `X` and `RXR`, `R = 1 - 2P`. -/
lemma binPinch_eq_avg (P X : Matrix ι ι ℂ) (hPP : P * P = P) :
    binPinch P X = (1 / 2 : ℂ) • (X + (1 - (2 : ℂ) • P) * X * (1 - (2 : ℂ) • P)) := by
  have e : (1 - (2 : ℂ) • P) * X * (1 - (2 : ℂ) • P) =
      X - (2 : ℂ) • (P * X) - (2 : ℂ) • (X * P) + (4 : ℂ) • (P * X * P) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    module
  rw [e, binPinch]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  module

lemma reflection_sq (P : Matrix ι ι ℂ) (hPP : P * P = P) :
    (1 - (2 : ℂ) • P) * (1 - (2 : ℂ) • P) = 1 := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, hPP]
  module

lemma reflection_herm (P : Matrix ι ι ℂ) (hP : Pᴴ = P) :
    (1 - (2 : ℂ) • P)ᴴ = 1 - (2 : ℂ) • P := by
  rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hP]
  congr 1
  simp

/-- Partial pinching by the projections in `s`. -/
noncomputable def partPinch {α : Type} (P : α → Matrix ι ι ℂ) (s : Finset α) (X : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  ∑ a ∈ s, P a * X * P a + (1 - ∑ a ∈ s, P a) * X * (1 - ∑ a ∈ s, P a)

lemma partPinch_empty {α : Type} (P : α → Matrix ι ι ℂ) (X : Matrix ι ι ℂ) :
    partPinch P ∅ X = X := by
  simp [partPinch]

lemma partPinch_insert {α : Type} [Fintype α] [DecidableEq α] (P : α → Matrix ι ι ℂ)
    (hP : IsProjFamily P) (s : Finset α) (b : α) (hb : b ∉ s) (X : Matrix ι ι ℂ) :
    partPinch P (insert b s) X = binPinch (P b) (partPinch P s X) := by
  have orth : ∀ a c, a ≠ c → P a * P c = 0 := fun a c h => by rw [hP.orth, if_neg h]
  have idem : ∀ a, P a * P a = P a := fun a => by rw [hP.orth, if_pos rfl]
  set Q := 1 - ∑ a ∈ s, P a with hQ
  have hbQ : P b * Q = P b := by
    rw [hQ, Matrix.mul_sub, Matrix.mul_one, Finset.mul_sum,
      Finset.sum_eq_zero (fun a ha => orth b a (fun h => hb (h ▸ ha))), sub_zero]
  have hQb : Q * P b = P b := by
    rw [hQ, Matrix.sub_mul, Matrix.one_mul, Finset.sum_mul,
      Finset.sum_eq_zero (fun a ha => orth a b (fun h => hb (h ▸ ha))), sub_zero]
  have hba : ∀ a ∈ s, P b * P a = 0 := fun a ha => orth b a (fun h => hb (h ▸ ha))
  have hab : ∀ a ∈ s, P a * P b = 0 := fun a ha => orth a b (fun h => hb (h ▸ ha))
  unfold partPinch binPinch
  rw [Finset.sum_insert hb, Finset.sum_insert hb]
  rw [← hQ]
  -- `P_b Y P_b = P_b X P_b`
  have h1 : P b * (∑ a ∈ s, P a * X * P a + Q * X * Q) * P b = P b * X * P b := by
    rw [Matrix.mul_add, Matrix.add_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_eq_zero (fun a ha => by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hba a ha]; simp)]
    rw [zero_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hbQ, Matrix.mul_assoc, hQb]
  -- `(1-P_b) Y (1-P_b) = ∑ P_a X P_a + (Q - P_b) X (Q - P_b)`
  have h2 : (1 - P b) * (∑ a ∈ s, P a * X * P a + Q * X * Q) * (1 - P b) =
      ∑ a ∈ s, P a * X * P a + (Q - P b) * X * (Q - P b) := by
    rw [Matrix.mul_add, Matrix.add_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun a ha => ?_
      have e1 : (1 - P b) * P a = P a := by rw [Matrix.sub_mul, Matrix.one_mul, hba a ha, sub_zero]
      have e2 : P a * (1 - P b) = P a := by rw [Matrix.mul_sub, Matrix.mul_one, hab a ha, sub_zero]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.mul_assoc, e2]
    · have e1 : (1 - P b) * Q = Q - P b := by rw [Matrix.sub_mul, Matrix.one_mul, hbQ]
      have e2 : Q * (1 - P b) = Q - P b := by rw [Matrix.mul_sub, Matrix.mul_one, hQb]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.mul_assoc, e2]
  rw [h1, h2]
  have e3 : 1 - (P b + ∑ a ∈ s, P a) = Q - P b := by rw [hQ]; abel
  rw [e3]
  abel

lemma partPinch_univ {α : Type} [Fintype α] [DecidableEq α] (P : α → Matrix ι ι ℂ)
    (hP : IsProjFamily P) (X : Matrix ι ι ℂ) : partPinch P univ X = pinch P X := by
  simp [partPinch, pinch, hP.sum_one]

/-- Monotonicity under all binary pinchings implies monotonicity under all pinchings. -/
theorem mono_pinch_of_binary (pd : Matrix ι ι ℂ → Prop) (D : Matrix ι ι ℂ → Matrix ι ι ℂ → ℝ)
    (hpd2 : ∀ P : Matrix ι ι ℂ, Pᴴ = P → P * P = P → ∀ X, pd X → pd (binPinch P X))
    (hmono2 : ∀ P : Matrix ι ι ℂ, Pᴴ = P → P * P = P → ∀ X Y, pd X → pd Y →
      D (binPinch P X) (binPinch P Y) ≤ D X Y)
    {α : Type} [Fintype α] [DecidableEq α] (P : α → Matrix ι ι ℂ) (hP : IsProjFamily P) :
    (∀ X, pd X → pd (pinch P X)) ∧
      ∀ X Y, pd X → pd Y → D (pinch P X) (pinch P Y) ≤ D X Y := by
  have idem : ∀ a, P a * P a = P a := fun a => by rw [hP.orth, if_pos rfl]
  have key : ∀ s : Finset α, (∀ X, pd X → pd (partPinch P s X)) ∧
      ∀ X Y, pd X → pd Y → D (partPinch P s X) (partPinch P s Y) ≤ D X Y := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨fun X hX => by rwa [partPinch_empty], fun X Y _ _ => by
        rw [partPinch_empty, partPinch_empty]⟩
    | insert b s hb ih =>
      refine ⟨fun X hX => ?_, fun X Y hX hY => ?_⟩
      · rw [partPinch_insert P hP s b hb]
        exact hpd2 (P b) (hP.herm b) (idem b) _ (ih.1 X hX)
      · rw [partPinch_insert P hP s b hb, partPinch_insert P hP s b hb]
        exact (hmono2 (P b) (hP.herm b) (idem b) _ _ (ih.1 X hX) (ih.1 Y hY)).trans
          (ih.2 X Y hX hY)
  obtain ⟨k1, k2⟩ := key univ
  exact ⟨fun X hX => by rw [← partPinch_univ P hP]; exact k1 X hX,
    fun X Y hX hY => by rw [← partPinch_univ P hP, ← partPinch_univ P hP]; exact k2 X Y hX hY⟩

end Houghton
