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
import FiniteLean.QIT.Entropy.Basic

/-!
# Strong subadditivity for commuting pinchings: the telescoping argument

Steps (5) of the SSA chain, independent of the analytic inputs: commuting pinchings commute, and
the inequality of `QIT_CommutingPinchingSSA` follows by telescoping from
* (4) `S(Πσ) - S(σ) = D(σ‖Πσ)` and
* (3) `D(Πρ‖Πσ) ≤ D(ρ‖σ)`,
for any "entropy" `S`, "relative entropy" `D` and class `pd` of states preserved by pinchings.
-/

universe u

namespace Houghton

open Finset Matrix

section Pinch

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {α β : Type} [Fintype α] [Fintype β]

/-- Commuting projection families give commuting pinchings. -/
lemma pinch_pinch_comm (P : α → Matrix ι ι ℂ) (Q : β → Matrix ι ι ℂ)
    (hPQ : ∀ a b, P a * Q b = Q b * P a) (X : Matrix ι ι ℂ) :
    pinch P (pinch Q X) = pinch Q (pinch P X) := by
  simp only [pinch, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  calc P a * (Q b * X * Q b) * P a = (P a * Q b) * X * (Q b * P a) := by
        simp only [Matrix.mul_assoc]
    _ = (Q b * P a) * X * (P a * Q b) := by rw [hPQ a b]
    _ = Q b * (P a * X * P a) * Q b := by simp only [Matrix.mul_assoc]

lemma pinch_add (P : α → Matrix ι ι ℂ) (X Y : Matrix ι ι ℂ) :
    pinch P (X + Y) = pinch P X + pinch P Y := by
  simp only [pinch, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

lemma pinch_smul (P : α → Matrix ι ι ℂ) (c : ℂ) (X : Matrix ι ι ℂ) :
    pinch P (c • X) = c • pinch P X := by
  simp only [pinch, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

lemma pinchAll_pinch_comm {m : ℕ} (P : Fin m → α → Matrix ι ι ℂ) (Q : α → Matrix ι ι ℂ)
    (hPQ : ∀ k a b, P k a * Q b = Q b * P k a) (X : Matrix ι ι ℂ) :
    pinchAll P (pinch Q X) = pinch Q (pinchAll P X) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [pinchAll]
    rw [ih (fun k => P k.succ) (fun k a b => hPQ k.succ a b)]
    exact pinch_pinch_comm (P 0) Q (hPQ 0) _

end Pinch

/-! ### Abstract telescoping -/

section Telescope

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {α : Type} [Fintype α] [DecidableEq α]

/-- Monotonicity under a composition of pinchings, from monotonicity under each pinching. -/
lemma mono_pinchAll (pd : Matrix ι ι ℂ → Prop) (D : Matrix ι ι ℂ → Matrix ι ι ℂ → ℝ)
    (hpd : ∀ (P : α → Matrix ι ι ℂ), IsProjFamily P → ∀ X, pd X → pd (pinch P X))
    (hmono : ∀ (P : α → Matrix ι ι ℂ), IsProjFamily P → ∀ X Y, pd X → pd Y →
      D (pinch P X) (pinch P Y) ≤ D X Y) :
    ∀ {m : ℕ} (P : Fin m → α → Matrix ι ι ℂ), (∀ k, IsProjFamily (P k)) →
      ∀ X Y, pd X → pd Y → (pd (pinchAll P X) ∧ D (pinchAll P X) (pinchAll P Y) ≤ D X Y)
  | 0, _, _, X, Y, hX, _ => ⟨hX, le_rfl⟩
  | m + 1, P, hP, X, Y, hX, hY => by
    obtain ⟨hX', hD'⟩ := mono_pinchAll pd D hpd hmono (fun k => P k.succ) (fun k => hP k.succ)
      X Y hX hY
    have hY' := (mono_pinchAll pd D hpd hmono (fun k => P k.succ) (fun k => hP k.succ)
      Y Y hY hY).1
    refine ⟨hpd (P 0) (hP 0) _ hX', ?_⟩
    exact (hmono (P 0) (hP 0) _ _ hX' hY').trans hD'

/-- **Telescoping**: steps (3), (4) and commutation give the commuting-pinching SSA inequality on
the class `pd`. -/
theorem ssa_telescope (pd : Matrix ι ι ℂ → Prop) (S : Matrix ι ι ℂ → ℝ)
    (D : Matrix ι ι ℂ → Matrix ι ι ℂ → ℝ)
    (hpd : ∀ (P : α → Matrix ι ι ℂ), IsProjFamily P → ∀ X, pd X → pd (pinch P X))
    (hmono : ∀ (P : α → Matrix ι ι ℂ), IsProjFamily P → ∀ X Y, pd X → pd Y →
      D (pinch P X) (pinch P Y) ≤ D X Y)
    (hgain : ∀ (P : α → Matrix ι ι ℂ), IsProjFamily P → ∀ X, pd X →
      S (pinch P X) - S X = D X (pinch P X)) :
    ∀ (m : ℕ) (P : Fin m → α → Matrix ι ι ℂ), (∀ k, IsProjFamily (P k)) →
      (∀ k l, k ≠ l → ∀ a b, P k a * P l b = P l b * P k a) →
      ∀ ρ, pd ρ → S (pinchAll P ρ) + m * S ρ ≤ ∑ k, S (pinch (P k) ρ) + S ρ
  | 0, P, _, _, ρ, _ => by simp [pinchAll]
  | m + 1, P, hP, hcomm, ρ, hρ => by
    set P' : Fin m → α → Matrix ι ι ℂ := fun k => P k.succ
    have hP' : ∀ k, IsProjFamily (P' k) := fun k => hP k.succ
    have hcomm' : ∀ k l, k ≠ l → ∀ a b, P' k a * P' l b = P' l b * P' k a :=
      fun k l hkl a b => hcomm k.succ l.succ (fun h => hkl (Fin.succ_injective _ h)) a b
    have ih := ssa_telescope pd S D hpd hmono hgain m P' hP' hcomm' ρ hρ
    have hE := mono_pinchAll pd D hpd hmono P' hP' ρ (pinch (P 0) ρ) hρ
      (hpd (P 0) (hP 0) ρ hρ)
    have hc : pinchAll P' (pinch (P 0) ρ) = pinch (P 0) (pinchAll P' ρ) :=
      pinchAll_pinch_comm P' (P 0)
        (fun k a b => hcomm k.succ 0 (Fin.succ_ne_zero k) a b) ρ
    have g1 := hgain (P 0) (hP 0) (pinchAll P' ρ) hE.1
    have g2 := hgain (P 0) (hP 0) ρ hρ
    rw [hc] at hE
    have hstep : S (pinchAll P ρ) - S (pinchAll P' ρ) ≤ S (pinch (P 0) ρ) - S ρ := by
      show S (pinch (P 0) (pinchAll P' ρ)) - S (pinchAll P' ρ) ≤ _
      rw [g1, g2]
      exact hE.2
    rw [Fin.sum_univ_succ]
    push_cast
    linarith

end Telescope

end Houghton
