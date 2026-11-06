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
import Mathlib.Tactic.Module
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.PosDef
import FiniteLean.QIT.Entropy.SSAInterface
import FiniteLean.QIT.Entropy.Spectral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Steps (1) and (4): `S = -Tr(ρ log ρ)` and the entropy gain of a pinching

(1) For Hermitian `A`, `Tr(A · f(A)) = ∑ λᵢ f(λᵢ)`; hence `vN A = -Re Tr(A · qmlog A)`.
(4) For positive definite `σ` and a pinching `Π`, `S(Πσ) - S(σ) = D(σ ‖ Πσ)`, because `log Πσ`
commutes with the projections.  With step (3) and the telescoping of `SSAPinch` this gives the
commuting-pinching SSA inequality for positive definite states.
-/

namespace Houghton

open Finset Matrix
open scoped ComplexOrder

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Step (1): `Tr(A f(A)) = ∑ λᵢ f(λᵢ)`. -/
lemma trace_mul_cfc {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (A * cfc f A).trace = ∑ i, (((hA.eigenvalues i) * f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hdec : A = U * diagonal (fun j => (hA.eigenvalues j : ℂ)) * star U := herm_decomp hA
  have e0 : A * (U * diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) * star U) =
      U * diagonal (fun j => (hA.eigenvalues j : ℂ)) * star U *
        (U * diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) * star U) := by
    rw [← hdec]
  rw [e0]
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have e : U * diagonal (fun j => (hA.eigenvalues j : ℂ)) * star U *
      (U * diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) * star U) =
      U * (diagonal (fun j => (hA.eigenvalues j : ℂ)) * diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues))
        * star U := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul]
  rw [e, Matrix.trace_mul_cycle, hUU, Matrix.one_mul, diagonal_mul_diagonal, trace_diagonal]
  refine sum_congr rfl fun i _ => ?_
  simp

/-- `vN A = -Re Tr(A · log A)`. -/
lemma vN_eq_trace {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    vN A = -(A * qmlog A).trace.re := by
  rw [qmlog, trace_mul_cfc hA, Complex.re_sum, vN_eq hA, ← sum_neg_distrib]
  refine sum_congr rfl fun i _ => ?_
  simp [ent]

/-- Pinchings preserve positive definiteness (no analytic input needed). -/
lemma posDef_pinch {α : Type} [Fintype α] [DecidableEq α] (P : α → Matrix n n ℂ)
    (hP : IsProjFamily P) (X : Matrix n n ℂ) (hX : X.PosDef) : (pinch P X).PosDef :=
  (mono_pinch_of_binary (fun X => X.PosDef) (fun _ _ => (0 : ℝ))
    (fun P hP hPP X hX => posDef_binPinch P X hP hPP hX) (fun _ _ _ _ _ _ _ => le_rfl) P hP).1 X hX

lemma pinch_commute {α : Type} [Fintype α] [DecidableEq α] (P : α → Matrix n n ℂ)
    (hP : IsProjFamily P) (X : Matrix n n ℂ) (a : α) : Commute (pinch P X) (P a) := by
  have orth : ∀ b c, P b * P c = if b = c then P b else 0 := hP.orth
  unfold Commute SemiconjBy pinch
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : b = a
  · subst h
    rw [Matrix.mul_assoc, orth, if_pos rfl, ← Matrix.mul_assoc, ← Matrix.mul_assoc, orth,
      if_pos rfl, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, orth, if_neg h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, orth,
      if_neg (Ne.symm h)]
    simp

/-- `Tr(X L) = Tr(Π(X) L)` when `L` commutes with the projections. -/
lemma trace_pinch_mul {α : Type} [Fintype α] [DecidableEq α] (P : α → Matrix n n ℂ)
    (hP : IsProjFamily P) (X L : Matrix n n ℂ) (hL : ∀ a, Commute L (P a)) :
    (pinch P X * L).trace = (X * L).trace := by
  have idem : ∀ a, P a * P a = P a := fun a => by rw [hP.orth, if_pos rfl]
  unfold pinch
  rw [Finset.sum_mul, trace_sum]
  have e : ∀ a, (P a * X * P a * L).trace = (X * L * P a).trace := by
    intro a
    calc (P a * X * P a * L).trace = (P a * X * (P a * L)).trace := by
          rw [Matrix.mul_assoc (P a * X)]
      _ = (P a * X * (L * P a)).trace := by rw [(hL a).eq]
      _ = (X * (L * P a) * P a).trace := by
          rw [Matrix.mul_assoc (P a), Matrix.trace_mul_comm, Matrix.mul_assoc]
      _ = (X * L * P a).trace := by
          rw [Matrix.mul_assoc X, Matrix.mul_assoc L, idem, ← Matrix.mul_assoc]
  simp only [e]
  rw [← trace_sum, ← Finset.mul_sum, hP.sum_one, Matrix.mul_one]

/-- **Step (4)**: entropy gain of a pinching. -/
theorem vN_pinch_gain {α : Type} [Fintype α] [DecidableEq α] (P : α → Matrix n n ℂ)
    (hP : IsProjFamily P) (σ : Matrix n n ℂ) (hσ : σ.PosDef) :
    vN (pinch P σ) - vN σ = qrelEnt σ (pinch P σ) := by
  have hτ := posDef_pinch P hP σ hσ
  have hL : ∀ a, Commute (qmlog (pinch P σ)) (P a) := fun a =>
    (pinch_commute P hP σ a).cfc_real Real.log
  rw [vN_eq_trace hτ.isHermitian, vN_eq_trace hσ.isHermitian, qrelEnt, Matrix.mul_sub,
    trace_sub, Complex.sub_re, ← trace_pinch_mul P hP σ _ hL]
  ring

/-- Commuting-pinching SSA for positive definite states, from `QIT.relEnt_jointlyConvex_of QIT.integralRep` and `QIT.relEnt_unitary_conj`. -/
theorem ssa_posDef (hJ : QIT_RelEntJointlyConvex) (hU : QIT_RelEntUnitaryInvariant)
    {α : Type} [Fintype α] [DecidableEq α] (m : ℕ) (P : Fin m → α → Matrix n n ℂ)
    (hP : ∀ k, IsProjFamily (P k))
    (hcomm : ∀ k l, k ≠ l → ∀ a b, P k a * P l b = P l b * P k a)
    (ρ : Matrix n n ℂ) (hρ : ρ.PosDef) :
    vN (pinchAll P ρ) + m * vN ρ ≤ ∑ k, vN (pinch (P k) ρ) + vN ρ :=
  ssa_telescope (fun X => X.PosDef) vN qrelEnt
    (fun Q hQ X hX => posDef_pinch Q hQ X hX)
    (fun Q hQ X Y hX hY => (qrelEnt_pinch_le hJ hU Q hQ).2 X Y hX hY)
    (fun Q hQ X hX => vN_pinch_gain Q hQ X hX) m P hP hcomm ρ hρ

end Houghton
