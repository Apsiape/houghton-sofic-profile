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
import FiniteLean.QIT.Entropy.SSABinary
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Interface to the relative-entropy library `QIT/` and monotonicity under pinchings

`qmlog`, `qrelEnt` are verbatim copies of `QIT.mlog`, `QIT.relEnt` (the equality of their bodies is proved by `rfl` in `FiniteLean.QIT.Entropy.Bridge`); `QIT_RelEntJointlyConvex` and `QIT_RelEntUnitaryInvariant`
are `QIT.relEnt_jointlyConvex_of QIT.integralRep` and `QIT.relEnt_unitary_conj`, packaged as `Prop`s.  From them we prove Step (3): relative entropy does not
increase under pinchings (via binary pinchings `X ↦ (X + RXR)/2`, `R = 1 - 2P`).
-/

namespace Houghton

open Finset Matrix
open scoped ComplexOrder

section Defs

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Copy of `QIT.mlog`. -/
noncomputable def qmlog (A : Matrix n n ℂ) : Matrix n n ℂ := cfc Real.log A

/-- Copy of `QIT.relEnt`. -/
noncomputable def qrelEnt (ρ σ : Matrix n n ℂ) : ℝ := (Matrix.trace (ρ * (qmlog ρ - qmlog σ))).re

end Defs

/-- `QIT.relEnt_jointlyConvex_of QIT.integralRep`. -/
def QIT_RelEntJointlyConvex : Prop :=
  ∀ {n : Type} [Fintype n] [DecidableEq n] {ρ₁ ρ₂ σ₁ σ₂ : Matrix n n ℂ} (_h₁ : ρ₁.PosDef)
    (_h₂ : ρ₂.PosDef) (_k₁ : σ₁.PosDef) (_k₂ : σ₂.PosDef) {t : ℝ} (_ht0 : 0 ≤ t) (_ht1 : t ≤ 1),
    qrelEnt (t • ρ₁ + (1 - t) • ρ₂) (t • σ₁ + (1 - t) • σ₂) ≤
      t * qrelEnt ρ₁ σ₁ + (1 - t) * qrelEnt ρ₂ σ₂

/-- `QIT.relEnt_unitary_conj`. -/
def QIT_RelEntUnitaryInvariant : Prop :=
  ∀ {n : Type} [Fintype n] [DecidableEq n] (U : Matrix.unitaryGroup n ℂ) {ρ σ : Matrix n n ℂ}
    (_hρ : ρ.PosDef) (_hσ : σ.PosDef),
    qrelEnt ((U : Matrix n n ℂ) * ρ * star (U : Matrix n n ℂ))
      ((U : Matrix n n ℂ) * σ * star (U : Matrix n n ℂ)) = qrelEnt ρ σ

section Mono

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The reflection `R = 1 - 2P` as a unitary. -/
noncomputable def reflU (P : Matrix n n ℂ) (hP : Pᴴ = P) (hPP : P * P = P) :
    Matrix.unitaryGroup n ℂ :=
  ⟨1 - (2 : ℂ) • P, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, reflection_herm P hP,
      reflection_sq P hPP]⟩

lemma reflU_coe (P : Matrix n n ℂ) (hP : Pᴴ = P) (hPP : P * P = P) :
    (reflU P hP hPP : Matrix n n ℂ) = 1 - (2 : ℂ) • P := rfl

lemma star_reflU (P : Matrix n n ℂ) (hP : Pᴴ = P) (hPP : P * P = P) :
    star (reflU P hP hPP : Matrix n n ℂ) = 1 - (2 : ℂ) • P := by
  rw [reflU_coe, Matrix.star_eq_conjTranspose, reflection_herm P hP]

lemma binPinch_eq_real_avg (P X : Matrix n n ℂ) (hPP : P * P = P) :
    binPinch P X = (1 / 2 : ℝ) • X + (1 - 1 / 2 : ℝ) • ((1 - (2 : ℂ) • P) * X * (1 - (2 : ℂ) • P)) := by
  rw [binPinch_eq_avg P X hPP, smul_add]
  congr 1
  · ext i j; simp [Complex.real_smul]
  · ext i j; simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]; norm_num

lemma posDef_refl_conj (P X : Matrix n n ℂ) (hP : Pᴴ = P) (hPP : P * P = P) (hX : X.PosDef) :
    ((1 - (2 : ℂ) • P) * X * (1 - (2 : ℂ) • P)).PosDef := by
  have h := hX.conjTranspose_mul_mul_same (B := 1 - (2 : ℂ) • P) (by
    intro v w hvw
    have := congrArg (fun u => (1 - (2 : ℂ) • P) *ᵥ u) hvw
    simp only [mulVec_mulVec, reflection_sq P hPP, one_mulVec] at this
    exact this)
  rwa [reflection_herm P hP] at h

lemma posDef_binPinch (P X : Matrix n n ℂ) (hP : Pᴴ = P) (hPP : P * P = P) (hX : X.PosDef) :
    (binPinch P X).PosDef := by
  rw [binPinch_eq_real_avg P X hPP]
  exact (hX.smul (by norm_num : (0 : ℝ) < 1 / 2)).add
    ((posDef_refl_conj P X hP hPP hX).smul (by norm_num : (0 : ℝ) < 1 - 1 / 2))

/-- Monotonicity of relative entropy under a binary pinching. -/
theorem qrelEnt_binPinch_le (hJ : QIT_RelEntJointlyConvex) (hU : QIT_RelEntUnitaryInvariant)
    (P : Matrix n n ℂ) (hP : Pᴴ = P) (hPP : P * P = P) (X Y : Matrix n n ℂ) (hX : X.PosDef)
    (hY : Y.PosDef) : qrelEnt (binPinch P X) (binPinch P Y) ≤ qrelEnt X Y := by
  rw [binPinch_eq_real_avg P X hPP, binPinch_eq_real_avg P Y hPP]
  refine (hJ hX (posDef_refl_conj P X hP hPP hX) hY (posDef_refl_conj P Y hP hPP hY)
    (by norm_num) (by norm_num)).trans (le_of_eq ?_)
  have hu := hU (reflU P hP hPP) hX hY
  rw [star_reflU, reflU_coe] at hu
  rw [hu]
  ring

/-- **Step (3)**: relative entropy does not increase under pinchings (and pinchings preserve
positive definiteness). -/
theorem qrelEnt_pinch_le (hJ : QIT_RelEntJointlyConvex) (hU : QIT_RelEntUnitaryInvariant)
    {α : Type} [Fintype α] [DecidableEq α] (P : α → Matrix n n ℂ) (hP : IsProjFamily P) :
    (∀ X : Matrix n n ℂ, X.PosDef → (pinch P X).PosDef) ∧
      ∀ X Y : Matrix n n ℂ, X.PosDef → Y.PosDef →
        qrelEnt (pinch P X) (pinch P Y) ≤ qrelEnt X Y :=
  mono_pinch_of_binary (fun X => X.PosDef) qrelEnt
    (fun P hP hPP X hX => posDef_binPinch P X hP hPP hX)
    (fun P hP hPP X Y hX hY => qrelEnt_binPinch_le hJ hU P hP hPP X Y hX hY) P hP

end Mono

end Houghton
