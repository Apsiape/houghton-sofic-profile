import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Matrix logarithm and Umegaki relative entropy

* `mlog A := cfc Real.log A` (Hermitian functional calculus on `Matrix n n ℂ`);
* `relEnt ρ σ := Re tr (ρ (log ρ - log σ))` (nats);
* `relEnt_unitary_conj`: invariance under simultaneous unitary conjugation.
-/

namespace QIT

open Matrix
open scoped ComplexOrder

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Matrix logarithm via the Hermitian functional calculus. -/
noncomputable def mlog (A : Matrix n n ℂ) : Matrix n n ℂ := cfc Real.log A

/-- Umegaki relative entropy (nats). -/
noncomputable def relEnt (ρ σ : Matrix n n ℂ) : ℝ := (Matrix.trace (ρ * (mlog ρ - mlog σ))).re

/-- `log` is continuous on the spectrum of a positive definite matrix. -/
theorem continuousOn_log_spectrum {A : Matrix n n ℂ} (hA : A.PosDef) :
    ContinuousOn Real.log (spectrum ℝ A) := by
  refine Real.continuousOn_log.mono fun x hx => ?_
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  rintro rfl
  exact (spectrum.zero_notMem_iff ℝ).2 hA.isUnit hx

/-- Conjugation by a unitary commutes with `mlog`. -/
theorem mlog_unitary_conj (U : Matrix.unitaryGroup n ℂ) {A : Matrix n n ℂ} (hA : A.PosDef) :
    mlog ((U : Matrix n n ℂ) * A * star (U : Matrix n n ℂ)) =
      (U : Matrix n n ℂ) * mlog A * star (U : Matrix n n ℂ) := by
  set φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U
  have hφ : ∀ x, φ x = (U : Matrix n n ℂ) * x * star (U : Matrix n n ℂ) := fun x => rfl
  have hcont : Continuous φ := by
    have : (φ : Matrix n n ℂ → Matrix n n ℂ) =
        fun x => (U : Matrix n n ℂ) * x * star (U : Matrix n n ℂ) := funext hφ
    rw [this]
    fun_prop
  have hsa : IsSelfAdjoint A := hA.isHermitian
  have hsa' : IsSelfAdjoint (φ A) := by
    rw [hφ]
    exact hsa.conjugate _
  have := StarAlgHomClass.map_cfc φ Real.log A
    (continuousOn_log_spectrum hA) hcont hsa hsa'
  simpa [mlog, hφ] using this.symm

/-- Unitary invariance of the relative entropy. -/
theorem relEnt_unitary_conj (U : Matrix.unitaryGroup n ℂ) {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef)
    (hσ : σ.PosDef) :
    relEnt ((U : Matrix n n ℂ) * ρ * star (U : Matrix n n ℂ))
      ((U : Matrix n n ℂ) * σ * star (U : Matrix n n ℂ)) = relEnt ρ σ := by
  set V : Matrix n n ℂ := (U : Matrix n n ℂ)
  have hVV : star V * V = 1 := Unitary.star_mul_self_of_mem U.2
  rw [relEnt, relEnt, mlog_unitary_conj U hρ, mlog_unitary_conj U hσ]
  have h : V * ρ * star V * (V * mlog ρ * star V - V * mlog σ * star V) =
      V * (ρ * (mlog ρ - mlog σ)) * star V := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star V) V, hVV, Matrix.one_mul, ← Matrix.mul_assoc (star V) V, hVV,
      Matrix.one_mul]
  rw [h, Matrix.trace_mul_cycle, hVV, Matrix.one_mul]

end QIT
