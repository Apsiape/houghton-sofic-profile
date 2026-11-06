import FiniteLean.QIT.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# J2: Kronecker lift of the relative entropy

`liftL ρ = ρ ⊗ₖ 1` and `liftR σ = 1 ⊗ₖ σᵀ` commute, are positive definite for positive definite
`ρ, σ`, are real-linear, and `relEnt ρ σ = Re ⟪vecOne, liftL ρ (mlog (liftL ρ) - mlog (liftR σ))
vecOne⟫` (`relEnt_eq_qf`).
-/

namespace QIT

open Matrix
open scoped ComplexOrder Kronecker

variable {n : Type} [Fintype n] [DecidableEq n]

/-- `ρ ↦ ρ ⊗ₖ 1`. -/
noncomputable def liftL (ρ : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ := ρ ⊗ₖ (1 : Matrix n n ℂ)

/-- `σ ↦ 1 ⊗ₖ σᵀ`. -/
noncomputable def liftR (σ : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ := (1 : Matrix n n ℂ) ⊗ₖ σᵀ

/-- `vec 1`. -/
def vecOne : n × n → ℂ := fun p => if p.1 = p.2 then 1 else 0

/-- The real quadratic form `M ↦ Re ⟪v, M v⟫`. -/
def qf {m : Type} [Fintype m] (v : m → ℂ) (M : Matrix m m ℂ) : ℝ :=
  (dotProduct (star v) (Matrix.mulVec M v)).re

theorem qf_add {m : Type} [Fintype m] (v : m → ℂ) (M N : Matrix m m ℂ) :
    qf v (M + N) = qf v M + qf v N := by
  simp [qf, Matrix.add_mulVec, dotProduct_add]

theorem qf_sub {m : Type} [Fintype m] (v : m → ℂ) (M N : Matrix m m ℂ) :
    qf v (M - N) = qf v M - qf v N := by
  simp [qf, Matrix.sub_mulVec, dotProduct_sub]

theorem qf_smul {m : Type} [Fintype m] (v : m → ℂ) (c : ℝ) (M : Matrix m m ℂ) :
    qf v (c • M) = c * qf v M := by
  simp [qf, Matrix.smul_mulVec, dotProduct_smul]

theorem qf_nonneg {m : Type} [Fintype m] (v : m → ℂ) {M : Matrix m m ℂ} (hM : M.PosSemidef) :
    0 ≤ qf v M := by
  have h := hM.dotProduct_mulVec_nonneg v
  exact (Complex.le_def.1 h).1

omit [Fintype n] in
theorem liftL_combo (ρ₁ ρ₂ : Matrix n n ℂ) (t : ℝ) :
    liftL (t • ρ₁ + (1 - t) • ρ₂) = t • liftL ρ₁ + (1 - t) • liftL ρ₂ := by
  simp [liftL, add_kronecker, smul_kronecker]

omit [Fintype n] in
theorem liftR_combo (σ₁ σ₂ : Matrix n n ℂ) (t : ℝ) :
    liftR (t • σ₁ + (1 - t) • σ₂) = t • liftR σ₁ + (1 - t) • liftR σ₂ := by
  simp [liftR, kronecker_add, kronecker_smul, transpose_add, transpose_smul]

theorem liftL_posDef {ρ : Matrix n n ℂ} (h : ρ.PosDef) : (liftL ρ).PosDef :=
  h.kronecker PosDef.one

theorem liftR_posDef {σ : Matrix n n ℂ} (h : σ.PosDef) : (liftR σ).PosDef :=
  PosDef.one.kronecker h.transpose

theorem liftL_liftR_commute (ρ σ : Matrix n n ℂ) : Commute (liftL ρ) (liftR σ) := by
  unfold Commute SemiconjBy liftL liftR
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, Matrix.one_mul,
    Matrix.mul_one]

/-- `A ↦ A ⊗ₖ 1` as a star-algebra homomorphism. -/
noncomputable def kronOneHom : Matrix n n ℂ →⋆ₐ[ℂ] Matrix (n × n) (n × n) ℂ where
  toFun A := A ⊗ₖ (1 : Matrix n n ℂ)
  map_one' := one_kronecker_one
  map_mul' A B := by
    show (A * B) ⊗ₖ (1 : Matrix n n ℂ) = A ⊗ₖ (1 : Matrix n n ℂ) * B ⊗ₖ (1 : Matrix n n ℂ)
    rw [← mul_kronecker_mul, Matrix.mul_one]
  map_zero' := zero_kronecker _
  map_add' A B := add_kronecker _ _ _
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, smul_kronecker, one_kronecker_one]
  map_star' A := by
    simp only [star_eq_conjTranspose, conjTranspose_kronecker, conjTranspose_one]

/-- `A ↦ 1 ⊗ₖ A` as a star-algebra homomorphism. -/
noncomputable def oneKronHom : Matrix n n ℂ →⋆ₐ[ℂ] Matrix (n × n) (n × n) ℂ where
  toFun A := (1 : Matrix n n ℂ) ⊗ₖ A
  map_one' := one_kronecker_one
  map_mul' A B := by
    show (1 : Matrix n n ℂ) ⊗ₖ (A * B) = (1 : Matrix n n ℂ) ⊗ₖ A * (1 : Matrix n n ℂ) ⊗ₖ B
    rw [← mul_kronecker_mul, Matrix.mul_one]
  map_zero' := kronecker_zero _
  map_add' A B := kronecker_add _ _ _
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, kronecker_smul, one_kronecker_one]
  map_star' A := by
    simp only [star_eq_conjTranspose, conjTranspose_kronecker, conjTranspose_one]

/-- Entrywise complex conjugation as a real star-algebra homomorphism. -/
noncomputable def conjHom : Matrix n n ℂ →⋆ₐ[ℝ] Matrix n n ℂ where
  toFun A := A.map (starRingEnd ℂ)
  map_one' := by ext i j; simp [one_apply]
  map_mul' A B := by ext i j; simp [mul_apply, map_sum]
  map_zero' := by ext; simp
  map_add' A B := by ext; simp
  commutes' c := by
    ext i j
    simp only [Algebra.algebraMap_eq_smul_one, map_apply, Matrix.smul_apply, one_apply]
    by_cases h : i = j <;> simp [h]
  map_star' A := by ext i j; simp

theorem isSelfAdjoint_mlog (A : Matrix n n ℂ) : IsSelfAdjoint (mlog A) := by
  unfold mlog
  exact cfc_predicate _ _

theorem mlog_map {B : Matrix n n ℂ} (φ : Matrix n n ℂ →⋆ₐ[ℂ] Matrix (n × n) (n × n) ℂ)
    (hφ : Continuous φ) (hB : B.PosDef) : mlog (φ B) = φ (mlog B) := by
  have h := StarAlgHom.map_cfc φ Real.log B (continuousOn_log_spectrum hB) hφ hB.isHermitian
    ((hB.isHermitian.isSelfAdjoint).map φ)
  exact h.symm

theorem transpose_eq_conjHom {B : Matrix n n ℂ} (hB : B.IsHermitian) : Bᵀ = conjHom B := by
  ext i j
  have := congrFun (congrFun hB j) i
  simp only [conjTranspose_apply, RCLike.star_def] at this
  simp [conjHom, ← this]

theorem mlog_transpose {B : Matrix n n ℂ} (hB : B.PosDef) : mlog Bᵀ = conjHom (mlog B) := by
  rw [transpose_eq_conjHom hB.isHermitian]
  have hcont : Continuous (conjHom : Matrix n n ℂ →⋆ₐ[ℝ] Matrix n n ℂ) :=
    continuous_id.matrix_map Complex.continuous_conj
  have h := StarAlgHomClass.map_cfc (S := ℝ) (conjHom : Matrix n n ℂ →⋆ₐ[ℝ] Matrix n n ℂ)
    Real.log B (continuousOn_log_spectrum hB) hcont hB.isHermitian
    ((hB.isHermitian.isSelfAdjoint).map conjHom)
  exact h.symm

theorem qf_vecOne_kron (A C : Matrix n n ℂ) :
    dotProduct (star vecOne) (Matrix.mulVec (A ⊗ₖ C) vecOne) = ∑ i, ∑ k, A i k * C i k := by
  simp only [dotProduct, mulVec, vecOne, Fintype.sum_prod_type, kronecker_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp only [ite_true, star_one, one_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

theorem continuous_kronOneHom : Continuous (kronOneHom : Matrix n n ℂ →⋆ₐ[ℂ] _) :=
  LinearMap.continuous_of_finiteDimensional (kronOneHom : Matrix n n ℂ →⋆ₐ[ℂ] _).toLinearMap

theorem continuous_oneKronHom : Continuous (oneKronHom : Matrix n n ℂ →⋆ₐ[ℂ] _) :=
  LinearMap.continuous_of_finiteDimensional (oneKronHom : Matrix n n ℂ →⋆ₐ[ℂ] _).toLinearMap

/-- **J2.** `relEnt ρ σ = Re ⟪vec 1, L (log L - log R) vec 1⟫` with `L = ρ ⊗ₖ 1`,
`R = 1 ⊗ₖ σᵀ`. -/
theorem relEnt_eq_qf {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    relEnt ρ σ = qf vecOne (liftL ρ * (mlog (liftL ρ) - mlog (liftR σ))) := by
  have hL : mlog (liftL ρ) = mlog ρ ⊗ₖ (1 : Matrix n n ℂ) :=
    mlog_map kronOneHom continuous_kronOneHom hρ
  have hR : mlog (liftR σ) = (1 : Matrix n n ℂ) ⊗ₖ conjHom (mlog σ) := by
    rw [← mlog_transpose hσ]
    exact mlog_map oneKronHom continuous_oneKronHom hσ.transpose
  have hY : (mlog σ).IsHermitian := isSelfAdjoint_mlog σ
  rw [hL, hR, liftL, Matrix.mul_sub, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one,
    Matrix.one_mul, qf, Matrix.sub_mulVec, dotProduct_sub, qf_vecOne_kron, qf_vecOne_kron, relEnt,
    Matrix.mul_sub, trace_sub]
  congr 2
  · simp [trace, one_apply, Finset.sum_ite_eq]
  · simp only [trace, diag, mul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    have := congrFun (congrFun hY k) i
    simp only [conjTranspose_apply, RCLike.star_def] at this
    simp only [conjHom, StarAlgHom.coe_mk', AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk, map_apply]
    rw [this]
    simp [one_apply]

end QIT
