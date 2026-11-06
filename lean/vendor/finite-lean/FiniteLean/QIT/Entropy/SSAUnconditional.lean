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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.SplitIfs
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.List.Induction
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.GroupTheory.Perm.ClosureSwap
import Mathlib.Algebra.Group.Subgroup.MulOpposite
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import FiniteLean.QIT.Entropy.SSAGain
import FiniteLean.QIT.Entropy.MatrixBounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

namespace Houghton

open Finset Matrix
open scoped ComplexOrder

variable {n : Type} [Fintype n] [DecidableEq n]

lemma spec_continuousOn (X : Matrix n n ℂ) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ X) :=
  (Matrix.finite_real_spectrum (A := X)).continuousOn f

lemma trace_cfc {X : Matrix n n ℂ} (hX : X.IsHermitian) (h : ℝ → ℝ) :
    (cfc h X).trace = ∑ i, ((h (hX.eigenvalues i) : ℝ) : ℂ) := by
  rw [hX.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul, trace_diagonal]
  rfl

/-- `vN(cfc g X) = ∑ η(g(λᵢ))` for Hermitian `X`. -/
lemma vN_cfc {X : Matrix n n ℂ} (hX : X.IsHermitian) (g : ℝ → ℝ) :
    vN (cfc g X) = ∑ i, ent (g (hX.eigenvalues i)) := by
  have hY : (cfc g X).IsHermitian := (cfc_predicate g X : IsSelfAdjoint (cfc g X))
  rw [vN_eq_trace hY, qmlog,
    ← cfc_comp' Real.log g X
      (((Matrix.finite_real_spectrum (A := X)).image g).continuousOn Real.log)
      (spec_continuousOn _ _),
    ← cfc_mul g (fun x => Real.log (g x)) X (spec_continuousOn _ _) (spec_continuousOn _ _),
    trace_cfc hX, Complex.re_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun i _ => ?_
  simp [ent]

/-- The affine path `(1-ε)X + (ε/d)·1` as a functional calculus. -/
lemma affine_eq_cfc {X : Matrix n n ℂ} (hX : X.IsHermitian) (s c : ℝ) :
    (s : ℂ) • X + (c : ℂ) • (1 : Matrix n n ℂ) = cfc (fun x => s * x + c) X := by
  have hsa : IsSelfAdjoint X := hX
  rw [cfc_add (a := X) (fun x => s * x) (fun _ => c), cfc_const_mul_id s X, cfc_const c X]
  rw [Algebra.algebraMap_eq_smul_one]
  ext i j
  simp [Complex.real_smul]

lemma pinch_one {α : Type} [Fintype α] [DecidableEq α] (P : α → Matrix n n ℂ)
    (hP : IsProjFamily P) : pinch P (1 : Matrix n n ℂ) = 1 := by
  simp only [pinch, Matrix.mul_one]
  rw [← hP.sum_one]
  refine sum_congr rfl fun a _ => ?_
  rw [hP.orth, if_pos rfl]

lemma pinch_affine {α : Type} [Fintype α] [DecidableEq α] (P : α → Matrix n n ℂ)
    (hP : IsProjFamily P) (X : Matrix n n ℂ) (s c : ℂ) :
    pinch P (s • X + c • 1) = s • pinch P X + c • 1 := by
  rw [pinch_add, pinch_smul, pinch_smul, pinch_one P hP]

lemma pinchAll_affine {α : Type} [Fintype α] [DecidableEq α] :
    ∀ {m : ℕ} (P : Fin m → α → Matrix n n ℂ), (∀ k, IsProjFamily (P k)) →
      ∀ (X : Matrix n n ℂ) (s c : ℂ), pinchAll P (s • X + c • 1) = s • pinchAll P X + c • 1
  | 0, _, _, _, _, _ => rfl
  | m + 1, P, hP, X, s, c => by
    simp only [pinchAll]
    rw [pinchAll_affine (fun k => P k.succ) (fun k => hP k.succ), pinch_affine (P 0) (hP 0)]

lemma pinch_herm {α : Type} [Fintype α] (P : α → Matrix n n ℂ) (hP : ∀ a, (P a)ᴴ = P a)
    (X : Matrix n n ℂ) (hX : X.IsHermitian) : (pinch P X).IsHermitian := by
  unfold IsHermitian pinch
  rw [conjTranspose_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [conjTranspose_mul, conjTranspose_mul, hP a, hX.eq, Matrix.mul_assoc]

lemma pinchAll_herm {α : Type} [Fintype α] :
    ∀ {m : ℕ} (P : Fin m → α → Matrix n n ℂ), (∀ k a, (P k a)ᴴ = P k a) →
      ∀ X : Matrix n n ℂ, X.IsHermitian → (pinchAll P X).IsHermitian
  | 0, _, _, X, hX => hX
  | m + 1, P, hP, X, hX => pinch_herm (P 0) (hP 0) _
      (pinchAll_herm (fun k => P k.succ) (fun k => hP k.succ) X hX)

lemma continuous_ent : Continuous ent := by
  have : ent = fun x => -(x * Real.log x) := rfl
  rw [this]
  exact Real.continuous_mul_log.neg

lemma vN_path {X : Matrix n n ℂ} (hX : X.IsHermitian) (d : ℝ) (ε : ℝ) :
    vN (((1 - ε : ℝ) : ℂ) • X + ((ε / d : ℝ) : ℂ) • (1 : Matrix n n ℂ)) =
      ∑ i, ent ((1 - ε) * hX.eigenvalues i + ε / d) := by
  rw [affine_eq_cfc hX, vN_cfc hX]

lemma continuous_vN_path {X : Matrix n n ℂ} (hX : X.IsHermitian) (d : ℝ) :
    Continuous fun ε : ℝ => ∑ i, ent ((1 - ε) * hX.eigenvalues i + ε / d) := by
  refine continuous_finset_sum _ fun i _ => continuous_ent.comp ?_
  fun_prop

/-- **Commuting-pinching SSA** from `QIT.relEnt_jointlyConvex_of QIT.integralRep` and `QIT.relEnt_unitary_conj` (joint convexity and unitary invariance of
the relative entropy). -/
theorem qit_commutingPinchingSSA_of (hJ : QIT_RelEntJointlyConvex)
    (hU : QIT_RelEntUnitaryInvariant) : QIT_CommutingPinchingSSA.{0} := by
  intro ι _ _ α _ _ m P hP hcomm ρ hρ
  obtain ⟨hρH, hρpsd, hρtr⟩ := hρ
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : ρ.trace = 0 := by simp [Matrix.trace]
    rw [this] at hρtr
    exact zero_ne_one hρtr
  set d : ℝ := (Fintype.card ι : ℝ) with hd
  have hdpos : 0 < d := by rw [hd]; exact_mod_cast Fintype.card_pos
  have hPH : ∀ k a, (P k a)ᴴ = P k a := fun k a => (hP k).herm a
  -- the path
  let path : ℝ → Matrix ι ι ℂ → Matrix ι ι ℂ := fun ε X =>
    ((1 - ε : ℝ) : ℂ) • X + ((ε / d : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)
  have hAll := pinchAll_herm P hPH ρ hρH
  have hK : ∀ k, (pinch (P k) ρ).IsHermitian := fun k => pinch_herm (P k) (hPH k) ρ hρH
  let F : ℝ → ℝ := fun ε =>
    (∑ i, ent ((1 - ε) * hAll.eigenvalues i + ε / d)) +
      m * (∑ i, ent ((1 - ε) * hρH.eigenvalues i + ε / d)) -
      (∑ k, ∑ i, ent ((1 - ε) * (hK k).eigenvalues i + ε / d)) -
      (∑ i, ent ((1 - ε) * hρH.eigenvalues i + ε / d))
  have hFc : Continuous F := by
    refine (((continuous_vN_path hAll d).add (continuous_const.mul
      (continuous_vN_path hρH d))).sub ?_).sub (continuous_vN_path hρH d)
    exact continuous_finset_sum _ fun k _ => continuous_vN_path (hK k) d
  -- `F ≤ 0` on `(0, 1)`
  have hFneg : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, F ε ≤ 0 := by
    intro ε hε
    have hpd : (path ε ρ).PosDef := by
      refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun v hv => ?_
      · unfold IsHermitian
        simp only [path, conjTranspose_add, conjTranspose_smul, conjTranspose_one, hρH.eq]
        congr 1 <;> congr 1 <;> simp
      · have h1 := hρpsd v
        have h2 : 0 < ∑ j, Complex.normSq (v j) := by
          by_contra hle
          push Not at hle
          exact hv (eq_zero_of_normSq_sum v hle)
        have e : star v ⬝ᵥ (path ε ρ *ᵥ v) =
            ((1 - ε : ℝ) : ℂ) * (star v ⬝ᵥ (ρ *ᵥ v)) + ((ε / d : ℝ) : ℂ) * (star v ⬝ᵥ v) := by
          simp only [path, add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul,
            smul_eq_mul]
        have hre : 0 < (star v ⬝ᵥ (path ε ρ *ᵥ v)).re := by
          rw [e, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, dot_star_self_re]
          have : 0 < ε / d * ∑ j, Complex.normSq (v j) := by
            have := div_pos hε.1 hdpos; positivity
          nlinarith [hε.2]
        have him : (star v ⬝ᵥ (path ε ρ *ᵥ v)).im = 0 := by
          rw [e, Complex.add_im, Complex.im_ofReal_mul, Complex.im_ofReal_mul]
          have h3 : (star v ⬝ᵥ v).im = 0 := by
            simp only [dotProduct, Complex.im_sum, Pi.star_apply]
            refine sum_eq_zero fun j _ => ?_
            rw [show star (v j) = (starRingEnd ℂ) (v j) from rfl, mul_comm, Complex.mul_conj,
              Complex.ofReal_im]
          have h4 : (star v ⬝ᵥ (ρ *ᵥ v)).im = 0 := by
            have := hρH.im_star_dotProduct_mulVec_self v
            simpa using this
          rw [h3, h4]; ring
        exact (Complex.lt_def).mpr ⟨by simpa using hre, by simpa using him.symm⟩
    have hs := ssa_posDef hJ hU m P hP hcomm (path ε ρ) hpd
    simp only [path] at hs
    rw [pinchAll_affine P hP] at hs
    simp only [pinch_affine (P _) (hP _)] at hs
    rw [vN_path hAll, vN_path hρH] at hs
    simp only [fun k => vN_path (hK k) d ε] at hs
    simp only [F]
    linarith
  -- pass to `ε = 0`
  have hcl : IsClosed {ε : ℝ | F ε ≤ 0} := isClosed_le hFc continuous_const
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ {ε : ℝ | F ε ≤ 0} := fun ε hε => hFneg ε hε
  have h0 : (0 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]; simp
  have hF0 : F 0 ≤ 0 := hcl.closure_subset_iff.mpr hsub h0
  have e0 : ∀ {X : Matrix ι ι ℂ} (hX : X.IsHermitian),
      ∑ i, ent ((1 - 0) * hX.eigenvalues i + 0 / d) = vN X := by
    intro X hX
    rw [vN_eq hX]
    simp
  simp only [F, e0 hAll, e0 hρH, e0 (hK _)] at hF0
  linarith


end Houghton
