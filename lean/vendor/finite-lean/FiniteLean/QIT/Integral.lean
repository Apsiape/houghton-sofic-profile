import FiniteLean.QIT.Interfaces
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.Matrix.PosDef

/-!
# The integral representation `IntegralRep`

Scalar identity `p log p − p log q = ∫₀^∞ (p²/(q + s p) − p/(1 + s)) ds` (`p, q > 0`), and its
matrix version for commuting positive definite `L, R`, via the joint spectral projections
`E_{λμ} = P_λ Q_μ` (`P_λ = 1_{λ}(L)`, `Q_μ = 1_{μ}(R)` by the functional calculus).
-/

open scoped ComplexOrder
open MeasureTheory Set Filter Topology Finset Matrix

namespace QIT

/-- The scalar integrand. -/
noncomputable def sint (p q s : ℝ) : ℝ := p ^ 2 / (q + s * p) - p / (1 + s)

lemma sint_antideriv (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (s : ℝ) (hs : 0 ≤ s) :
    HasDerivAt (fun s => p * Real.log (q + s * p) - p * Real.log (1 + s)) (sint p q s) s := by
  have h1 : 0 < q + s * p := by positivity
  have h2 : 0 < 1 + s := by linarith
  have d1 : HasDerivAt (fun s => q + s * p) p s := by
    simpa using ((hasDerivAt_id s).mul_const p).const_add q
  have d2 : HasDerivAt (fun s => 1 + s) 1 s := by
    simpa using (hasDerivAt_id s).const_add 1
  have := ((d1.log h1.ne').const_mul p).sub ((d2.log h2.ne').const_mul p)
  convert this using 1
  unfold sint
  field_simp

lemma sint_tendsto (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    Tendsto (fun s => p * Real.log (q + s * p) - p * Real.log (1 + s)) atTop
      (𝓝 (p * Real.log p)) := by
  have hlim : Tendsto (fun s : ℝ => p + (q - p) / (1 + s)) atTop (𝓝 p) := by
    have : Tendsto (fun s : ℝ => (q - p) / (1 + s)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ 1 tendsto_id)
    simpa using this.const_add p
  have hlog := (hlim.log hp.ne').const_mul p
  refine hlog.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  have h1 : 0 < q + s * p := by positivity
  have h2 : 0 < 1 + s := by linarith
  have e : p + (q - p) / (1 + s) = (q + s * p) / (1 + s) := by field_simp; ring
  rw [e, Real.log_div h1.ne' h2.ne']
  ring

lemma sint_integrable (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    IntegrableOn (sint p q) (Ioi 0) := by
  have hd := fun s (hs : s ∈ Ioi (0 : ℝ)) => sint_antideriv p q hp hq s (le_of_lt hs)
  have hc : ContinuousWithinAt (fun s => p * Real.log (q + s * p) - p * Real.log (1 + s))
      (Ici 0) 0 := (sint_antideriv p q hp hq 0 le_rfl).continuousAt.continuousWithinAt
  have hform : ∀ s ∈ Ioi (0 : ℝ), sint p q s = p * (p - q) / ((q + s * p) * (1 + s)) := by
    intro s hs
    have h1 : 0 < q + s * p := by have := hs.out; positivity
    have h2 : 0 < 1 + s := by have := hs.out; linarith
    unfold sint
    rw [div_sub_div _ _ h1.ne' h2.ne']
    congr 1
    ring
  rcases le_total q p with hpq | hpq
  · refine integrableOn_Ioi_deriv_of_nonneg hc hd (fun s hs => ?_) (sint_tendsto p q hp hq)
    rw [hform s hs]
    have := hs.out
    apply div_nonneg (mul_nonneg hp.le (by linarith)) (by positivity)
  · refine integrableOn_Ioi_deriv_of_nonpos hc hd (fun s hs => ?_) (sint_tendsto p q hp hq)
    rw [hform s hs]
    have := hs.out
    apply div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hp.le (by linarith))
      (by positivity)

lemma sint_integral (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    ∫ s in Ioi (0 : ℝ), sint p q s = p * Real.log p - p * Real.log q := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto
    (sint_antideriv p q hp hq 0 le_rfl).continuousAt.continuousWithinAt
    (fun s hs => sint_antideriv p q hp hq s (le_of_lt hs)) (sint_integrable p q hp hq)
    (sint_tendsto p q hp hq)]
  simp

/-! ### Spectral projections -/

section Spectral

variable {m : Type} [Fintype m] [DecidableEq m]

/-- The (finite) real spectrum as a `Finset`. -/
noncomputable def spf (A : Matrix m m ℂ) : Finset ℝ := (Matrix.finite_real_spectrum (A := A)).toFinset

lemma mem_spf {A : Matrix m m ℂ} {a : ℝ} : a ∈ spf A ↔ a ∈ spectrum ℝ A :=
  Set.Finite.mem_toFinset _

lemma contSp (A : Matrix m m ℂ) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) :=
  (Matrix.finite_real_spectrum (A := A)).continuousOn f

/-- Indicator of a point. -/
noncomputable def ind (a : ℝ) : ℝ → ℝ := fun x => if x = a then 1 else 0

/-- Spectral projection `1_{a}(A)`. -/
noncomputable def sproj (A : Matrix m m ℂ) (a : ℝ) : Matrix m m ℂ := cfc (ind a) A

lemma cfc_expand (A : Matrix m m ℂ) (f : ℝ → ℝ) :
    cfc f A = ∑ a ∈ spf A, f a • sproj A a := by
  have h1 : cfc f A = cfc (∑ a ∈ spf A, fun x => f a * ind a x) A := by
    refine cfc_congr fun x hx => ?_
    simp only [Finset.sum_apply, ind, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq (spf A) x f, if_pos (mem_spf.mpr hx)]
  rw [h1, cfc_sum _ _ _ (fun a _ => contSp A _)]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact cfc_const_mul (f a) (ind a) A (contSp A _)

lemma sproj_mul (A : Matrix m m ℂ) (a b : ℝ) :
    sproj A a * sproj A b = if a = b then sproj A a else 0 := by
  unfold sproj
  rw [← cfc_mul (ind a) (ind b) A (contSp A _) (contSp A _)]
  split_ifs with h
  · subst h
    congr 1
    funext x
    unfold ind
    split_ifs <;> simp
  · have : (fun x => ind a x * ind b x) = (0 : ℝ → ℝ) := by
      funext x
      unfold ind
      by_cases ha : x = a
      · simp [ha, h]
      · simp [ha]
    rw [this, cfc_zero]

lemma sum_sproj (A : Matrix m m ℂ) (hA : IsSelfAdjoint A) : ∑ a ∈ spf A, sproj A a = 1 := by
  have h := cfc_expand A (fun _ => 1)
  rw [cfc_const_one ℝ A hA] at h
  rw [h]
  simp

lemma spf_pos {A : Matrix m m ℂ} (hA : A.PosDef) {a : ℝ} (ha : a ∈ spf A) : 0 < a := by
  rw [mem_spf, hA.isHermitian.spectrum_real_eq_range_eigenvalues] at ha
  obtain ⟨i, rfl⟩ := ha
  exact hA.eigenvalues_pos i

/-! ### Joint calculus of two commuting Hermitian matrices -/

variable (L R : Matrix m m ℂ)

/-- Joint spectral projections. -/
noncomputable def jE (a b : ℝ) : Matrix m m ℂ := sproj L a * sproj R b

/-- Joint functional calculus `J F = ∑ F(a, b) E_{ab}`. -/
noncomputable def jJ (F : ℝ → ℝ → ℝ) : Matrix m m ℂ :=
  ∑ a ∈ spf L, ∑ b ∈ spf R, F a b • jE L R a b

variable {L R}

lemma jE_mul (hLR : Commute L R) (a b a' b' : ℝ) :
    jE L R a b * jE L R a' b' = if a = a' then (if b = b' then jE L R a b else 0) else 0 := by
  have hc : Commute (sproj R b) (sproj L a') := by
    have h1 : Commute (sproj L a') R := hLR.cfc_real (ind a')
    exact (h1.symm.cfc_real (ind b))
  unfold jE
  calc sproj L a * sproj R b * (sproj L a' * sproj R b')
      = sproj L a * (sproj R b * sproj L a') * sproj R b' := by simp only [Matrix.mul_assoc]
    _ = sproj L a * (sproj L a' * sproj R b) * sproj R b' := by rw [hc.eq]
    _ = (sproj L a * sproj L a') * (sproj R b * sproj R b') := by simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [sproj_mul, sproj_mul]
        split_ifs <;> simp

lemma jJ_mul (hLR : Commute L R) (F G : ℝ → ℝ → ℝ) :
    jJ L R F * jJ L R G = jJ L R (fun a b => F a b * G a b) := by
  unfold jJ
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.mul_sum]
  simp only [Finset.mul_sum, smul_mul_smul_comm, jE_mul hLR, smul_ite, smul_zero]
  rw [Finset.sum_eq_single_of_mem a ha (fun x _ hx => Finset.sum_eq_zero fun y _ => by
    rw [if_neg (Ne.symm hx)])]
  rw [Finset.sum_eq_single_of_mem b hb (fun y _ hy => by rw [if_pos rfl, if_neg (Ne.symm hy)])]
  rw [if_pos rfl, if_pos rfl]

lemma jJ_congr (F G : ℝ → ℝ → ℝ) (h : ∀ a ∈ spf L, ∀ b ∈ spf R, F a b = G a b) :
    jJ L R F = jJ L R G := by
  unfold jJ
  exact Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => by rw [h a ha b hb]

lemma jJ_add (F G : ℝ → ℝ → ℝ) :
    jJ L R F + jJ L R G = jJ L R (fun a b => F a b + G a b) := by
  unfold jJ
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => (add_smul _ _ _).symm

lemma jJ_smul (r : ℝ) (F : ℝ → ℝ → ℝ) : r • jJ L R F = jJ L R (fun a b => r * F a b) := by
  unfold jJ
  simp only [Finset.smul_sum, smul_smul]

lemma jJ_sub (F G : ℝ → ℝ → ℝ) :
    jJ L R F - jJ L R G = jJ L R (fun a b => F a b - G a b) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ (jJ L R G), jJ_smul, jJ_add]
  congr 1
  funext a b
  ring

lemma jJ_left (hL : IsSelfAdjoint L) (hR : IsSelfAdjoint R) (f : ℝ → ℝ) :
    cfc f L = jJ L R (fun a _ => f a) := by
  rw [← Matrix.mul_one (cfc f L), ← sum_sproj R hR, cfc_expand L f, Finset.sum_mul]
  unfold jJ jE
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => smul_mul_assoc _ _ _

lemma jJ_right (hL : IsSelfAdjoint L) (hR : IsSelfAdjoint R) (g : ℝ → ℝ) :
    cfc g R = jJ L R (fun _ b => g b) := by
  rw [← Matrix.one_mul (cfc g R), ← sum_sproj L hL, cfc_expand R g, Finset.sum_mul]
  unfold jJ jE
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => mul_smul_comm _ _ _

lemma jJ_one (hL : IsSelfAdjoint L) (hR : IsSelfAdjoint R) : jJ L R (fun _ _ => 1) = 1 := by
  rw [← jJ_left hL hR (fun _ => 1), cfc_const_one ℝ L hL]

lemma qf_jJ (F : ℝ → ℝ → ℝ) (v : m → ℂ) :
    (dotProduct (star v) (Matrix.mulVec (jJ L R F) v)).re =
      ∑ a ∈ spf L, ∑ b ∈ spf R, F a b * (dotProduct (star v) (Matrix.mulVec (jE L R a b) v)).re := by
  unfold jJ
  rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, Complex.smul_re, smul_eq_mul]

end Spectral

/-- **The integral representation** (step J3 of joint convexity). -/
theorem integralRep : IntegralRep := by
  intro m _ _ L R hL hR hLR v
  have hLs : IsSelfAdjoint L := hL.isHermitian
  have hRs : IsSelfAdjoint R := hR.isHermitian
  set w : ℝ → ℝ → ℝ := fun a b => (dotProduct (star v) (Matrix.mulVec (jE L R a b) v)).re
  have hLJ : L = jJ L R (fun a _ => a) := by
    rw [← jJ_left hLs hRs (fun a => a), cfc_id' ℝ L hLs]
  have hRJ : R = jJ L R (fun _ b => b) := by
    rw [← jJ_right hLs hRs (fun b => b), cfc_id' ℝ R hRs]
  -- the integrand
  have hM : ∀ s ∈ Ioi (0 : ℝ), L * (R + (s : ℂ) • L)⁻¹ * L - ((1 + s)⁻¹ : ℂ) • L =
      jJ L R (fun a b => sint a b s) := by
    intro s hs
    have hs0 : 0 < s := hs
    have hsum : R + (s : ℂ) • L = jJ L R (fun a b => b + s * a) := by
      rw [Complex.coe_smul]
      have e : R + s • L = jJ L R (fun _ b => b) + s • jJ L R (fun a _ => a) :=
        congrArg₂ (· + ·) hRJ (congrArg (s • ·) hLJ)
      rw [e, jJ_smul, jJ_add]
    have hinv : (R + (s : ℂ) • L)⁻¹ = jJ L R (fun a b => (b + s * a)⁻¹) := by
      apply Matrix.inv_eq_right_inv
      rw [hsum, jJ_mul hLR, ← jJ_one hLs hRs]
      refine jJ_congr _ _ fun a ha b hb => ?_
      have := spf_pos hL ha
      have := spf_pos hR hb
      field_simp
    have h1 : ((1 + s)⁻¹ : ℂ) = (((1 + s)⁻¹ : ℝ) : ℂ) := by push_cast; ring
    rw [hinv, h1, Complex.coe_smul]
    have e : L * jJ L R (fun a b => (b + s * a)⁻¹) * L - (1 + s)⁻¹ • L =
        jJ L R (fun a _ => a) * jJ L R (fun a b => (b + s * a)⁻¹) * jJ L R (fun a _ => a) -
          (1 + s)⁻¹ • jJ L R (fun a _ => a) := by rw [← hLJ]
    rw [e, jJ_mul hLR, jJ_mul hLR, jJ_smul, jJ_sub]
    refine jJ_congr _ _ fun a _ b _ => ?_
    unfold sint
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hfun : EqOn
      (fun s : ℝ => (dotProduct (star v) (Matrix.mulVec
        (L * (R + (s : ℂ) • L)⁻¹ * L - ((1 + s)⁻¹ : ℂ) • L) v)).re)
      (fun s => ∑ a ∈ spf L, ∑ b ∈ spf R, sint a b s * w a b) (Ioi 0) := by
    intro s hs
    simp only
    rw [hM s hs, qf_jJ]
  have hint : IntegrableOn (fun s => ∑ a ∈ spf L, ∑ b ∈ spf R, sint a b s * w a b) (Ioi 0) := by
    refine integrable_finset_sum _ fun a ha => integrable_finset_sum _ fun b hb => ?_
    exact (sint_integrable a b (spf_pos hL ha) (spf_pos hR hb)).mul_const _
  refine ⟨hint.congr_fun hfun.symm measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hfun, integral_finset_sum _ (fun a ha =>
    integrable_finset_sum _ fun b hb =>
      (sint_integrable a b (spf_pos hL ha) (spf_pos hR hb)).mul_const _)]
  have hlhs : L * (mlog L - mlog R) = jJ L R (fun a b => a * (Real.log a - Real.log b)) := by
    rw [mlog, mlog, jJ_left hLs hRs Real.log, jJ_right hLs hRs Real.log, jJ_sub]
    have e : L * jJ L R (fun a b => Real.log a - Real.log b) =
        jJ L R (fun a _ => a) * jJ L R (fun a b => Real.log a - Real.log b) := by rw [← hLJ]
    rw [e, jJ_mul hLR]
  rw [hlhs, qf_jJ]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [integral_finset_sum _ (fun b hb =>
    (sint_integrable a b (spf_pos hL ha) (spf_pos hR hb)).mul_const _)]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [integral_mul_const, sint_integral a b (spf_pos hL ha) (spf_pos hR hb)]
  ring

end QIT
