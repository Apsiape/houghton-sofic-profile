import Houghton.Chunk
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Theorem 1.1 (lower bounds) and Corollary 1.2

The two analytic inputs use the following mathematical interfaces:

* `DimensionPermStatement` is Proposition `prop:dimension-perm` (`Houghton.dimension_perm`,
  specialised to `Ω : Type`);
* `AreaStatement` is Theorem `thm:area` (`Houghton.astar_le_pow`): `A*(M) ≤ M¹¹` for `M ≥ 2`;
* `WeightedAreaStatement` is Theorem `thm:area-weighted`: `A*(M) ≤ 135 M^{log₂ 107}` for `M ≥ 2`
  (areas are natural numbers, so this is `A*(M) ≤ ⌊135 M^{log₂ 107}⌋`).
-/

namespace Houghton

open Real

/-- Interface of Proposition `prop:dimension-perm` (for `Ω : Type`). -/
def DimensionPermStatement : Prop :=
  ∀ {Ω : Type} [Fintype Ω] [DecidableEq Ω] (φ : F →* Equiv.Perm Ω) (δ : ℝ),
    (∀ i, dH (φ (rel i)) 1 ≤ δ) → 1/2 ≤ dH (φ γ) 1 → ∀ (N A : ℕ), 1 ≤ N → AstarLE (3 * N) A →
      (10:ℝ)^8 * N * max 1 A * δ ≤ 1 → (N : ℝ) / 16 ≤ Real.logb 2 (Fintype.card Ω)

/-- Interface of Theorem `thm:area`. -/
def AreaStatement : Prop := ∀ M : ℕ, 2 ≤ M → AstarLE M (M ^ 11)

/-- Interface of Theorem `thm:area-weighted` (areas are integers, hence the floor). -/
def WeightedAreaStatement : Prop :=
  ∀ M : ℕ, 2 ≤ M → AstarLE M ⌊(135:ℝ) * (M:ℝ) ^ Real.logb 2 107⌋₊

/-- Statement of the upper bound in Theorem 1.1 (Proposition `prop:sofic-upper`):
`log₂ σ_{E_H}(r) = O(√r log r)`. Proved as `Houghton.soficUpper` (with `C = 7000`) in
`Houghton/Upper.lean`. -/
def SoficUpperStatement : Prop :=
  ∃ C : ℝ, ∀ r : ℝ, 2 ≤ r →
    ∃ n ∈ modelSizes E_H r, Real.logb 2 n ≤ C * r ^ ((1:ℝ) / 2) * Real.logb 2 r

/-- The degrees `n ≥ 1` admitting an `r⁻¹`-morphism `E_H → Sym_n` that separates `γ` from `1` by
`1 - r⁻¹`; every model size of `E_H` is one (`goodSize_of_mem`), and these are all that the proof
of the lower bound uses. -/
def GoodSize (r : ℝ) (n : ℕ) : Prop :=
  0 < n ∧ ∃ f : H3 → Equiv.Perm (Fin n), IsEpsMorphism E_H r⁻¹ f ∧
    1 - r⁻¹ ≤ dH (f (ρH' γ)) (f 1)

theorem goodSize_of_mem {r : ℝ} {n : ℕ} (hn : n ∈ modelSizes E_H r) : GoodSize r n := by
  obtain ⟨hn0, f, hf, he⟩ := hn
  exact ⟨hn0, f, hf, he (ρH' γ) rho'_γ_mem_E_H 1 one_mem_E_H rho'_γ_ne_one⟩

/-- The common step: a model of `E_H` gives an approximate representation to which
Proposition `prop:dimension-perm` applies. -/
theorem logb_ge_of_model (hdim : DimensionPermStatement) {r : ℝ} (hr : 10 ≤ r) {n : ℕ}
    (hn : GoodSize r n) (N A : ℕ) (hN : 1 ≤ N) (hA : AstarLE (3 * N) A)
    (hδ : (10:ℝ)^8 * N * max 1 A * (23 / r) ≤ 1) : (N : ℝ) / 16 ≤ Real.logb 2 n := by
  obtain ⟨_, f, hf, hsep⟩ := hn
  obtain ⟨hrel, hγ⟩ := transfer_of hf hsep
  have hγ' : 1/2 ≤ dH (phiOf f γ) 1 := by
    have : 5 / r ≤ 1/2 := by rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  have := hdim (phiOf f) (23 / r) hrel hγ' N A hN hA hδ
  simpa using this

/-- From `N/16 ≤ log₂ n` and `t < N/16` (or `t ≤ 0`) to `2^t ≤ n`. -/
theorem two_rpow_le_of_logb {n : ℕ} (hn : 0 < n) {t : ℝ} (h : t ≤ Real.logb 2 n) :
    (2:ℝ) ^ t ≤ n := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  calc (2:ℝ) ^ t ≤ 2 ^ Real.logb 2 n := Real.rpow_le_rpow_of_exponent_le (by norm_num) h
    _ = n := Real.rpow_logb (by norm_num) (by norm_num) hn'

theorem two_rpow_le_of_nonpos {n : ℕ} (hn : 0 < n) {t : ℝ} (h : t ≤ 0) : (2:ℝ) ^ t ≤ n := by
  have : (1:ℝ) ≤ n := by exact_mod_cast hn
  exact (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) h).trans this

/-- `((r/K)^(1/q))^q = r/K`. -/
theorem root_pow_eq {y q : ℝ} (hy : 0 ≤ y) (hq : 0 < q) : (y ^ (1 / q)) ^ q = y := by
  rw [one_div, Real.rpow_inv_rpow hy hq.ne']

/-! ### The unweighted bound `σ_{E_H}(r) ≥ 2^{r^{1/12}/270 - 1/16}` -/

/-- `K₁ = 23 · 10⁸ · 3¹¹`. -/
def K₁ : ℝ := 23 * 10 ^ 8 * 3 ^ 11

theorem K₁_pos : 0 < K₁ := by unfold K₁; norm_num

/-- `c = K₁^{-1/12}/16 ≥ 1/270`, i.e. `16 K₁^{1/12} ≤ 270`. -/
theorem K₁_root_le : K₁ ^ ((1:ℝ) / 12) ≤ 270 / 16 := by
  have h : K₁ ≤ (270 / 16 : ℝ) ^ (12:ℝ) := by
    rw [show (12:ℝ) = ((12:ℕ):ℝ) by norm_num, Real.rpow_natCast]; unfold K₁; norm_num
  calc K₁ ^ ((1:ℝ) / 12) ≤ ((270 / 16 : ℝ) ^ (12:ℝ)) ^ ((1:ℝ) / 12) :=
        Real.rpow_le_rpow K₁_pos.le h (by norm_num)
    _ = 270 / 16 := by
        rw [← Real.rpow_mul (by norm_num)]; norm_num

/-- The unweighted bound for every `GoodSize`. -/
theorem lower_bound_unweighted_of_good (hdim : DimensionPermStatement) (harea : AreaStatement)
    {r : ℝ} (hr : 2 ≤ r) {n : ℕ} (hn : GoodSize r n) :
    (2:ℝ) ^ (r ^ ((1:ℝ) / 12) / 270 - 1 / 16) ≤ n := by
  have hn0 : 0 < n := hn.1
  have hr0 : 0 ≤ r := by linarith
  set x := (r / K₁) ^ ((1:ℝ) / 12) with hxdef
  have hx0 : 0 ≤ x := Real.rpow_nonneg (div_nonneg hr0 K₁_pos.le) _
  have hxpow : x ^ (12:ℝ) = r / K₁ := root_pow_eq (div_nonneg hr0 K₁_pos.le) (by norm_num)
  set N := ⌊x⌋₊ with hNdef
  have hNx : (N:ℝ) ≤ x := Nat.floor_le hx0
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  -- `r^{1/12}/270 ≤ x/16`
  have hcmp : r ^ ((1:ℝ) / 12) / 270 ≤ x / 16 := by
    have hroot := K₁_root_le
    have hKpos : 0 < K₁ ^ ((1:ℝ) / 12) := Real.rpow_pos_of_pos K₁_pos _
    have hx' : x = r ^ ((1:ℝ) / 12) / K₁ ^ ((1:ℝ) / 12) := Real.div_rpow hr0 K₁_pos.le _
    rw [hx', div_div]
    apply div_le_div_of_nonneg_left (Real.rpow_nonneg hr0 _) (mul_pos hKpos (by norm_num))
    linarith
  rcases Nat.eq_zero_or_pos N with hN0 | hN1
  · -- `N = 0`: the exponent is negative.
    apply two_rpow_le_of_nonpos hn0
    rw [hN0] at hxN; push_cast at hxN
    linarith
  · -- `N ≥ 1`.
    have hN1' : (1:ℝ) ≤ N := by exact_mod_cast hN1
    have hx1 : 1 ≤ x := hN1'.trans hNx
    -- `K₁ N¹² ≤ r`
    have hN12 : (N:ℝ) ^ (12:ℕ) ≤ r / K₁ := by
      rw [← hxpow, ← Real.rpow_natCast, Nat.cast_ofNat]
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) hNx (by norm_num)
    have hKN : K₁ * (N:ℝ) ^ (12:ℕ) ≤ r := by
      rw [le_div_iff₀ K₁_pos] at hN12; linarith
    have hr10 : 10 ≤ r := by
      have : (1:ℝ) ≤ (N:ℝ) ^ (12:ℕ) := one_le_pow₀ hN1'
      have hK : (10:ℝ) ≤ K₁ := by unfold K₁; norm_num
      nlinarith [K₁_pos]
    have hA := harea (3 * N) (by omega)
    have hδ : (10:ℝ)^8 * N * max 1 ((3 * N) ^ 11 : ℕ) * (23 / r) ≤ 1 := by
      have hmax : max 1 ((3 * N) ^ 11) = (3 * N) ^ 11 :=
        max_eq_right (Nat.one_le_pow _ _ (by omega))
      rw [hmax]
      push_cast
      rw [mul_div_assoc', div_le_one (by linarith)]
      have : (10:ℝ) ^ 8 * N * (3 * N) ^ 11 * 23 = K₁ * (N:ℝ) ^ (12:ℕ) := by unfold K₁; ring
      linarith
    have hlog := logb_ge_of_model hdim hr10 hn N _ hN1 hA hδ
    apply two_rpow_le_of_logb hn0
    linarith

/-- **Theorem 1.1, unweighted lower bound** (for every model): if `r ≥ 2` and `E_H` admits a
`(1 - r⁻¹)`-expansive `r⁻¹`-morphism to `Sym_n`, then `n ≥ 2^{r^{1/12}/270 - 1/16}`. -/
theorem lower_bound_unweighted (hdim : DimensionPermStatement) (harea : AreaStatement)
    {r : ℝ} (hr : 2 ≤ r) {n : ℕ} (hn : n ∈ modelSizes E_H r) :
    (2:ℝ) ^ (r ^ ((1:ℝ) / 12) / 270 - 1 / 16) ≤ n :=
  lower_bound_unweighted_of_good hdim harea hr (goodSize_of_mem hn)

/-- **Theorem 1.1, unweighted, profile form**: `σ_{E_H}(r) ≥ 2^{r^{1/12}/270 - 1/16}` for `r ≥ 2`
(trivially true when `σ_{E_H}(r) = ⊤`). -/
theorem profile_lower_unweighted (hdim : DimensionPermStatement) (harea : AreaStatement)
    {r : ℝ} (hr : 2 ≤ r) :
    ∀ m : ℕ, profile E_H r = m → (2:ℝ) ^ (r ^ ((1:ℝ) / 12) / 270 - 1 / 16) ≤ m :=
  le_profile_of_forall fun _ hn => lower_bound_unweighted hdim harea hr hn

/-! ### Superpolynomial growth -/

/-- For `c > 0` and `0 < β ≤ 1`, `2^{c r^β - d}` eventually beats every `C r^k`. -/
theorem exists_two_rpow_gt (c d β C k R : ℝ) (hc : 0 < c) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    ∃ r : ℝ, R ≤ r ∧ 2 ≤ r ∧ C * r ^ k < (2:ℝ) ^ (c * r ^ β - d) := by
  set P : ℕ := ⌈k / β⌉₊
  set lam : ℝ := (2 + |d|) / c
  set D : ℝ := |C| * lam ^ P
  have hlog2' : Real.log 2 < 1 := by
    have h := Real.add_one_lt_exp (x := 1) one_ne_zero
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (by norm_num) (by linarith)
  have hlog2 : 1 / 2 < Real.log 2 := by
    have h := Real.add_one_lt_exp (x := -(1 / 2)) (by norm_num)
    have h2 : Real.exp (1 / 2) < 2 := by
      have : Real.exp (1 / 2) * Real.exp (-(1 / 2)) = 1 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos (1 / 2)]
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact h2
  have hlog2pos : 0 < Real.log 2 := by linarith
  have hlogne : Real.log 2 ≠ 0 := hlog2pos.ne'
  have hc' : c ≠ 0 := hc.ne'
  have ev := (Real.tendsto_exp_div_pow_atTop P).eventually (Filter.eventually_gt_atTop D)
  have ev2 := Filter.eventually_ge_atTop (max 1 (max (2 * c + |d|) (c * R + |d|)))
  obtain ⟨x, hx1, hx2⟩ := (ev.and ev2).exists
  have hx1' : 1 ≤ x := (le_max_left _ _).trans hx2
  have hx2' : 2 * c + |d| ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx2
  have hx3' : c * R + |d| ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx2
  have hxpos : 0 < x := by linarith
  set u : ℝ := (x / Real.log 2 + d) / c with hudef
  have hxl : x ≤ x / Real.log 2 := by
    rw [le_div_iff₀ hlog2pos]; nlinarith
  have hxl2 : x / Real.log 2 ≤ 2 * x := by
    rw [div_le_iff₀ hlog2pos]; nlinarith
  have hu2 : 2 ≤ u := by
    rw [hudef, le_div_iff₀ hc]
    have : -|d| ≤ d := neg_abs_le d
    linarith
  have huR : R ≤ u := by
    rw [hudef, le_div_iff₀ hc]
    have : -|d| ≤ d := neg_abs_le d
    linarith
  have hu0 : 0 ≤ u := by linarith
  have hu1 : 1 ≤ u := by linarith
  set r : ℝ := u ^ β⁻¹ with hrdef
  have hβinv : 1 ≤ β⁻¹ := one_le_inv_iff₀.mpr ⟨hβ0, hβ1⟩
  have hur : u ≤ r := by
    calc u = u ^ (1:ℝ) := (Real.rpow_one u).symm
      _ ≤ u ^ β⁻¹ := Real.rpow_le_rpow_of_exponent_le hu1 hβinv
  refine ⟨r, huR.trans hur, hu2.trans hur, ?_⟩
  have hrβ : r ^ β = u := Real.rpow_inv_rpow hu0 hβ0.ne'
  have hexp : c * r ^ β - d = x / Real.log 2 := by
    rw [hrβ, hudef, mul_div_assoc', mul_div_cancel_left₀ _ hc']; ring
  have h2x : (2:ℝ) ^ (c * r ^ β - d) = Real.exp x := by
    rw [hexp, Real.rpow_def_of_pos (by norm_num), mul_div_assoc', mul_div_cancel_left₀ _ hlogne]
  rw [h2x]
  -- `r^k ≤ u^P`
  have hrk : r ^ k ≤ u ^ P := by
    rw [hrdef, ← Real.rpow_mul hu0, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hu1
    have := Nat.le_ceil (k / β)
    rw [inv_mul_eq_div]; exact this
  have hulam : u ≤ lam * x := by
    rw [hudef, div_le_iff₀ hc]
    have hd : d ≤ |d| * x := by
      have : |d| ≤ |d| * x := le_mul_of_one_le_right (abs_nonneg d) hx1'
      linarith [le_abs_self d]
    have : lam * x * c = (2 + |d|) * x := by
      simp only [lam]; field_simp
    rw [this]; nlinarith
  have hupow : u ^ P ≤ lam ^ P * x ^ P := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hu0 hulam P
  have hCr : C * r ^ k ≤ |C| * (lam ^ P * x ^ P) := by
    have hrk0 : 0 ≤ r ^ k := Real.rpow_nonneg (by linarith) _
    calc C * r ^ k ≤ |C| * r ^ k := mul_le_mul_of_nonneg_right (le_abs_self C) hrk0
      _ ≤ |C| * u ^ P := mul_le_mul_of_nonneg_left hrk (abs_nonneg C)
      _ ≤ |C| * (lam ^ P * x ^ P) := mul_le_mul_of_nonneg_left hupow (abs_nonneg C)
  have hxP : 0 < x ^ P := pow_pos hxpos P
  have : D * x ^ P < Real.exp x := by
    have := hx1; rw [lt_div_iff₀ hxP] at this; exact this
  calc C * r ^ k ≤ |C| * (lam ^ P * x ^ P) := hCr
    _ = D * x ^ P := by simp only [D]; ring
    _ < Real.exp x := this

/-- **Corollary 1.2**: the profile of `E_H` is not bounded by any polynomial: for all `k, C` and
every `R` there is `r ≥ max 2 R` with `σ_{E_H}(r) > C r^k` (where `⊤ > C r^k`). -/
theorem not_polynomially_bounded' (hdim : DimensionPermStatement) (harea : AreaStatement) :
    ∀ k C R : ℝ, ∃ r : ℝ, R ≤ r ∧ 2 ≤ r ∧ ∀ m : ℕ, profile E_H r = m → C * r ^ k < m := by
  intro k C R
  obtain ⟨r, hR, hr, hlt⟩ := exists_two_rpow_gt (1 / 270) (1 / 16) (1 / 12) C k R
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨r, hR, hr, fun m hm => ?_⟩
  have := profile_lower_unweighted hdim harea hr m hm
  have e : (1:ℝ) / 270 * r ^ ((1:ℝ) / 12) - 1 / 16 = r ^ ((1:ℝ) / 12) / 270 - 1 / 16 := by ring
  rw [e] at hlt
  linarith

/-- **Corollary 1.2** (as stated in the task): for all `k, C` there is `r ≥ 2` with
`σ_{E_H}(r) > C r^k`. -/
theorem not_polynomially_bounded (hdim : DimensionPermStatement) (harea : AreaStatement) :
    ∀ k C : ℝ, ∃ r : ℝ, 2 ≤ r ∧ ∀ m : ℕ, profile E_H r = m → C * r ^ k < m := by
  intro k C
  obtain ⟨r, -, hr, h⟩ := not_polynomially_bounded' hdim harea k C 0
  exact ⟨r, hr, h⟩

/-- The lower bound in the paper's convention for products of permutations. -/
theorem lower_bound_unweighted_paper (hdim : DimensionPermStatement) (harea : AreaStatement)
    {r : ℝ} (hr : 2 ≤ r) {n : ℕ} (hn : n ∈ modelSizesPaper E_H r) :
    (2:ℝ) ^ (r ^ ((1:ℝ) / 12) / 270 - 1 / 16) ≤ n := by
  rw [modelSizesPaper_eq] at hn
  exact lower_bound_unweighted hdim harea hr hn

/-- `σ_{E_H}` is not bounded. -/
theorem not_bounded_E_H (hdim : DimensionPermStatement) (harea : AreaStatement) (C : ℕ)
    (hC : ∀ r : ℝ, 1 < r → profile E_H r ≤ C) : False := by
  obtain ⟨r, hr, hlt⟩ := not_polynomially_bounded hdim harea 0 C
  have hle := hC r (by linarith)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top C) hle)
  have h1 := hlt m hm.symm
  rw [← hm] at hle
  have h3 : (m : ℝ) ≤ C := by exact_mod_cast hle
  rw [Real.rpow_zero, mul_one] at h1
  linarith

/-- `E_H` does not embed in a finite group. -/
theorem not_embeds_E_H (hdim : DimensionPermStatement) (harea : AreaStatement) :
    ¬ EmbedsInFiniteGroup E_H := fun hE => by
  obtain ⟨C, hC⟩ := profile_le_of_embeds E_H hE
  exact not_bounded_E_H hdim harea C fun r hr => hC r (by linarith)

/-- Combined with Lemma `lem:floor`: `σ_{E_H}(r) ≥ 2r` for every `r > 1`. -/
theorem profile_ge_two_mul (hdim : DimensionPermStatement) (harea : AreaStatement) :
    ∀ r : ℝ, 1 < r → ∀ n : ℕ, profile E_H r = n → 2 * r ≤ n :=
  (profile_bounded_or_ge E_H).resolve_left fun ⟨C, hC⟩ => not_bounded_E_H hdim harea C hC

/-! ### The weighted bound `σ_{E_H}(r) ≥ 2^{r^{1/(log₂107+1)}/1280 - 1/16}` -/

/-- `p = log₂ 107`. -/
noncomputable def pW : ℝ := Real.logb 2 107

set_option exponentiation.threshold 1000 in
theorem pW_ge : (673:ℝ) / 100 ≤ pW := by
  unfold pW
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]
  have h : (2:ℝ) ^ (673:ℕ) ≤ (107:ℝ) ^ (100:ℕ) := by
    exact_mod_cast (show (2:ℕ) ^ 673 ≤ 107 ^ 100 by decide)
  calc (2:ℝ) ^ ((673:ℝ) / 100) = ((2:ℝ) ^ ((673:ℕ):ℝ)) ^ ((1:ℝ) / 100) := by
        rw [← Real.rpow_mul (by norm_num)]; norm_num
    _ = ((2:ℝ) ^ (673:ℕ)) ^ ((1:ℝ) / 100) := by rw [Real.rpow_natCast]
    _ ≤ ((107:ℝ) ^ (100:ℕ)) ^ ((1:ℝ) / 100) := Real.rpow_le_rpow (by positivity) h (by norm_num)
    _ = 107 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num

theorem pW_pos : 0 < pW := lt_of_lt_of_le (by norm_num) pW_ge

/-- `K₂ = 23 · 10⁸ · 135 · 3^{log₂ 107}`. -/
noncomputable def K₂ : ℝ := 23 * 10 ^ 8 * 135 * (3:ℝ) ^ pW

theorem K₂_pos : 0 < K₂ := by unfold K₂; positivity

set_option exponentiation.threshold 1000 in
/-- `K₂ ≤ 80^{p+1}`, i.e. `c_S = K₂^{-1/(p+1)}/16 ≥ 1/1280`. -/
theorem K₂_le : K₂ ≤ (80:ℝ) ^ (pW + 1) := by
  have h1 : (3881250000:ℝ) ≤ (80 / 3 : ℝ) ^ ((673:ℝ) / 100) := by
    have h : (3881250000:ℝ) ^ (100:ℕ) ≤ (80 / 3 : ℝ) ^ (673:ℕ) := by
      rw [div_pow, le_div_iff₀ (by positivity)]
      exact_mod_cast (show (3881250000:ℕ) ^ 100 * 3 ^ 673 ≤ 80 ^ 673 by decide)
    calc (3881250000:ℝ) = ((3881250000:ℝ) ^ (100:ℕ)) ^ ((1:ℝ) / 100) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ ((80 / 3 : ℝ) ^ (673:ℕ)) ^ ((1:ℝ) / 100) :=
          Real.rpow_le_rpow (by positivity) h (by norm_num)
      _ = (80 / 3 : ℝ) ^ ((673:ℝ) / 100) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have h2 : (80 / 3 : ℝ) ^ ((673:ℝ) / 100) ≤ (80 / 3 : ℝ) ^ pW :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) pW_ge
  have h3 : (80:ℝ) ^ pW = (80 / 3 : ℝ) ^ pW * (3:ℝ) ^ pW := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  have h3pos : 0 < (3:ℝ) ^ pW := by positivity
  have h4 : (3881250000:ℝ) ≤ (80 / 3 : ℝ) ^ pW := h1.trans h2
  have h5 := mul_le_mul_of_nonneg_right h4 h3pos.le
  rw [Real.rpow_add_one (by norm_num), h3]
  unfold K₂
  nlinarith

theorem K₂_root_le : K₂ ^ (1 / (pW + 1)) ≤ 80 := by
  have hq : 0 < pW + 1 := by linarith [pW_pos]
  calc K₂ ^ (1 / (pW + 1)) ≤ ((80:ℝ) ^ (pW + 1)) ^ (1 / (pW + 1)) :=
        Real.rpow_le_rpow K₂_pos.le K₂_le (by positivity)
    _ = 80 := by rw [one_div, Real.rpow_rpow_inv (by norm_num) hq.ne']

/-- The weighted bound for every `GoodSize`. -/
theorem lower_bound_weighted_of_good (hdim : DimensionPermStatement)
    (harea : WeightedAreaStatement) {r : ℝ} (hr : 2 ≤ r) {n : ℕ} (hn : GoodSize r n) :
    (2:ℝ) ^ (r ^ (1 / (Real.logb 2 107 + 1)) / 1280 - 1 / 16) ≤ n := by
  have hn0 : 0 < n := hn.1
  have hr0 : 0 ≤ r := by linarith
  change (2:ℝ) ^ (r ^ (1 / (pW + 1)) / 1280 - 1 / 16) ≤ n
  have hq : 0 < pW + 1 := by linarith [pW_pos]
  set x := (r / K₂) ^ (1 / (pW + 1)) with hxdef
  have hx0 : 0 ≤ x := Real.rpow_nonneg (div_nonneg hr0 K₂_pos.le) _
  have hxpow : x ^ (pW + 1) = r / K₂ := root_pow_eq (div_nonneg hr0 K₂_pos.le) hq
  set N := ⌊x⌋₊ with hNdef
  have hNx : (N:ℝ) ≤ x := Nat.floor_le hx0
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hcmp : r ^ (1 / (pW + 1)) / 1280 ≤ x / 16 := by
    have hroot := K₂_root_le
    have hKpos : 0 < K₂ ^ (1 / (pW + 1)) := Real.rpow_pos_of_pos K₂_pos _
    have hx' : x = r ^ (1 / (pW + 1)) / K₂ ^ (1 / (pW + 1)) := Real.div_rpow hr0 K₂_pos.le _
    rw [hx', div_div]
    apply div_le_div_of_nonneg_left (Real.rpow_nonneg hr0 _) (mul_pos hKpos (by norm_num))
    linarith
  rcases Nat.eq_zero_or_pos N with hN0 | hN1
  · apply two_rpow_le_of_nonpos hn0
    rw [hN0] at hxN; push_cast at hxN
    linarith
  · have hN1' : (1:ℝ) ≤ N := by exact_mod_cast hN1
    have hNpos : (0:ℝ) < N := by linarith
    have hNq : (N:ℝ) ^ (pW + 1) ≤ r / K₂ := by
      rw [← hxpow]; exact Real.rpow_le_rpow (Nat.cast_nonneg _) hNx hq.le
    have hKN : K₂ * (N:ℝ) ^ (pW + 1) ≤ r := by
      rw [le_div_iff₀ K₂_pos] at hNq; linarith
    have hNq1 : (1:ℝ) ≤ (N:ℝ) ^ (pW + 1) := Real.one_le_rpow hN1' hq.le
    have hK10 : (10:ℝ) ≤ K₂ := by
      unfold K₂
      have : (1:ℝ) ≤ (3:ℝ) ^ pW := Real.one_le_rpow (by norm_num) pW_pos.le
      nlinarith
    have hr10 : 10 ≤ r := by nlinarith [K₂_pos]
    have hA := harea (3 * N) (by omega)
    set A := ⌊(135:ℝ) * ((3 * N : ℕ) : ℝ) ^ Real.logb 2 107⌋₊ with hAdef
    have hAle : ((max 1 A : ℕ) : ℝ) ≤ 135 * (3 * (N:ℝ)) ^ pW := by
      have hB1 : (1:ℝ) ≤ 135 * (3 * (N:ℝ)) ^ pW := by
        have : (1:ℝ) ≤ (3 * (N:ℝ)) ^ pW := Real.one_le_rpow (by linarith) pW_pos.le
        linarith
      have hAB : (A:ℝ) ≤ 135 * (3 * (N:ℝ)) ^ pW := by
        have := Nat.floor_le (a := (135:ℝ) * ((3 * N : ℕ) : ℝ) ^ Real.logb 2 107)
          (by positivity)
        rw [← hAdef] at this
        push_cast at this
        exact this
      rcases le_total 1 A with h | h
      · rw [max_eq_right h]; exact hAB
      · rw [max_eq_left h]; push_cast; exact hB1
    have hδ : (10:ℝ)^8 * N * max 1 A * (23 / r) ≤ 1 := by
      have hsplit : (3 * (N:ℝ)) ^ pW = (3:ℝ) ^ pW * (N:ℝ) ^ pW :=
        Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
      have hNp : (N:ℝ) * (N:ℝ) ^ pW = (N:ℝ) ^ (pW + 1) := by
        rw [Real.rpow_add_one hNpos.ne']; ring
      have hbound : (10:ℝ)^8 * N * (135 * (3 * (N:ℝ)) ^ pW) * 23 = K₂ * (N:ℝ) ^ (pW + 1) := by
        rw [hsplit, ← hNp]; unfold K₂; ring
      have hrpos : 0 < r := by linarith
      rw [mul_div_assoc', div_le_one hrpos]
      have hmono : (10:ℝ)^8 * N * max 1 A * 23 ≤ (10:ℝ)^8 * N * (135 * (3 * (N:ℝ)) ^ pW) * 23 := by
        have hNn : (0:ℝ) ≤ (10:ℝ)^8 * N := by positivity
        have := mul_le_mul_of_nonneg_left hAle hNn
        push_cast at this ⊢
        linarith
      linarith
    have hlog := logb_ge_of_model hdim hr10 hn N A hN1 hA hδ
    apply two_rpow_le_of_logb hn0
    linarith

/-- **Theorem 1.1, weighted lower bound** (for every model): if `r ≥ 2` and `E_H` admits a
`(1 - r⁻¹)`-expansive `r⁻¹`-morphism to `Sym_n`, then
`n ≥ 2^{r^{1/(log₂107+1)}/1280 - 1/16}`. -/
theorem lower_bound_weighted (hdim : DimensionPermStatement) (harea : WeightedAreaStatement)
    {r : ℝ} (hr : 2 ≤ r) {n : ℕ} (hn : n ∈ modelSizes E_H r) :
    (2:ℝ) ^ (r ^ (1 / (Real.logb 2 107 + 1)) / 1280 - 1 / 16) ≤ n :=
  lower_bound_weighted_of_good hdim harea hr (goodSize_of_mem hn)

/-- **Theorem 1.1, weighted, profile form**. -/
theorem profile_lower_weighted (hdim : DimensionPermStatement) (harea : WeightedAreaStatement)
    {r : ℝ} (hr : 2 ≤ r) :
    ∀ m : ℕ, profile E_H r = m →
      (2:ℝ) ^ (r ^ (1 / (Real.logb 2 107 + 1)) / 1280 - 1 / 16) ≤ m :=
  le_profile_of_forall fun _ hn => lower_bound_weighted hdim harea hr hn

end Houghton
