import Houghton.Analysis.SectorSpectral

/-!
# The single-twirl bound, reduced to a generic matrix inequality

In the Fourier picture the dephasing of label `i` is the twirl `σ = (1/3) ∑ₜ Zₜ ρ̂ Zₜ*` by the diagonal
unitaries `Zₜ = diag(ω^{t χᵢ})`, and `ρ̂ = P/D` with `P = YY*/9^N` a projection of trace `D`.
We prove that the weight moved out of `ran P` is `w ≤ 1/7500` (from the commutator hypotheses), and
reduce `SubTwirlEntropy` to the generic statement `GenTwirlBound`.
-/

universe u

namespace Houghton

open Finset Equiv Matrix ComplexConjugate

/-! ### Moving a permutation through ordered products -/

section Perm

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

lemma dH_comm_ofFn (z : Perm Ω) : ∀ {n : ℕ} (u : Fin n → Perm Ω),
    dH (z * (List.ofFn u).prod) ((List.ofFn u).prod * z) ≤ ∑ j, dH (z * u j) (u j * z)
  | 0, u => by
    rw [List.ofFn_zero, List.prod_nil, mul_one, one_mul, dH_self]
    exact sum_nonneg fun _ _ => dH_nonneg _ _
  | n + 1, u => by
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    have ih := dH_comm_ofFn z (fun j => u j.succ)
    set Q := (List.ofFn fun j => u j.succ).prod
    calc dH (z * (u 0 * Q)) (u 0 * Q * z)
        ≤ dH (z * (u 0 * Q)) (u 0 * z * Q) + dH (u 0 * z * Q) (u 0 * Q * z) := dH_triangle _ _ _
      _ = dH (z * u 0) (u 0 * z) + dH (z * Q) (Q * z) := by
          congr 1
          · rw [← mul_assoc, dH_mul_right]
          · rw [mul_assoc, mul_assoc, dH_mul_left]
      _ ≤ _ := add_le_add le_rfl ih

lemma ofFn_update_prod' (z : Perm Ω) : ∀ {n : ℕ} (h : Fin n → Perm Ω) (i : Fin n),
    ∃ L R : Perm Ω, (∀ a, (List.ofFn (Function.update h i a)).prod = L * a * R) ∧
      dH (z * R) (R * z) ≤ ∑ j, dH (z * h j) (h j * z)
  | 0, _, i => i.elim0
  | n + 1, h, i => by
    cases i using Fin.cases with
    | zero =>
      refine ⟨1, (List.ofFn fun j : Fin n => h j.succ).prod, fun a => ?_, ?_⟩
      · have e0 : (fun j : Fin n => Function.update h 0 a j.succ) = fun j => h j.succ :=
          funext fun j => Function.update_of_ne (Fin.succ_ne_zero j) _ _
        rw [List.ofFn_succ, List.prod_cons, Function.update_self, e0, one_mul]
      · rw [Fin.sum_univ_succ]
        exact (dH_comm_ofFn z _).trans (le_add_of_nonneg_left (dH_nonneg _ _))
    | succ i =>
      obtain ⟨L, R, hLR, hR⟩ := ofFn_update_prod' z (fun j : Fin n => h j.succ) i
      refine ⟨h 0 * L, R, fun a => ?_, ?_⟩
      · rw [List.ofFn_succ, List.prod_cons,
          Function.update_of_ne (Fin.succ_ne_zero i).symm]
        have e : (fun j : Fin n => Function.update h i.succ a j.succ) =
            Function.update (fun j => h j.succ) i a :=
          Function.update_comp_eq_of_injective h (Fin.succ_injective n) i a
        rw [e, hLR]
        simp only [mul_assoc]
      · rw [Fin.sum_univ_succ]
        exact hR.trans (le_add_of_nonneg_left (dH_nonneg _ _))

lemma dH_comm_pow_right (a b : Perm Ω) : ∀ k : ℕ,
    dH (a * b ^ k) (b ^ k * a) ≤ k * dH (a * b) (b * a)
  | 0 => by simp [dH_self]
  | k + 1 => by
    rw [pow_succ]
    calc dH (a * (b ^ k * b)) (b ^ k * b * a)
        ≤ dH (a * (b ^ k * b)) (b ^ k * a * b) + dH (b ^ k * a * b) (b ^ k * b * a) :=
          dH_triangle _ _ _
      _ = dH (a * b ^ k) (b ^ k * a) + dH (a * b) (b * a) := by
          congr 1
          · rw [← mul_assoc, dH_mul_right]
          · rw [mul_assoc, mul_assoc, dH_mul_left]
      _ ≤ k * dH (a * b) (b * a) + dH (a * b) (b * a) :=
          add_le_add (dH_comm_pow_right a b k) le_rfl
      _ = ((k + 1 : ℕ) : ℝ) * dH (a * b) (b * a) := by push_cast; ring

lemma dH_comm_pow_pow (a b : Perm Ω) (m k : ℕ) :
    dH (a ^ m * b ^ k) (b ^ k * a ^ m) ≤ m * k * dH (a * b) (b * a) := by
  have h1 : dH (a ^ m * b ^ k) (b ^ k * a ^ m) ≤ m * dH (a * b ^ k) (b ^ k * a) := by
    rw [dH_comm, dH_comm (a * b ^ k)]
    exact dH_comm_pow_right (b ^ k) a m
  have h2 := dH_comm_pow_right a b k
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  calc _ ≤ m * dH (a * b ^ k) (b ^ k * a) := h1
    _ ≤ m * (k * dH (a * b) (b * a)) := mul_le_mul_of_nonneg_left h2 hm
    _ = _ := by ring

variable {N : ℕ}

lemma fprod_shift_dH (c : Fin N → Perm Ω) (hc : ∀ i, c i ^ 3 = 1) (g : Fin N → Fin 3)
    (i : Fin N) (t : Fin 3) :
    dH (fprod c g * c i ^ t.val) (fprod c (g + Pi.single i t)) ≤
      4 * ∑ j ∈ univ.filter (· ≠ i), dH (c i * c j) (c j * c i) := by
  obtain ⟨L, R, hLR, hR⟩ := ofFn_update_prod' (c i ^ t.val) (fun j => c j ^ (g j).val) i
  have hf : ∀ a : Fin 3, fprod c (Function.update g i a) = L * c i ^ a.val * R := by
    intro a
    rw [← hLR]
    unfold fprod
    congr 2
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  have hg : fprod c g = L * c i ^ (g i).val * R := by
    rw [← hf]; congr; exact (Function.update_eq_self i g).symm
  rw [shift_eq_update, hf, hg, pow_val_add _ (hc i), mul_assoc L, mul_assoc L, mul_assoc L,
    dH_mul_left, mul_assoc, mul_assoc, dH_mul_left, dH_comm]
  refine hR.trans ?_
  rw [← add_sum_erase univ _ (mem_univ i), filter_ne', mul_sum]
  have hii : dH (c i ^ t.val * c i ^ (g i).val) (c i ^ (g i).val * c i ^ t.val) = 0 := by
    rw [← pow_add, ← pow_add, add_comm, dH_self]
  rw [hii, zero_add]
  refine sum_le_sum fun j _ => ?_
  refine (dH_comm_pow_pow (c i) (c j) t.val (g j).val).trans ?_
  have ht : (t.val : ℝ) ≤ 2 := by exact_mod_cast Nat.le_of_lt_succ t.isLt
  have hgj : ((g j).val : ℝ) ≤ 2 := by exact_mod_cast Nat.le_of_lt_succ (g j).isLt
  have h0 := dH_nonneg (c i * c j) (c j * c i)
  have : (t.val : ℝ) * (g j).val ≤ 4 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) t.val, Nat.cast_nonneg (α := ℝ) (g j).val]
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) t.val) (Nat.cast_nonneg (α := ℝ) (g j).val)]

end Perm

/-! ### The generic bound (remaining input) -/

/-- **Generic single-twirl entropy bound.** `σ = (P + Z₁PZ₁* + Z₂PZ₂*)/(3D)` is a uniform mixture of three
unitary conjugates of the normalized rank-`D` projection `P`; if the weight `1 - tr(Pσ)` it puts outside
`ran P` is at most `w ≤ 1/4`, then `S(σ) ≤ log D + h(w) + w log 2` (nats).  Proof sketch: pinching by
`{P, 1-P}` does not decrease entropy; the two blocks have weights `1-w₀, w₀` and ranks `≤ D` and
`≤ rank((1-P)(Z₁PZ₁* + Z₂PZ₂*)(1-P)) ≤ 2D`; `S(block) ≤ η(weight) + weight·log rank`; and
`h(x) + x log 2` increases on `[0, 1/2]`. -/
def GenTwirlBound : Prop :=
  ∀ (n : Type u) [Fintype n] [DecidableEq n] (P Z₁ Z₂ : Matrix n n ℂ) (D : ℕ) (w : ℝ),
    Pᴴ = P → P * P = P → P.trace = D → 0 < D →
    Z₁ * Z₁ᴴ = 1 → Z₂ * Z₂ᴴ = 1 →
    1 - (P * (((3 * D : ℕ) : ℂ)⁻¹ • (P + Z₁ * P * Z₁ᴴ + Z₂ * P * Z₂ᴴ))).trace.re ≤ w →
    w ≤ 1 / 4 →
    vN ((((3 * D : ℕ) : ℂ))⁻¹ • (P + Z₁ * P * Z₁ᴴ + Z₂ * P * Z₂ᴴ)) ≤
      Real.log D + ent w + ent (1 - w) + w * Real.log 2

/-! ### The twirl in the Fourier picture -/

section Mat

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω] {N : ℕ}

/-- The diagonal unitaries `Zₜ = diag(ω^{t χᵢ})`. -/
noncomputable def Zt (i : Fin N) (t : Fin 3) :
    Matrix ((Fin N → Fin 3) × Ω) ((Fin N → Fin 3) × Ω) ℂ :=
  diagonal fun p => ech (t * p.1 i)

/-- The projection `P = YY*/9^N` onto `ran ρ̂`. -/
noncomputable def Pproj (c : Fin N → Perm Ω) :
    Matrix ((Fin N → Fin 3) × Ω) ((Fin N → Fin 3) × Ω) ℂ :=
  ((9 : ℂ) ^ N)⁻¹ • (Ymat c * (Ymat c)ᴴ)

lemma ech_mul_star (s : Fin 3) : ech s * star (ech s) = 1 := by
  rw [show star (ech s) = conj (ech s) from rfl, conj_ech, ← ech_add, add_neg_cancel, ech_zero]

lemma Zt_unitary (i : Fin N) (t : Fin 3) : Zt (Ω := Ω) i t * (Zt i t)ᴴ = 1 := by
  rw [Zt, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext p
  exact ech_mul_star _

lemma Zt_zero (i : Fin N) : Zt (Ω := Ω) i 0 = 1 := by
  rw [Zt, ← diagonal_one]
  congr 1
  funext p
  simp [ech_zero]

lemma pinch_eq_twirl (i : Fin N) (X : Matrix ((Fin N → Fin 3) × Ω) ((Fin N → Fin 3) × Ω) ℂ) :
    pinch (labelProj i) X = (3 : ℂ)⁻¹ • ∑ t : Fin 3, Zt i t * X * (Zt i t)ᴴ := by
  ext p q
  rw [pinch_labelProj, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  simp only [Zt, diagonal_conjTranspose, mul_diagonal, diagonal_mul, Pi.star_apply]
  have e : ∀ t : Fin 3, ech (t * p.1 i) * X p q * star (ech (t * q.1 i)) =
      ech (t * (p.1 i - q.1 i)) * X p q := by
    intro t
    rw [show star (ech (t * q.1 i)) = conj (ech (t * q.1 i)) from rfl, conj_ech, mul_right_comm,
      ← ech_add, mul_sub, sub_eq_add_neg]
  simp only [e, ← sum_mul, sum_ech, sub_eq_zero]
  split_ifs <;> simp

lemma Pproj_herm (c : Fin N → Perm Ω) : (Pproj c)ᴴ = Pproj c := by
  rw [Pproj, conjTranspose_smul, conjTranspose_mul, conjTranspose_conjTranspose]
  congr 1
  simp

lemma YYYY (c : Fin N → Perm Ω) :
    Ymat c * (Ymat c)ᴴ * (Ymat c * (Ymat c)ᴴ) = ((9 : ℂ) ^ N) • (Ymat c * (Ymat c)ᴴ) := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Ymat c)ᴴ, YhY, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul]

lemma Pproj_idem (c : Fin N → Perm Ω) : Pproj c * Pproj c = Pproj c := by
  rw [Pproj, Matrix.smul_mul, Matrix.mul_smul, YYYY, smul_smul, smul_smul]
  congr 1
  field_simp

lemma Pproj_trace (c : Fin N → Perm Ω) : (Pproj c).trace = Fintype.card Ω := by
  rw [Pproj, trace_smul, Matrix.trace_mul_comm, YhY, trace_smul, trace_one, smul_eq_mul,
    smul_eq_mul]
  field_simp

lemma rhoSec_eq (c : Fin N → Perm Ω) (hD : 0 < Fintype.card Ω) :
    rhoSec c = ((Fintype.card Ω : ℂ))⁻¹ • Pproj c := by
  ext p q
  simp only [rhoSec, Pproj, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

lemma sigma_eq (c : Fin N → Perm Ω) (hD : 0 < Fintype.card Ω) (i : Fin N) :
    pinch (labelProj i) (rhoSec c) = (((3 * Fintype.card Ω : ℕ) : ℂ))⁻¹ •
      (Pproj c + Zt i 1 * Pproj c * (Zt i 1)ᴴ + Zt i 2 * Pproj c * (Zt i 2)ᴴ) := by
  rw [pinch_eq_twirl, rhoSec_eq c hD, Fin.sum_univ_three, Zt_zero]
  simp only [Matrix.mul_smul, Matrix.smul_mul, conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
    ← smul_add, smul_smul]
  congr 1
  push_cast
  rw [mul_inv]

/-- `G = Y* Zₜ Y`. -/
noncomputable def Gmat (c : Fin N → Perm Ω) (i : Fin N) (t : Fin 3) : Matrix Ω Ω ℂ :=
  (Ymat c)ᴴ * Zt i t * Ymat c

lemma trace_GG (G : Matrix Ω Ω ℂ) : (G * Gᴴ).trace = (nsq G : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, mul_apply, conjTranspose_apply, nsq, Complex.ofReal_sum]
  refine sum_congr rfl fun ω _ => sum_congr rfl fun ω' _ => ?_
  rw [show star (G ω ω') = conj (G ω ω') from rfl, Complex.mul_conj]

lemma trace_PZPZ (c : Fin N → Perm Ω) (Z : Matrix ((Fin N → Fin 3) × Ω) ((Fin N → Fin 3) × Ω) ℂ) :
    (Pproj c * (Z * Pproj c * Zᴴ)).trace =
      ((9 : ℂ) ^ N)⁻¹ * ((9 : ℂ) ^ N)⁻¹ * (nsq ((Ymat c)ᴴ * Z * Ymat c) : ℂ) := by
  have e : Pproj c * (Z * Pproj c * Zᴴ) = (((9 : ℂ) ^ N)⁻¹ * ((9 : ℂ) ^ N)⁻¹) •
      (Ymat c * (Ymat c)ᴴ * (Z * (Ymat c * (Ymat c)ᴴ) * Zᴴ)) := by
    simp only [Pproj, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [e, trace_smul, smul_eq_mul, ← trace_GG]
  congr 1
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (Ymat c)]
  simp only [Matrix.mul_assoc]

lemma G_term (c : Fin N → Perm Ω) (i : Fin N) (t : Fin 3) (ω ω' α : Ω) (χ : Fin N → Fin 3) :
    star (Msec c χ α ω) * ech (t * χ i) * Msec c χ α ω' =
        conj (∑ g, ech (-(dot χ g)) * pm (fprod c g) α ω) *
          ∑ h, ech (-(dot χ h)) * pm (fprod c (h + Pi.single i t)) α ω' := by
  have := FT_shift (fun g => pm (fprod c g)) χ i t α ω'
  simp only [FT] at this
  simp only [Msec, FT]
  rw [mul_assoc, this, starRingEnd_apply]
lemma G_inner (c : Fin N → Perm Ω) (i : Fin N) (t : Fin 3) (ω ω' α : Ω) :
    ∑ χ, star (Msec c χ α ω) * ech (t * χ i) * Msec c χ α ω' =
      3 ^ N * ∑ g, conj (pm (fprod c g) α ω) * pm (fprod c (g + Pi.single i t)) α ω' := by
  have e := Finset.sum_congr (s₁ := (univ : Finset (Fin N → Fin 3))) rfl
    (fun χ (_ : χ ∈ univ) => G_term c i t ω ω' α χ)
  rw [e]
  have p := parseval_scalar (fun g => pm (fprod c g) α ω)
    (fun g => pm (fprod c (g + Pi.single i t)) α ω')
  beta_reduce at p
  exact p
lemma G_apply (c : Fin N → Perm Ω) (i : Fin N) (t : Fin 3) (ω ω' : Ω) :
    Gmat c i t ω ω' =
      3 ^ N * ∑ g, if fprod c g ω = fprod c (g + Pi.single i t) ω' then (1 : ℂ) else 0 := by
  simp only [Gmat]
  rw [mul_apply]
  simp only [Zt, mul_diagonal, conjTranspose_apply, Ymat]
  rw [Fintype.sum_prod_type, sum_comm]
  dsimp only
  have e := Finset.sum_congr (s₁ := (univ : Finset Ω)) rfl
    (fun α (_ : α ∈ univ) => G_inner c i t ω ω' α)
  rw [e, ← mul_sum]
  congr 1
  rw [sum_comm]
  refine sum_congr rfl fun g _ => ?_
  simp only [pm, apply_ite conj, map_one, map_zero, ite_mul, one_mul, zero_mul]
  rw [sum_ite_eq']
  simp
lemma hip_pm_G (c : Fin N → Perm Ω) (i : Fin N) (t : Fin 3) (σ : Perm Ω) :
    hip (pm σ) (Gmat c i t) = ((3 ^ N * ∑ g, (Fintype.card Ω : ℝ) *
      (1 - dH (fprod c g * σ) (fprod c (g + Pi.single i t))) : ℝ) : ℂ) := by
  unfold hip
  rw [sum_comm]
  have e : ∀ ω', ∑ ω, conj (pm σ ω ω') * Gmat c i t ω ω' = Gmat c i t (σ ω') ω' := by
    intro ω'
    simp only [pm, apply_ite conj, map_one, map_zero, ite_mul, one_mul, zero_mul]
    rw [sum_ite_eq']
    simp
  have e' := Finset.sum_congr (s₁ := (univ : Finset Ω)) rfl (fun ω' (_ : ω' ∈ univ) => e ω')
  rw [e']
  have e2 := Finset.sum_congr (s₁ := (univ : Finset Ω)) rfl
    (fun ω' (_ : ω' ∈ univ) => G_apply c i t (σ ω') ω')
  rw [e2, ← mul_sum, sum_comm]
  have e3 : ∀ g, ∑ ω', (if fprod c g (σ ω') = fprod c (g + Pi.single i t) ω' then (1 : ℂ) else 0) =
      (((Fintype.card Ω : ℝ) * (1 - dH (fprod c g * σ) (fprod c (g + Pi.single i t))) : ℝ) : ℂ) := by
    intro g
    rw [← card_agree, sum_boole]
    push_cast
    rfl
  have e4 := Finset.sum_congr (s₁ := (univ : Finset (Fin N → Fin 3))) rfl
    (fun g (_ : g ∈ univ) => e3 g)
  rw [e4]
  push_cast
  rfl

lemma trace_PZPZ_ge (c : Fin N → Perm Ω) (hD : 0 < Fintype.card Ω) (i : Fin N) (t : Fin 3)
    (ε : ℝ) (hε : ∀ g, dH (fprod c g * c i ^ t.val) (fprod c (g + Pi.single i t)) ≤ ε)
    (hε1 : ε ≤ 1) :
    (Fintype.card Ω : ℝ) * (1 - ε) ^ 2 ≤
      (Pproj c * (Zt i t * Pproj c * (Zt i t)ᴴ)).trace.re := by
  set G := Gmat c i t with hG
  set D : ℝ := (Fintype.card Ω : ℝ) with hDdef
  have hDpos : 0 < D := by rw [hDdef]; exact_mod_cast hD
  rw [trace_PZPZ, show (Ymat c)ᴴ * Zt i t * Ymat c = G from rfl]
  have hre : ((((9 : ℂ) ^ N)⁻¹ * ((9 : ℂ) ^ N)⁻¹ * (nsq G : ℂ))).re =
      nsq G / ((9 : ℝ) ^ N * 9 ^ N) := by
    rw [show ((9 : ℂ) ^ N)⁻¹ * ((9 : ℂ) ^ N)⁻¹ * (nsq G : ℂ) =
      ((nsq G / ((9 : ℝ) ^ N * 9 ^ N) : ℝ) : ℂ) by push_cast; field_simp, Complex.ofReal_re]
  rw [hre]
  -- Cauchy–Schwarz against `P_{c^t}`
  have hcs := re_hip_le (pm (c i ^ t.val)) G
  have hnsq : nsq (pm (c i ^ t.val)) = D := by
    have h := hip_pm (c i ^ t.val) (c i ^ t.val)
    rw [hip_self, dH_self, sub_zero, mul_one] at h
    exact_mod_cast h
  rw [hnsq, hG, hip_pm_G, Complex.ofReal_re, ← hG] at hcs
  have hlow : 3 ^ N * ∑ _g : Fin N → Fin 3, D * (1 - ε) ≤
      3 ^ N * ∑ g, D * (1 - dH (fprod c g * c i ^ t.val) (fprod c (g + Pi.single i t))) :=
    mul_le_mul_of_nonneg_left (sum_le_sum fun g _ =>
      mul_le_mul_of_nonneg_left (by linarith [hε g]) hDpos.le) (by positivity)
  rw [sum_const, card_univ, card_G, nsmul_eq_mul] at hlow
  push_cast at hlow
  have h9 : (9 : ℝ) ^ N = 3 ^ N * 3 ^ N := by rw [← mul_pow]; norm_num
  have hX : 0 ≤ (9 : ℝ) ^ N * D * (1 - ε) := by
    have : 0 ≤ 1 - ε := by linarith
    positivity
  have key : (9 : ℝ) ^ N * D * (1 - ε) ≤ Real.sqrt D * Real.sqrt (nsq G) := by
    rw [h9]; nlinarith
  have hsq := mul_self_le_mul_self hX key
  have hsD : Real.sqrt D * Real.sqrt D = D := Real.mul_self_sqrt hDpos.le
  have hsG : Real.sqrt (nsq G) * Real.sqrt (nsq G) = nsq G := Real.mul_self_sqrt (nsq_nonneg _)
  have h81 : (0 : ℝ) < 9 ^ N * 9 ^ N := by positivity
  rw [le_div_iff₀ h81]
  have : (9 : ℝ) ^ N * D * (1 - ε) * ((9 : ℝ) ^ N * D * (1 - ε)) ≤ D * nsq G := by
    calc _ ≤ Real.sqrt D * Real.sqrt (nsq G) * (Real.sqrt D * Real.sqrt (nsq G)) := hsq
      _ = Real.sqrt D * Real.sqrt D * (Real.sqrt (nsq G) * Real.sqrt (nsq G)) := by ring
      _ = D * nsq G := by rw [hsD, hsG]
  nlinarith

lemma weight_bound (c : Fin N → Perm Ω) (hD : 0 < Fintype.card Ω) (i : Fin N) (ε : ℝ)
    (hε : ∀ t : Fin 3, ∀ g, dH (fprod c g * c i ^ t.val) (fprod c (g + Pi.single i t)) ≤ ε)
    (hε1 : ε ≤ 1) :
    1 - (Pproj c * ((((3 * Fintype.card Ω : ℕ) : ℂ))⁻¹ • (Pproj c + Zt i 1 * Pproj c * (Zt i 1)ᴴ +
      Zt i 2 * Pproj c * (Zt i 2)ᴴ))).trace.re ≤ 4 / 3 * ε := by
  have hDpos : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast hD
  have t1 := trace_PZPZ_ge c hD i 1 ε (hε 1) hε1
  have t2 := trace_PZPZ_ge c hD i 2 ε (hε 2) hε1
  set x := (Pproj c * (Zt i 1 * Pproj c * (Zt i 1)ᴴ)).trace.re
  set y := (Pproj c * (Zt i 2 * Pproj c * (Zt i 2)ᴴ)).trace.re
  have e : (Pproj c * ((((3 * Fintype.card Ω : ℕ) : ℂ))⁻¹ • (Pproj c + Zt i 1 * Pproj c * (Zt i 1)ᴴ +
      Zt i 2 * Pproj c * (Zt i 2)ᴴ))).trace.re =
      (3 * (Fintype.card Ω : ℝ))⁻¹ * ((Fintype.card Ω : ℝ) + x + y) := by
    rw [Matrix.mul_smul, trace_smul, Matrix.mul_add, Matrix.mul_add, trace_add, trace_add,
      Pproj_idem, Pproj_trace, smul_eq_mul,
      show (((3 * Fintype.card Ω : ℕ) : ℂ))⁻¹ = (((3 * (Fintype.card Ω : ℝ))⁻¹ : ℝ) : ℂ) by
        push_cast; ring, Complex.re_ofReal_mul]
    simp only [Complex.add_re, Complex.natCast_re]
    rfl
  rw [e]
  have hxy : 2 * (Fintype.card Ω : ℝ) * (1 - 2 * ε) ≤ x + y := by
    nlinarith [sq_nonneg ε]
  have key : (3 * (Fintype.card Ω : ℝ))⁻¹ * ((Fintype.card Ω : ℝ) + x + y) - (1 - 4 / 3 * ε) =
      (x + y - 2 * (Fintype.card Ω : ℝ) * (1 - 2 * ε)) / (3 * (Fintype.card Ω : ℝ)) := by
    field_simp
    ring
  have : 0 ≤ (x + y - 2 * (Fintype.card Ω : ℝ) * (1 - 2 * ε)) / (3 * (Fintype.card Ω : ℝ)) :=
    div_nonneg (by linarith) (by positivity)
  linarith

end Mat

lemma numeric_twirl : ent (1 / 7500) + ent (1 - 1 / 7500) + 1 / 7500 * Real.log 2 ≤ 1 / 200 := by
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have h1 : ent (1 / 7500) ≤ 13 / 7500 := by
    unfold ent
    have e : Real.log (1 / 7500) = -Real.log 7500 := by rw [one_div, Real.log_inv]
    rw [e]
    have h75 : Real.log 7500 ≤ 13 * Real.log 2 := by
      rw [show (13 : ℝ) * Real.log 2 = Real.log (2 ^ 13) by rw [Real.log_pow]; norm_num]
      exact Real.log_le_log (by norm_num) (by norm_num)
    nlinarith
  have h2 : ent (1 - 1 / 7500) ≤ 1 / 7500 := by
    unfold ent
    have hq : (0 : ℝ) < 1 - 1 / 7500 := by norm_num
    have hL := Real.log_le_sub_one_of_pos (inv_pos.mpr hq)
    rw [Real.log_inv] at hL
    have hm := mul_le_mul_of_nonneg_left hL hq.le
    have e : (1 - 1 / 7500 : ℝ) * ((1 - 1 / 7500)⁻¹ - 1) = 1 / 7500 := by norm_num
    nlinarith
  nlinarith

/-- `SubTwirlEntropy` from the generic bound. -/
theorem subTwirlEntropy_of_gen (hG : GenTwirlBound.{u}) : SubTwirlEntropy.{u} := by
  intro Ω _ _ N c x h1 h2 h3 h4 h5 h6 i
  have hD0 : Fintype.card Ω ≠ 0 := by
    intro h0
    have := h4 i
    rw [dH_eq, h0, Nat.cast_zero, div_zero] at this
    norm_num at this
  have hD := Nat.pos_of_ne_zero hD0
  have hε : ∀ t : Fin 3, ∀ g, dH (fprod c g * c i ^ t.val) (fprod c (g + Pi.single i t)) ≤
      1 / 10000 := by
    intro t g
    have := fprod_shift_dH c h1 g i t
    have := h5 i
    linarith
  have hw := weight_bound c hD i (1 / 10000) hε (by norm_num)
  rw [sigma_eq c hD i]
  have hb := hG ((Fin N → Fin 3) × Ω) (Pproj c) (Zt i 1) (Zt i 2) (Fintype.card Ω) (1 / 7500)
    (Pproj_herm c) (Pproj_idem c) (Pproj_trace c) hD (Zt_unitary i 1) (Zt_unitary i 2)
    (by linarith) (by norm_num)
  have hn := numeric_twirl
  linarith

/-- **Proposition `prop:dimension-perm`** from strong subadditivity for commuting pinchings and the
generic single-twirl bound. -/
theorem dimension_perm_of_QIT_gen (hQ : QIT_CommutingPinchingSSA.{u}) (hG : GenTwirlBound.{u})
    {Ω : Type u} [Fintype Ω] [DecidableEq Ω] (φ : F →* Equiv.Perm Ω) (δ : ℝ)
    (hrel : ∀ i, dH (φ (rel i)) 1 ≤ δ) (hγ : 1/2 ≤ dH (φ γ) 1) (N A : ℕ) (hN : 1 ≤ N)
    (hA' : AstarLE (3 * N) A) (hδ : (10:ℝ)^8 * N * max 1 A * δ ≤ 1) :
    (N : ℝ) / 16 ≤ Real.logb 2 (Fintype.card Ω) :=
  dimension_perm_of_QIT_twirl hQ (subTwirlEntropy_of_gen hG) φ δ hrel hγ N A hN hA' hδ

end Houghton
