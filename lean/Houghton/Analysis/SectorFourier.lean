import Houghton.Analysis.SectorEntropy
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Defs

/-!
# The explicit sector distribution

For exact local actions `c_i³ = x_i² = 1`, `x_i c_i x_i = c_i⁻¹` on a finite set `Ω` (`D = |Ω|`),
let `f(g) = c_1^{g_1} ⋯ c_N^{g_N}` (`g ∈ (ℤ/3)^N`) and
`M_χ = ∑_g ω^{-χ·g} P_{f(g)}` (entrywise, `P_σ` the permutation matrix).  The sector distribution is
`p(χ) = ‖M_χ‖²_HS / (9^N D)`; in the paper's notation `M_χ / 3^N = Q_{1,χ_1} ⋯ Q_{N,χ_N}` is the
product of the spectral projections of the `c_i`, and `p` is the joint law of the labels of the
commuting shifts `C_i` in the state `ρ = VV*/D` (proof of Theorem `thm:phase-robust`).

Proved here, from the permutation hypotheses only (Fourier analysis on `(ℤ/3)^N`):
* `sum_pSec`: `∑ p = 1`;
* `marginal_pSec`: `Pr(Z_i ≠ 0) = (2/3) dH(c_i, 1)` (exactly);
* `bhatt_pSec`: `∑_χ √(p(χ) p(χ⁽ⁱ⁾)) ≥ 1 - 2 ∑_{j ≠ i} dH(x_i c_j, c_j x_i)`.
The remaining input is the entropy bound `PermSectorEntropy`.
-/

universe u

namespace Houghton

open Finset Equiv ComplexConjugate

/-! ### Cube roots of unity -/

/-- `ω = e^{2πi/3}`. -/
noncomputable def ω3 : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

lemma sqrt3_mul_self : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)

lemma ω3_mul_self : ω3 * ω3 = conj ω3 := by
  apply Complex.ext <;> simp [ω3, Complex.mul_re, Complex.mul_im] <;> nlinarith [sqrt3_mul_self]

lemma ω3_mul_conj : ω3 * conj ω3 = 1 := by
  apply Complex.ext <;> simp [ω3, Complex.mul_re, Complex.mul_im] <;> nlinarith [sqrt3_mul_self]

lemma conj_mul_ω3 : conj ω3 * ω3 = 1 := by rw [mul_comm, ω3_mul_conj]

lemma conj_ω3_mul_self : conj ω3 * conj ω3 = ω3 := by
  rw [← map_mul, ω3_mul_self, Complex.conj_conj]

lemma one_add_ω3 : 1 + ω3 + conj ω3 = 0 := by
  apply Complex.ext <;> simp [ω3] <;> ring

/-- The characters of `ℤ/3`: `ech t = ω^t`. -/
noncomputable def ech : Fin 3 → ℂ := ![1, ω3, conj ω3]

lemma ech_zero : ech 0 = 1 := rfl

lemma ech_add (s t : Fin 3) : ech (s + t) = ech s * ech t := by
  fin_cases s <;> fin_cases t <;>
    simp [ech, ω3_mul_self, ω3_mul_conj, conj_mul_ω3, conj_ω3_mul_self]

lemma conj_ech (t : Fin 3) : conj (ech t) = ech (-t) := by
  fin_cases t <;> simp [ech]

lemma sum_ech (t : Fin 3) : ∑ a : Fin 3, ech (a * t) = if t = 0 then 3 else 0 := by
  fin_cases t <;> simp [Fin.sum_univ_three, ech]
  · exact one_add_ω3
  · linear_combination one_add_ω3

lemma ech_sum {ι : Type*} (s : Finset ι) (f : ι → Fin 3) :
    ech (∑ i ∈ s, f i) = ∏ i ∈ s, ech (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ech_zero]
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, ech_add, ih]

/-! ### Characters of `(ℤ/3)^N` and Parseval -/

variable {N : ℕ}

/-- The pairing `χ · g`. -/
def dot (χ g : Fin N → Fin 3) : Fin 3 := ∑ j, χ j * g j

lemma sum_ech_dot (v : Fin N → Fin 3) :
    ∑ χ : Fin N → Fin 3, ech (dot χ v) = if v = 0 then (3 : ℂ) ^ N else 0 := by
  simp only [dot, ech_sum]
  rw [← Fintype.prod_sum (fun j (a : Fin 3) => ech (a * v j))]
  simp only [sum_ech]
  split_ifs with hv
  · simp [hv]
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
    simp only [Pi.zero_apply] at hj
    exact prod_eq_zero (mem_univ j) (by simp [hj])

lemma dot_sub (χ g h : Fin N → Fin 3) : dot χ (g - h) = dot χ g - dot χ h := by
  simp only [dot, Pi.sub_apply, mul_sub, sum_sub_distrib]

lemma dot_single (χ : Fin N → Fin 3) (i : Fin N) (k : Fin 3) :
    dot χ (Pi.single i k) = χ i * k := by
  simp [dot, Pi.single_apply, mul_ite]

lemma parseval_scalar (a b : (Fin N → Fin 3) → ℂ) :
    ∑ χ, conj (∑ g, ech (-(dot χ g)) * a g) * (∑ h, ech (-(dot χ h)) * b h) =
      3 ^ N * ∑ g, conj (a g) * b g := by
  have key : ∀ g h : Fin N → Fin 3,
      ∑ χ : Fin N → Fin 3, conj (ech (-(dot χ g))) * ech (-(dot χ h)) =
        if g = h then (3 : ℂ) ^ N else 0 := by
    intro g h
    have e : ∀ χ, conj (ech (-(dot χ g))) * ech (-(dot χ h)) = ech (dot χ (g - h)) := by
      intro χ
      rw [conj_ech, neg_neg, ← ech_add, dot_sub, sub_eq_add_neg]
    simp only [e, sum_ech_dot, sub_eq_zero]
  calc ∑ χ, conj (∑ g, ech (-(dot χ g)) * a g) * (∑ h, ech (-(dot χ h)) * b h)
      = ∑ χ, ∑ g, ∑ h, (conj (ech (-(dot χ g))) * ech (-(dot χ h))) * (conj (a g) * b h) := by
        refine sum_congr rfl (fun χ _ => ?_)
        rw [map_sum, sum_mul_sum]
        refine sum_congr rfl (fun g _ => sum_congr rfl (fun h _ => ?_))
        rw [map_mul]; ring
    _ = ∑ g, ∑ h, ∑ χ, (conj (ech (-(dot χ g))) * ech (-(dot χ h))) * (conj (a g) * b h) := by
        rw [sum_comm]; exact sum_congr rfl (fun g _ => sum_comm)
    _ = ∑ g, ∑ h, (if g = h then (3 : ℂ) ^ N else 0) * (conj (a g) * b h) := by
        refine sum_congr rfl (fun g _ => sum_congr rfl (fun h _ => ?_))
        rw [← sum_mul, key]
    _ = 3 ^ N * ∑ g, conj (a g) * b g := by
        rw [mul_sum]
        refine sum_congr rfl (fun g _ => ?_)
        simp [ite_mul]

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

/-- Entrywise Hilbert–Schmidt inner product. -/
noncomputable def hip (A B : Ω → Ω → ℂ) : ℂ := ∑ α, ∑ β, conj (A α β) * B α β

/-- Squared Hilbert–Schmidt norm. -/
noncomputable def nsq (A : Ω → Ω → ℂ) : ℝ := ∑ α, ∑ β, Complex.normSq (A α β)

/-- Fourier transform on `(ℤ/3)^N` of a matrix-valued function. -/
noncomputable def FT (A : (Fin N → Fin 3) → Ω → Ω → ℂ) (χ : Fin N → Fin 3) : Ω → Ω → ℂ :=
  fun α β => ∑ g, ech (-(dot χ g)) * A g α β

theorem parseval (A B : (Fin N → Fin 3) → Ω → Ω → ℂ) :
    ∑ χ, hip (FT A χ) (FT B χ) = 3 ^ N * ∑ g, hip (A g) (B g) := by
  have h1 : ∀ α β, ∑ χ : Fin N → Fin 3, conj (FT A χ α β) * FT B χ α β =
      3 ^ N * ∑ g, conj (A g α β) * B g α β :=
    fun α β => parseval_scalar (fun g => A g α β) (fun g => B g α β)
  simp only [hip]
  calc ∑ χ, ∑ α, ∑ β, conj (FT A χ α β) * FT B χ α β
      = ∑ α, ∑ β, ∑ χ, conj (FT A χ α β) * FT B χ α β := by
        rw [sum_comm]; exact sum_congr rfl (fun α _ => sum_comm)
    _ = ∑ α, ∑ β, 3 ^ N * ∑ g, conj (A g α β) * B g α β := by simp only [h1]
    _ = 3 ^ N * ∑ g, ∑ α, ∑ β, conj (A g α β) * B g α β := by
        simp only [← mul_sum]
        congr 1
        symm
        rw [sum_comm]; exact sum_congr rfl (fun α _ => sum_comm)

lemma hip_self (A : Ω → Ω → ℂ) : hip A A = (nsq A : ℂ) := by
  simp [hip, nsq, Complex.normSq_eq_conj_mul_self]

lemma nsq_nonneg (A : Ω → Ω → ℂ) : 0 ≤ nsq A :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => Complex.normSq_nonneg _

lemma re_hip_le (A B : Ω → Ω → ℂ) : (hip A B).re ≤ Real.sqrt (nsq A) * Real.sqrt (nsq B) := by
  have h1 : (hip A B).re ≤ ∑ p : Ω × Ω, ‖A p.1 p.2‖ * ‖B p.1 p.2‖ := by
    rw [hip, ← Fintype.sum_prod_type', Complex.re_sum]
    refine sum_le_sum fun p _ => (Complex.re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt univ (fun p : Ω × Ω => ‖A p.1 p.2‖)
    (fun p => ‖B p.1 p.2‖)
  have e : ∀ C : Ω → Ω → ℂ, ∑ p : Ω × Ω, ‖C p.1 p.2‖ ^ 2 = nsq C := by
    intro C
    rw [nsq, ← Fintype.sum_prod_type']
    exact sum_congr rfl fun p _ => (Complex.normSq_eq_norm_sq _).symm
  rw [e, e] at h2
  linarith

/-- Reindexing a matrix by a permutation on both sides (`X ↦ P_x⁻¹ X P_x`). -/
def rix (x : Perm Ω) (A : Ω → Ω → ℂ) : Ω → Ω → ℂ := fun α β => A (x α) (x β)

lemma nsq_rix (x : Perm Ω) (A : Ω → Ω → ℂ) : nsq (rix x A) = nsq A := by
  simp only [nsq, rix]
  calc ∑ α, ∑ β, Complex.normSq (A (x α) (x β)) = ∑ α, ∑ β, Complex.normSq (A (x α) β) :=
        sum_congr rfl fun α _ => Equiv.sum_comp x (fun β => Complex.normSq (A (x α) β))
    _ = ∑ α, ∑ β, Complex.normSq (A α β) :=
        Equiv.sum_comp x (fun α => ∑ β, Complex.normSq (A α β))

/-! ### Permutation matrices -/

/-- Entries of the permutation matrix `P_σ e_β = e_{σ β}`. -/
noncomputable def pm (σ : Perm Ω) : Ω → Ω → ℂ := fun α β => if α = σ β then 1 else 0

lemma card_agree (g h : Perm Ω) :
    ((univ.filter fun β => g β = h β).card : ℝ) = Fintype.card Ω * (1 - dH g h) := by
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset Ω))
    (fun β => g β = h β)
  rw [card_univ] at hsplit
  have hc' : hc g h = (univ.filter fun β => ¬ g β = h β).card := rfl
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h0 | hpos
  · have : (univ.filter fun β => g β = h β).card = 0 := by omega
    simp [this, h0]
  · rw [dH_eq, mul_sub, mul_one, mul_div_cancel₀ _ (by positivity), hc', ← hsplit]
    push_cast
    ring

lemma hip_pm_rix (σ τ y : Perm Ω) :
    hip (pm σ) (rix y (pm τ)) = ((Fintype.card Ω : ℝ) * (1 - dH (y * σ) (τ * y)) : ℝ) := by
  rw [← card_agree, hip, sum_comm]
  have e : ∀ β, ∑ α, conj (pm σ α β) * rix y (pm τ) α β =
      if (y * σ) β = (τ * y) β then 1 else 0 := by
    intro β
    rw [sum_eq_single (σ β)]
    · simp only [pm, rix, Perm.mul_apply, if_true, map_one, one_mul]
      exact if_congr Iff.rfl rfl rfl
    · intro α _ hα; simp [pm, hα]
    · simp
  simp only [e]
  rw [sum_boole]
  push_cast
  rfl

lemma hip_pm (σ τ : Perm Ω) :
    hip (pm σ) (pm τ) = ((Fintype.card Ω : ℝ) * (1 - dH σ τ) : ℝ) := by
  have := hip_pm_rix σ τ 1
  rwa [one_mul, mul_one, show rix 1 (pm τ) = pm τ from rfl] at this

/-! ### Ordered products -/

lemma ofFn_update_prod {M : Type*} [Monoid M] : ∀ {n : ℕ} (h : Fin n → M) (i : Fin n),
    ∃ L R : M, ∀ a : M, (List.ofFn (Function.update h i a)).prod = L * a * R
  | 0, _, i => i.elim0
  | n + 1, h, i => by
    cases i using Fin.cases with
    | zero =>
      refine ⟨1, (List.ofFn fun j : Fin n => h j.succ).prod, fun a => ?_⟩
      have e0 : (fun j : Fin n => Function.update h 0 a j.succ) = fun j => h j.succ :=
        funext fun j => Function.update_of_ne (Fin.succ_ne_zero j) _ _
      rw [List.ofFn_succ, List.prod_cons, Function.update_self, e0, one_mul]
    | succ i =>
      obtain ⟨L, R, hLR⟩ := ofFn_update_prod (fun j : Fin n => h j.succ) i
      refine ⟨h 0 * L, R, fun a => ?_⟩
      rw [List.ofFn_succ, List.prod_cons,
        Function.update_of_ne (Fin.succ_ne_zero i).symm]
      have e : (fun j : Fin n => Function.update h i.succ a j.succ) =
          Function.update (fun j => h j.succ) i a :=
        Function.update_comp_eq_of_injective h (Fin.succ_injective n) i a
      rw [e, hLR]
      simp only [mul_assoc]

lemma dH_ofFn_prod_le : ∀ {n : ℕ} (u v : Fin n → Perm Ω),
    dH (List.ofFn u).prod (List.ofFn v).prod ≤ ∑ j, dH (u j) (v j)
  | 0, u, v => by
    rw [List.ofFn_zero, List.ofFn_zero, List.prod_nil, dH_self, Finset.univ_eq_empty,
      Finset.sum_empty]
  | n + 1, u, v => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Fin.sum_univ_succ]
    exact (dH_mul_le _ _ _ _).trans (add_le_add le_rfl (dH_ofFn_prod_le _ _))

lemma conj_ofFn_prod (x : Perm Ω) (hx : x * x = 1) : ∀ {n : ℕ} (u : Fin n → Perm Ω),
    x * (List.ofFn u).prod * x = (List.ofFn fun j => x * u j * x).prod
  | 0, u => by simp [hx]
  | n + 1, u => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons,
      ← conj_ofFn_prod x hx (fun j => u j.succ)]
    calc x * (u 0 * (List.ofFn fun j => u j.succ).prod) * x
        = x * u 0 * 1 * (List.ofFn fun j => u j.succ).prod * x := by simp [mul_assoc]
      _ = x * u 0 * (x * x) * (List.ofFn fun j => u j.succ).prod * x := by rw [hx]
      _ = _ := by simp only [mul_assoc]

lemma conj_pow_inv (x c : Perm Ω) (hx : x * x = 1) : ∀ n : ℕ, (x * c * x) ^ n = x * c ^ n * x
  | 0 => by simp [hx]
  | n + 1 => by
    rw [pow_succ, conj_pow_inv x c hx n, pow_succ]
    calc x * c ^ n * x * (x * c * x) = x * c ^ n * (x * x) * c * x := by simp only [mul_assoc]
      _ = x * (c ^ n * c) * x := by rw [hx]; simp only [mul_one, mul_assoc]

/-- `f(g) = c_1^{g_1} ⋯ c_N^{g_N}`. -/
def fprod (c : Fin N → Perm Ω) (g : Fin N → Fin 3) : Perm Ω :=
  (List.ofFn fun j => c j ^ (g j).val).prod

lemma fprod_update (c : Fin N → Perm Ω) (g : Fin N → Fin 3) (i : Fin N) :
    ∃ L R : Perm Ω, ∀ a : Fin 3, fprod c (Function.update g i a) = L * c i ^ a.val * R := by
  obtain ⟨L, R, h⟩ := ofFn_update_prod (fun j => c j ^ (g j).val) i
  refine ⟨L, R, fun a => ?_⟩
  rw [← h]
  unfold fprod
  congr 2
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

lemma pow_mod3 (c : Perm Ω) (h : c ^ 3 = 1) (n : ℕ) : c ^ (n % 3) = c ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 3]
  rw [pow_add, pow_mul, h, one_pow, one_mul]

lemma pow_val_add (c : Perm Ω) (h : c ^ 3 = 1) (a b : Fin 3) :
    c ^ (a + b).val = c ^ a.val * c ^ b.val := by
  rw [Fin.val_add, pow_mod3 c h, pow_add]

lemma pow_val_neg (c : Perm Ω) (h : c ^ 3 = 1) (a : Fin 3) :
    c ^ (-a).val = (c ^ a.val)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_val_add c h, neg_add_cancel]
  simp

lemma dH_pow_val_one (c : Perm Ω) (h : c ^ 3 = 1) (k : Fin 3) (hk : k ≠ 0) :
    dH (c ^ k.val) 1 = dH c 1 := by
  fin_cases k
  · exact absurd rfl hk
  · show dH (c ^ 1) 1 = dH c 1
    rw [pow_one]
  · show dH (c ^ 2) 1 = dH c 1
    have h2 : c ^ 2 = c⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ, h]
    rw [h2, dH_inv_one]

/-! ### The sector distribution -/

/-- `M_χ = ∑_g ω^{-χ·g} P_{f(g)}`. -/
noncomputable def Msec (c : Fin N → Perm Ω) (χ : Fin N → Fin 3) : Ω → Ω → ℂ :=
  FT (fun g => pm (fprod c g)) χ

/-- The sector distribution `p(χ) = ‖M_χ‖² / (9^N D)`. -/
noncomputable def pSec (c : Fin N → Perm Ω) (χ : Fin N → Fin 3) : ℝ :=
  nsq (Msec c χ) / (9 ^ N * Fintype.card Ω)

lemma pSec_nonneg (c : Fin N → Perm Ω) (χ : Fin N → Fin 3) : 0 ≤ pSec c χ :=
  div_nonneg (nsq_nonneg _) (by positivity)

lemma card_G : Fintype.card (Fin N → Fin 3) = 3 ^ N := by simp

lemma sum_nsq_Msec (c : Fin N → Perm Ω) :
    ∑ χ, nsq (Msec c χ) = 9 ^ N * Fintype.card Ω := by
  have h := parseval (fun g => pm (fprod c g)) (fun g => pm (fprod c g))
  simp only [hip_pm, dH_self, sub_zero, mul_one, sum_const, card_univ, card_G,
    nsmul_eq_mul] at h
  have h' : ((∑ χ, nsq (Msec c χ) : ℝ) : ℂ) = ((9 ^ N * Fintype.card Ω : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simp only [← hip_self, Msec]
    rw [h]
    push_cast
    rw [show (9 : ℂ) ^ N = 3 ^ N * 3 ^ N by rw [← mul_pow]; norm_num]
    ring
  exact_mod_cast h'

theorem sum_pSec (c : Fin N → Perm Ω) (hD : 0 < Fintype.card Ω) : ∑ χ, pSec c χ = 1 := by
  simp only [pSec, ← sum_div, sum_nsq_Msec]
  exact div_self (by positivity)

/-! ### Marginals -/

lemma FT_shift (A : (Fin N → Fin 3) → Ω → Ω → ℂ) (χ : Fin N → Fin 3) (i : Fin N) (k : Fin 3)
    (α β : Ω) :
    ech (k * χ i) * FT A χ α β = FT (fun g => A (g + Pi.single i k)) χ α β := by
  simp only [FT, mul_sum]
  rw [← Equiv.sum_comp (Equiv.addRight (Pi.single i k))]
  refine sum_congr rfl fun g _ => ?_
  simp only [Equiv.coe_addRight]
  have e : k * χ i + -(dot χ (g + Pi.single i k)) = -(dot χ g) := by
    have := dot_sub χ (g + Pi.single i k) (Pi.single i k)
    rw [add_sub_cancel_right, dot_single] at this
    rw [this, neg_sub, sub_eq_add_neg, mul_comm k (χ i)]
  rw [← mul_assoc, ← ech_add, e]

lemma hip_smul (A B : Ω → Ω → ℂ) (s : ℂ) : hip A (fun α β => s * B α β) = s * hip A B := by
  simp only [hip, mul_sum]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

lemma shift_eq_update (g : Fin N → Fin 3) (i : Fin N) (k : Fin 3) :
    g + Pi.single i k = Function.update g i (g i + k) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj, Function.update_of_ne hj]

lemma dH_fprod_shift (c : Fin N → Perm Ω) (hc : ∀ i, c i ^ 3 = 1) (g : Fin N → Fin 3)
    (i : Fin N) (k : Fin 3) :
    dH (fprod c g) (fprod c (g + Pi.single i k)) = dH (c i ^ k.val) 1 := by
  obtain ⟨L, R, h⟩ := fprod_update c g i
  have hg : fprod c g = L * c i ^ (g i).val * R := by
    rw [← h]; congr; exact (Function.update_eq_self i g).symm
  rw [shift_eq_update, h, hg, dH_mul_right, dH_mul_left, pow_val_add _ (hc i), dH_comm,
    dH_mul_self_left]

theorem marginal_pSec (c : Fin N → Perm Ω) (hc : ∀ i, c i ^ 3 = 1) (hD : 0 < Fintype.card Ω)
    (i : Fin N) :
    ∑ z ∈ univ.filter (fun z => z i ≠ 0), pSec c z = 2 / 3 * dH (c i) 1 := by
  have hc0 : (Fintype.card Ω : ℝ) ≠ 0 := by positivity
  -- the twisted sums
  have T : ∀ k : Fin 3, ∑ χ, ech (k * χ i) * (nsq (Msec c χ) : ℂ) =
      ((9 ^ N * Fintype.card Ω * (1 - dH (c i ^ k.val) 1) : ℝ) : ℂ) := by
    intro k
    have h := parseval (fun g => pm (fprod c g)) (fun g => pm (fprod c (g + Pi.single i k)))
    have e1 : ∀ χ, ech (k * χ i) * (nsq (Msec c χ) : ℂ) =
        hip (FT (fun g => pm (fprod c g)) χ)
          (FT (fun g => pm (fprod c (g + Pi.single i k))) χ) := by
      intro χ
      rw [← hip_self, Msec, ← hip_smul]
      congr 1
      funext α β
      exact FT_shift (fun g => pm (fprod c g)) χ i k α β
    simp only [e1, h, hip_pm, dH_fprod_shift c hc, sum_const, card_univ, card_G, nsmul_eq_mul]
    push_cast
    rw [show (9 : ℂ) ^ N = 3 ^ N * 3 ^ N by rw [← mul_pow]; norm_num]
    ring
  -- sum over `k`
  have S : ∑ χ, (if χ i = 0 then (3 : ℂ) else 0) * (nsq (Msec c χ) : ℂ) =
      ((9 ^ N * Fintype.card Ω * (3 - 2 * dH (c i) 1) : ℝ) : ℂ) := by
    have : ∀ χ : Fin N → Fin 3, (if χ i = 0 then (3 : ℂ) else 0) * (nsq (Msec c χ) : ℂ) =
        ∑ k : Fin 3, ech (k * χ i) * (nsq (Msec c χ) : ℂ) := by
      intro χ; rw [← sum_mul, sum_ech]
    rw [sum_congr rfl fun χ _ => this χ, sum_comm, Fin.sum_univ_three]
    simp only [T]
    rw [dH_pow_val_one _ (hc i) 1 (by decide), dH_pow_val_one _ (hc i) 2 (by decide)]
    simp only [Fin.val_zero, pow_zero, dH_self]
    push_cast
    ring
  have S2 : ∑ χ, (if χ i = 0 then 3 * nsq (Msec c χ) else 0) =
      9 ^ N * Fintype.card Ω * (3 - 2 * dH (c i) 1) := by
    have e : ∀ χ : Fin N → Fin 3, (if χ i = 0 then (3 : ℂ) else 0) * (nsq (Msec c χ) : ℂ) =
        (((if χ i = 0 then 3 * nsq (Msec c χ) else 0) : ℝ) : ℂ) := by
      intro χ; split_ifs <;> simp
    simp only [e] at S
    rw [← Complex.ofReal_sum] at S
    exact_mod_cast S
  have S' : ∑ χ, (if χ i = 0 then nsq (Msec c χ) else 0) =
      9 ^ N * Fintype.card Ω * (1 - 2 / 3 * dH (c i) 1) := by
    have : ∑ χ, (if χ i = 0 then 3 * nsq (Msec c χ) else 0) =
        3 * ∑ χ, (if χ i = 0 then nsq (Msec c χ) else 0) := by
      rw [mul_sum]; exact sum_congr rfl fun χ _ => by split_ifs <;> simp
    rw [this] at S2; linarith
  have htot := sum_nsq_Msec c
  have hsplit : ∑ z ∈ univ.filter (fun z => z i ≠ 0), pSec c z =
      (∑ χ, nsq (Msec c χ) - ∑ χ, (if χ i = 0 then nsq (Msec c χ) else 0)) /
        (9 ^ N * Fintype.card Ω) := by
    rw [sum_filter, ← sum_sub_distrib, sum_div]
    refine sum_congr rfl fun χ _ => ?_
    by_cases h : χ i = 0 <;> simp [pSec, h]
  rw [hsplit, htot, S']
  field_simp
  ring

/-! ### The Bhattacharyya bound -/

lemma fl_eq_neg (a : Fin 3) : fl a = -a := by fin_cases a <;> rfl

lemma flipAt_eq (i : Fin N) (z : Fin N → Fin 3) : flipAt i z = Function.update z i (-z i) := by
  simp [flipAt, fl_eq_neg]

lemma flipAt_flipAt (i : Fin N) (z : Fin N → Fin 3) : flipAt i (flipAt i z) = z := by
  simp [flipAt_eq]

lemma dot_flipAt (i : Fin N) (χ g : Fin N → Fin 3) : dot (flipAt i χ) g = dot χ (flipAt i g) := by
  simp only [dot, flipAt_eq]
  refine sum_congr rfl fun j _ => ?_
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

lemma FT_flip (A : (Fin N → Fin 3) → Ω → Ω → ℂ) (i : Fin N) (χ : Fin N → Fin 3) :
    FT A (flipAt i χ) = FT (fun g => A (flipAt i g)) χ := by
  funext α β
  simp only [FT, dot_flipAt]
  let e : Perm (Fin N → Fin 3) := Function.Involutive.toPerm _ (flipAt_flipAt i)
  rw [← Equiv.sum_comp e]
  refine sum_congr rfl fun g _ => ?_
  show ech (-dot χ (flipAt i (flipAt i g))) * A (flipAt i g) α β = _
  rw [flipAt_flipAt]

/-- The cross-commutator defect of `x_i` against the other `c_j`. -/
noncomputable def kap (c x : Fin N → Perm Ω) (i : Fin N) : ℝ :=
  ∑ j ∈ univ.filter (· ≠ i), dH (x i * c j) (c j * x i)

lemma dH_conj_fprod (c x : Fin N → Perm Ω) (h1 : ∀ i, c i ^ 3 = 1) (h2 : ∀ i, x i ^ 2 = 1)
    (h3 : ∀ i, x i * c i * x i = (c i)⁻¹) (i : Fin N) (g : Fin N → Fin 3) :
    dH (x i * fprod c g * x i) (fprod c (flipAt i g)) ≤ 2 * kap c x i := by
  have hx : x i * x i = 1 := by rw [← pow_two, h2]
  unfold fprod kap
  rw [conj_ofFn_prod (x i) hx]
  refine (dH_ofFn_prod_le _ _).trans ?_
  beta_reduce
  rw [← add_sum_erase univ _ (mem_univ i), filter_ne', mul_sum]
  have hi : dH (x i * c i ^ (g i).val * x i) (c i ^ (flipAt i g i).val) = 0 := by
    have hconj : x i * c i ^ (g i).val * x i = (c i ^ (g i).val)⁻¹ := by
      rw [← conj_pow_inv _ _ hx, h3, inv_pow]
    rw [hconj, flipAt_eq, Function.update_self, pow_val_neg _ (h1 i), dH_self]
  rw [hi, zero_add]
  refine sum_le_sum fun j hj => ?_
  have hji : j ≠ i := ne_of_mem_erase hj
  rw [flipAt_eq, Function.update_of_ne hji, ← conj_pow_inv _ _ hx]
  refine (dH_pow_le _ _ _).trans ?_
  have hval : ((g j).val : ℝ) ≤ 2 := by exact_mod_cast Nat.le_of_lt_succ (g j).isLt
  have hd : dH (x i * c j * x i) (c j) = dH (x i * c j) (c j * x i) := by
    rw [← dH_mul_right (x i) (x i * c j * x i) (c j), mul_assoc (x i * c j), hx, mul_one]
  rw [hd]
  exact mul_le_mul_of_nonneg_right hval (dH_nonneg _ _)

theorem bhatt_pSec (c x : Fin N → Perm Ω) (h1 : ∀ i, c i ^ 3 = 1) (h2 : ∀ i, x i ^ 2 = 1)
    (h3 : ∀ i, x i * c i * x i = (c i)⁻¹) (hD : 0 < Fintype.card Ω) (i : Fin N) :
    1 - 2 * kap c x i ≤ ∑ z, Real.sqrt (pSec c z * pSec c (flipAt i z)) := by
  have hKpos : (0 : ℝ) < 9 ^ N * Fintype.card Ω := by positivity
  have hx : x i * x i = 1 := by rw [← pow_two, h2]
  -- termwise Cauchy–Schwarz
  have hterm : ∀ χ, (hip (Msec c χ) (rix (x i) (Msec c (flipAt i χ)))).re /
      (9 ^ N * Fintype.card Ω) ≤ Real.sqrt (pSec c χ * pSec c (flipAt i χ)) := by
    intro χ
    have hcs := re_hip_le (Msec c χ) (rix (x i) (Msec c (flipAt i χ)))
    rw [nsq_rix] at hcs
    have e : Real.sqrt (pSec c χ * pSec c (flipAt i χ)) =
        Real.sqrt (nsq (Msec c χ)) * Real.sqrt (nsq (Msec c (flipAt i χ))) /
          (9 ^ N * Fintype.card Ω) := by
      unfold pSec
      rw [div_mul_div_comm, Real.sqrt_div (mul_nonneg (nsq_nonneg _) (nsq_nonneg _)),
        Real.sqrt_mul (nsq_nonneg _), Real.sqrt_mul_self hKpos.le]
    rw [e]
    exact div_le_div_of_nonneg_right hcs hKpos.le
  -- the sum of the overlaps, by Parseval
  have hsum : ∑ χ, hip (Msec c χ) (rix (x i) (Msec c (flipAt i χ))) =
      3 ^ N * ∑ g, (((Fintype.card Ω : ℝ) *
        (1 - dH (x i * fprod c g) (fprod c (flipAt i g) * x i)) : ℝ) : ℂ) := by
    have hB : ∀ χ, rix (x i) (Msec c (flipAt i χ)) =
        FT (fun g => rix (x i) (pm (fprod c (flipAt i g)))) χ := by
      intro χ; rw [Msec, FT_flip]; rfl
    simp only [hB]
    simp only [Msec]
    rw [parseval]
    simp only [hip_pm_rix]
  have hlow : ∀ g : Fin N → Fin 3, (Fintype.card Ω : ℝ) * (1 - 2 * kap c x i) ≤
      (Fintype.card Ω : ℝ) * (1 - dH (x i * fprod c g) (fprod c (flipAt i g) * x i)) := by
    intro g
    have hb := dH_conj_fprod c x h1 h2 h3 i g
    have e : dH (x i * fprod c g) (fprod c (flipAt i g) * x i) =
        dH (x i * fprod c g * x i) (fprod c (flipAt i g)) := by
      rw [← dH_mul_right (x i) (x i * fprod c g * x i) (fprod c (flipAt i g)),
        mul_assoc (x i * fprod c g), hx, mul_one]
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have hre : (9 ^ N * Fintype.card Ω) * (1 - 2 * kap c x i) ≤
      (∑ χ, hip (Msec c χ) (rix (x i) (Msec c (flipAt i χ)))).re := by
    rw [hsum, ← Complex.ofReal_sum, show (3 : ℂ) ^ N = (((3 : ℝ) ^ N : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    calc (9 ^ N * Fintype.card Ω) * (1 - 2 * kap c x i)
        = 3 ^ N * ∑ _g : Fin N → Fin 3, (Fintype.card Ω : ℝ) * (1 - 2 * kap c x i) := by
          rw [sum_const, card_univ, card_G, nsmul_eq_mul]; push_cast
          rw [show (9 : ℝ) ^ N = 3 ^ N * 3 ^ N by rw [← mul_pow]; norm_num]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_le_sum fun g _ => hlow g) (by positivity)
  calc 1 - 2 * kap c x i = (9 ^ N * Fintype.card Ω) * (1 - 2 * kap c x i) /
        (9 ^ N * Fintype.card Ω) := (mul_div_cancel_left₀ _ hKpos.ne').symm
    _ ≤ (∑ χ, hip (Msec c χ) (rix (x i) (Msec c (flipAt i χ)))).re /
        (9 ^ N * Fintype.card Ω) := div_le_div_of_nonneg_right hre hKpos.le
    _ = ∑ χ, (hip (Msec c χ) (rix (x i) (Msec c (flipAt i χ)))).re /
        (9 ^ N * Fintype.card Ω) := by rw [Complex.re_sum, sum_div]
    _ ≤ _ := sum_le_sum fun χ _ => hterm χ

/-! ### From the entropy bound to `PermSectorBound` -/

lemma logb_ge_of_sector {N : ℕ} (p : (Fin N → Fin 3) → ℝ) (L : ℝ) (hp0 : ∀ z, 0 ≤ p z)
    (hp1 : ∑ z, p z = 1) (hH : (∑ z, ent (p z)) / Real.log 2 ≤ L + N / 100)
    (hs : ∀ i, 1 / 12 ≤ ∑ z ∈ univ.filter (fun z => z i ≠ 0), p z)
    (hb : ∀ i, 1 - 1 / 20000 ≤ ∑ z, Real.sqrt (p z * p (flipAt i z))) :
    (N : ℝ) / 16 ≤ L := by
  have main := Ent_ge N p hp0
  have hEnt : Ent p = ∑ z, ent (p z) := by simp [Ent, hp1, ent_one]
  have hsi : ∀ i, 1 / 12 ≤ sAt i p := by
    intro i
    have := hs i
    simp only [sum_filter, ne_eq, ite_not] at this
    exact this
  have hdi : ∀ i, dAt i p ≤ 1 / 20000 := by
    intro i
    have e : ∀ z, (if z i = 0 then 0 else p z - Real.sqrt (p z * p (flipAt i z))) =
        p z - Real.sqrt (p z * p (flipAt i z)) := by
      intro z
      split_ifs with hz
      · have hf : flipAt i z = z := by
          simp only [flipAt, hz]
          rw [show fl 0 = 0 from rfl, ← hz, Function.update_eq_self]
        rw [hf, Real.sqrt_mul_self (hp0 z), sub_self]
      · rfl
    simp only [dAt, e, sum_sub_distrib, hp1]
    linarith [hb i]
  have hl2 := log_two_gt_half
  have hl2pos : 0 < Real.log 2 := by linarith
  have hsum : (N : ℝ) * (Real.log 2 * (1 / 12) - 2 * (1 / 20000)) ≤ ∑ z, ent (p z) := by
    rw [← hEnt]
    refine le_trans ?_ main
    have : ∀ i ∈ (univ : Finset (Fin N)),
        Real.log 2 * (1 / 12) - 2 * (1 / 20000) ≤ Real.log 2 * sAt i p - 2 * dAt i p := by
      intro i _
      have := hsi i
      have := hdi i
      nlinarith
    calc (N : ℝ) * (Real.log 2 * (1 / 12) - 2 * (1 / 20000))
        = ∑ _i : Fin N, (Real.log 2 * (1 / 12) - 2 * (1 / 20000)) := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum this
  rw [div_le_iff₀ hl2pos] at hH
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have key : Real.log 2 * ((N : ℝ) / 16) ≤ Real.log 2 * L := by
    nlinarith [mul_nonneg hN0 (le_of_lt (sub_pos.mpr hl2))]
  exact le_of_mul_le_mul_left key hl2pos

/-- **Remaining input**: the entropy of the explicit sector distribution is at most
`log₂ D + N/100` (the quantum part of Theorem `thm:phase-robust`). -/
def PermSectorEntropy : Prop :=
  ∀ (Ω : Type u) [Fintype Ω] [DecidableEq Ω] (N : ℕ) (c x : Fin N → Perm Ω),
    (∀ i, c i ^ 3 = 1) → (∀ i, x i ^ 2 = 1) → (∀ i, x i * c i * x i = (c i)⁻¹) →
    (∀ i, (1 : ℝ) / 8 ≤ dH (c i) 1) →
    (∀ i, ∑ j ∈ univ.filter (· ≠ i), dH (c i * c j) (c j * c i) ≤ 1 / 40000) →
    (∀ i, ∑ j ∈ univ.filter (· ≠ i), dH (x i * c j) (c j * x i) ≤ 1 / 40000) →
    (∑ z, ent (pSec c z)) / Real.log 2 ≤ Real.logb 2 (Fintype.card Ω) + N / 100

theorem permSectorBound_of_entropy (h : PermSectorEntropy.{u}) : PermSectorBound.{u} := by
  intro Ω _ _ N c x h1 h2 h3 h4 h5 h6
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Nat.cast_zero, zero_div]
    rcases Nat.eq_zero_or_pos (Fintype.card Ω) with hD | hD
    · simp [hD]
    · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hD)
  · have hD0 : Fintype.card Ω ≠ 0 := by
      intro h0
      have := h4 ⟨0, hN⟩
      rw [dH_eq, h0, Nat.cast_zero, div_zero] at this
      norm_num at this
    have hD := Nat.pos_of_ne_zero hD0
    refine logb_ge_of_sector (pSec c) _ (pSec_nonneg c) (sum_pSec c hD)
      (h Ω N c x h1 h2 h3 h4 h5 h6) (fun i => ?_) (fun i => ?_)
    · rw [marginal_pSec c h1 hD i]
      have := h4 i
      linarith
    · have hb := bhatt_pSec c x h1 h2 h3 hD i
      have := h6 i
      unfold kap at hb
      linarith

/-- **Proposition `prop:dimension-perm`**, assuming only the entropy bound `PermSectorEntropy`
for the explicit sector distribution. -/
theorem dimension_perm_of_sectorEntropy (hS : PermSectorEntropy.{u}) {Ω : Type u}
    [Fintype Ω] [DecidableEq Ω] (φ : F →* Equiv.Perm Ω) (δ : ℝ)
    (hrel : ∀ i, dH (φ (rel i)) 1 ≤ δ) (hγ : 1/2 ≤ dH (φ γ) 1) (N A : ℕ) (hN : 1 ≤ N)
    (hA : AstarLE (3 * N) A) (hδ : (10:ℝ)^8 * N * max 1 A * δ ≤ 1) :
    (N : ℝ) / 16 ≤ Real.logb 2 (Fintype.card Ω) :=
  dimension_perm_of_sectorBound (permSectorBound_of_entropy hS) φ δ hrel hγ N A hN hA hδ

end Houghton
