import Houghton.Area.Main
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring

/-! Theorem `thm:dehn` (Appendix B), part 1: Lemma `lem:transfer` (i), (ii) in general form,
with integer-indexed `σ`. -/

namespace Houghton

/-- `σ_k = a^k α a^{-k}` for `k : ℤ`. -/
def σz (k : ℤ) : F := a ^ k * α * a ^ (-k)

lemma σz_natCast (j : ℕ) : σz j = σ j := by
  simp [σz, σ, zpow_neg, zpow_natCast, inv_pow]

/-- **Lemma `lem:transfer` (ii)**: `U(q) ≤ ∑_{i<q} E(i)`. -/
theorem transfer_ii (E : ℕ → ℕ) : ∀ q : ℕ, (∀ i < q, AreaLE (comm (σ i) t) (E i)) →
    AreaEq (σ q) (τ q) (((List.range q).map E).sum)
  | 0, _ => AreaEq.of_eq (by simp [σ, τ])
  | q + 1, hE => by
    have ih := transfer_ii E q (fun i hi => hE i (by omega))
    have h1 := ((hE q (by omega)).conj b).inv
    have h2 := AreaLE.conj b ih
    have e : (b * comm (σ q) t * b⁻¹)⁻¹ * (b * (σ q * (τ q)⁻¹) * b⁻¹) =
        σ (q + 1) * (τ (q + 1))⁻¹ := by
      simp only [σ, τ, comm, t, inv_pow]
      group
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    show AreaLE (σ (q + 1) * (τ (q + 1))⁻¹) _
    rw [Nat.add_comm (List.sum _)]
    exact (h1.mul h2).of_eq e

/-- `t_k = a^k t a^{-k}`. -/
def tz (k : ℤ) : F := a ^ k * t * a ^ (-k)

lemma tz_step (k : ℤ) : AreaEq (tz k) (tz (k + 1) * σz (k - 1)) 1 := by
  -- `b^{-1} = a b^{-1} a^{-1} α` is a rotation of `r₄`
  have h := (AreaLE.rel 3).conj (a ^ k * a * b⁻¹ * a⁻¹)
  refine h.of_eq ?_
  simp only [rel, Matrix.cons_val, r₄, tz, σz, t]
  group

/-- `S_k = σ_{k-2} ⋯ σ_{-1}`. -/
def Sz : ℕ → F
  | 0 => 1
  | k + 1 => σz ((k : ℤ) - 1) * Sz k

lemma t_eq_tz_Sz : ∀ k : ℕ, AreaEq t (tz k * Sz k) k
  | 0 => AreaEq.of_eq (by simp [tz, Sz])
  | k + 1 => by
    have h := (t_eq_tz_Sz k).trans ((tz_step k).mul (AreaEq.refl (Sz k)))
    have e : tz ((k + 1 : ℕ) : ℤ) * Sz (k + 1) = tz ((k : ℤ) + 1) * σz ((k : ℤ) - 1) * Sz k := by
      rw [mul_assoc]; push_cast; rfl
    rw [e]
    exact h.mono (by omega)

/-- Far commutators with an integer index `l ≥ -1`. -/
lemma comm_σ_σz {A i : ℕ} (hA : ∀ d, 2 ≤ d → d ≤ i + 1 → AreaLE (comm (σ 0) (σ d)) A)
    (l : ℤ) (hl : -1 ≤ l) (hli : l + 2 ≤ i) : AreaLE (comm (σ i) (σz l)) A := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (i : ℤ) = l + d := ⟨(i - l).toNat, by omega⟩
  have h := ((hA d (by omega) (by omega)).comm_symm).conj (a ^ l)
  refine h.of_eq ?_
  have hi : σ i = σz (l + d) := by rw [← hd, σz_natCast]
  rw [hi]
  simp only [σz, σ, comm, zpow_add, zpow_natCast, zpow_neg, inv_pow]
  group

lemma comm_σ_Sz {A i : ℕ} (hA : ∀ d, 2 ≤ d → d ≤ i + 1 → AreaLE (comm (σ 0) (σ d)) A) :
    ∀ k : ℕ, k ≤ i → AreaLE (comm (σ i) (Sz k)) (k * A)
  | 0, _ => by
    rw [Nat.zero_mul]; exact AreaLE.of_eq_one (by show comm (σ i) 1 = 1; simp [comm])
  | k + 1, hk => by
    have h1 := comm_σ_σz hA ((k : ℤ) - 1) (by omega) (by omega)
    have h2 := comm_σ_Sz hA k (by omega)
    show AreaLE (comm (σ i) (σz ((k : ℤ) - 1) * Sz k)) _
    exact (h1.comm_mul_right h2).mono (by rw [Nat.succ_mul]; omega)

/-- **Lemma `lem:transfer` (i)**: `E(i) ≤ 2i + 1 + ∑_{d=2}^{i+1} A(d) ≤ 2i + 1 + i·A`. -/
theorem transfer_i {A : ℕ} (i : ℕ) (hA : ∀ d, 2 ≤ d → d ≤ i + 1 → AreaLE (comm (σ 0) (σ d)) A) :
    AreaLE (comm (σ i) t) (2 * i + 1 + i * A) := by
  have h1 : AreaEq (comm (σ i) t) (comm (σ i) (tz i * Sz i)) (0 + i + 0 + i) :=
    (AreaEq.refl _).comm (t_eq_tz_Sz i)
  have h2 : AreaLE (comm (σ i) (tz i)) 1 := by
    refine (area_comm_α_t.conj (a ^ (i : ℤ))).of_eq ?_
    simp only [σ, tz, comm, zpow_natCast, zpow_neg, inv_pow]
    group
  have h3 := h2.comm_mul_right (comm_σ_Sz hA i le_rfl)
  exact (AreaLE.of_areaEq h1 h3).mono (by omega)

/-! ### `E(i) ≤ 2Fi + 1` and `U(q) ≤ F q²` with `F = 1 + A*(M)` -/

lemma sum_bound (A : ℕ) : ∀ q : ℕ,
    ((List.range q).map fun i => 2 * i + 1 + i * A).sum ≤ (1 + A) * q ^ 2
  | 0 => by simp
  | q + 1 => by
    have ih := sum_bound A q
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have e : (1 + A) * (q + 1) ^ 2 = (1 + A) * q ^ 2 + (2 * q + 1 + q * A) + (A * q + A) := by ring
    omega

/-- `U(q) ≤ (1 + A) q²` when `A*(M) ≤ A` and `q ≤ M`. -/
theorem area_U_of_astar {M A q : ℕ} (hA : AstarLE M A) (hq : q ≤ M) :
    AreaEq (σ q) (τ q) ((1 + A) * q ^ 2) := by
  have hE : ∀ i < q, AreaLE (comm (σ i) t) (2 * i + 1 + i * A) := fun i hi =>
    transfer_i i fun d hd hdi => hA 0 d (by omega) (by omega) (by omega) true true
  exact (transfer_ii _ q hE).mono (sum_bound A q)

/-! ### The collection identity `b^q a b^{-q} = τ_{q-1}^{-1} ⋯ τ_0^{-1} a` (`q` cells) -/

/-- `τ_{q-1}^{-1} ⋯ τ_0^{-1}`. -/
def Pτ : ℕ → F
  | 0 => 1
  | q + 1 => (τ q)⁻¹ * Pτ q

/-- `σ_{q-1}^{-1} ⋯ σ_0^{-1}`. -/
def Pσ : ℕ → F
  | 0 => 1
  | q + 1 => (σ q)⁻¹ * Pσ q

lemma conj_b_Pτ : ∀ q : ℕ, b * Pτ q * b⁻¹ * α⁻¹ = Pτ (q + 1)
  | 0 => by simp [Pτ, τ]
  | q + 1 => by
    have ih := conj_b_Pτ q
    have e : b * Pτ (q + 1) * b⁻¹ * α⁻¹ = (τ (q + 1))⁻¹ * (b * Pτ q * b⁻¹ * α⁻¹) := by
      simp only [Pτ, τ, inv_pow]
      group
    rw [e, ih]; rfl

theorem collect_b_a : ∀ q : ℕ, AreaEq (b ^ q * a * b⁻¹ ^ q) (Pτ q * a) q
  | 0 => AreaEq.of_eq (by simp [Pτ])
  | q + 1 => by
    have h1 := (collect_b_a q).conj b
    have h2 : AreaEq (b * a * b⁻¹) (α⁻¹ * a) 1 := by
      refine ((AreaLE.rel 3).inv.conj α⁻¹).of_eq ?_
      simp only [rel, Matrix.cons_val, r₄]
      group
    have h3 := (AreaEq.refl (b * Pτ q * b⁻¹)).mul h2
    have e1 : b * (b ^ q * a * b⁻¹ ^ q) * b⁻¹ = b ^ (q + 1) * a * b⁻¹ ^ (q + 1) := by
      simp only [inv_pow]; group
    have e2 : b * Pτ q * b⁻¹ * (α⁻¹ * a) = Pτ (q + 1) * a := by
      rw [← conj_b_Pτ q]; group
    have e3 : b * (Pτ q * a) * b⁻¹ = b * Pτ q * b⁻¹ * (b * a * b⁻¹) := by group
    rw [e1, e3] at h1
    rw [e2] at h3
    exact (h1.trans h3).mono (by omega)

/-- Replacing each `τ_j` by `σ_j` (`U(j) ≤ (1+A) j²` each). -/
theorem Pτ_Pσ {M A : ℕ} (hA : AstarLE M A) :
    ∀ q : ℕ, q ≤ M → AreaEq (Pτ q) (Pσ q) (q * ((1 + A) * q ^ 2))
  | 0, _ => AreaEq.of_eq rfl
  | q + 1, hq => by
    have h1 := (area_U_of_astar hA (q := q) (by omega)).symm.inv
    have h2 := Pτ_Pσ hA q (by omega)
    refine (h1.mul h2).mono ?_
    have : q ^ 2 ≤ (q + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h4 : (1 + A) * q ^ 2 ≤ (1 + A) * (q + 1) ^ 2 := Nat.mul_le_mul_left _ this
    have h5 : q * ((1 + A) * q ^ 2) ≤ q * ((1 + A) * (q + 1) ^ 2) := Nat.mul_le_mul_left _ h4
    rw [Nat.succ_mul]; omega

/-- **Collection rule** `s(m,q) a = (σ_{m+q-1}^{-1} ⋯ σ_m^{-1}) s(m+1,q)` with
`s(m,q) = a^m b^q`, at cost `q + q (1+A) q²`. -/
theorem collect_rule_a {M A : ℕ} (hA : AstarLE M A) (m q : ℕ) (hq : q ≤ M) :
    AreaEq (a ^ m * b ^ q * a) (a ^ m * Pσ q * (a ^ m)⁻¹ * (a ^ (m + 1) * b ^ q))
      (q + q * ((1 + A) * q ^ 2)) := by
  have h := (collect_b_a q).trans ((Pτ_Pσ hA q hq).mul (AreaEq.refl a))
  have h2 := (h.mul (AreaEq.refl (b ^ q))).conj (a ^ m)
  have e1 : a ^ m * (b ^ q * a * b⁻¹ ^ q * b ^ q) * (a ^ m)⁻¹ * a ^ m = a ^ m * b ^ q * a := by
    simp only [inv_pow]; group
  have e2 : a ^ m * (Pσ q * a * b ^ q) * (a ^ m)⁻¹ * a ^ m =
      a ^ m * Pσ q * (a ^ m)⁻¹ * (a ^ (m + 1) * b ^ q) := by
    simp only [pow_succ]; group
  have h3 := h2.mul (AreaEq.refl (a ^ m))
  rw [e1, e2] at h3
  exact h3.mono (by omega)

/-- Rewriting both sides of an `AreaEq` by free identities. -/
lemma areaEq_congr {u u' v v' : F} {n m : ℕ} (h : AreaEq u v n) (e : u = u') (e' : v = v')
    (hnm : n ≤ m) : AreaEq u' v' m := e ▸ e' ▸ h.mono hnm

/-- **Collection rule** for `a⁻¹`: `s(m+1,q) a⁻¹ = (σ_{m+q-1}^{-1} ⋯ σ_m^{-1})⁻¹ s(m,q)`. -/
theorem collect_rule_a_inv {M A : ℕ} (hA : AstarLE M A) (m q : ℕ) (hq : q ≤ M) :
    AreaEq (a ^ (m + 1) * b ^ q * a⁻¹) ((a ^ m * Pσ q * (a ^ m)⁻¹)⁻¹ * (a ^ m * b ^ q))
      (q + q * ((1 + A) * q ^ 2)) := by
  have h := ((collect_rule_a hA m q hq).symm.mul (AreaEq.refl a⁻¹))
  have h2 := (AreaEq.refl (a ^ m * Pσ q * (a ^ m)⁻¹)⁻¹).mul h
  refine areaEq_congr h2 ?_ ?_ (by omega)
  · simp only [pow_succ]; group
  · group

/-- **Collection rule** for `α`: `s(m,q) α = σ_{m+q} s(m,q)`, at cost `U(q) ≤ (1+A) q²`. -/
theorem collect_rule_α {M A : ℕ} (hA : AstarLE M A) (m q : ℕ) (hq : q ≤ M) :
    AreaEq (a ^ m * b ^ q * α) (σ (m + q) * (a ^ m * b ^ q)) ((1 + A) * q ^ 2) := by
  have h := (((area_U_of_astar hA hq).symm.mul (AreaEq.refl (b ^ q))).conj (a ^ m)).mul
    (AreaEq.refl (a ^ m))
  refine areaEq_congr h ?_ ?_ (by omega)
  · simp only [τ, inv_pow]; group
  · simp only [σ, pow_add, inv_pow]; group

end Houghton
