/- Xia/Proofs/Thm31.lean — proofs of the rows thm_3_1_step3, thm_3_1_step4, H4_theta, thm_3_1_step2, thm_3_1_bij, thm_3_1_card and 1 more of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import Xia.Defs.Symmetry

namespace Xia.Proofs

open Xia Finset

set_option linter.unusedSectionVars false

/-! ## Part A — the exponent model: `ω ^ k.val` for `k : ZMod n` when `ω ^ n = 1` -/

section Expo

variable {n : ℕ} [NeZero n] {M : Type*} [Monoid M]

theorem H4_pow_congr {ω : M} (hω : ω ^ n = 1) {a b : ℕ} (hab : (a : ZMod n) = (b : ZMod n)) :
    ω ^ a = ω ^ b := by
  rw [ZMod.natCast_eq_natCast_iff'] at hab
  rw [pow_eq_pow_mod a hω, pow_eq_pow_mod b hω, hab]

theorem H4_pow_val_natCast {ω : M} (hω : ω ^ n = 1) (a : ℕ) : ω ^ ((a : ZMod n).val) = ω ^ a :=
  H4_pow_congr hω (by rw [ZMod.natCast_zmod_val])

theorem H4_pow_val_add {ω : M} (hω : ω ^ n = 1) (a b : ZMod n) :
    ω ^ ((a + b).val) = ω ^ a.val * ω ^ b.val := by
  rw [← pow_add]
  apply H4_pow_congr hω
  rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

theorem H4_pow_val_mul_nat {ω : M} (hω : ω ^ n = 1) (k : ZMod n) (a : ℕ) :
    (ω ^ k.val) ^ a = ω ^ ((k * (a : ZMod n)).val) := by
  rw [← pow_mul]
  apply H4_pow_congr hω
  rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

theorem H4_pow_val_mul {ω : M} (hω : ω ^ n = 1) (k t : ZMod n) :
    (ω ^ k.val) ^ t.val = ω ^ ((k * t).val) := by
  rw [H4_pow_val_mul_nat hω, ZMod.natCast_zmod_val]

theorem H4_pow_val_zero (ω : M) : ω ^ ((0 : ZMod n).val) = 1 := by
  rw [ZMod.val_zero, pow_zero]

theorem H4_pow_val_neg {K : Type*} [Field K] {ω : K} (hω : ω ^ n = 1) (k : ZMod n) :
    ω ^ ((-k).val) = (ω ^ k.val)⁻¹ := by
  have h1 : ω ^ ((-k).val) * ω ^ k.val = 1 := by
    rw [← H4_pow_val_add hω, neg_add_cancel, H4_pow_val_zero]
  exact eq_inv_of_mul_eq_one_left h1

end Expo

/-! ## Part B — arithmetic of `n = 2^e`, `half n`, and powers of `3` modulo `2^e` -/

section Arith

theorem H4_shape {n e : ℕ} (hne : n = 2 ^ e) (he : 3 ≤ e) : ∃ t : ℕ, 1 ≤ t ∧ n = 8 * t := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 3 := ⟨e - 3, by omega⟩
  refine ⟨2 ^ k, Nat.one_le_two_pow, ?_⟩
  rw [hne, pow_add]; ring

theorem H4_two_pow_dvd (k : ℕ) : (2 : ℤ) ^ (k + 3) ∣ 3 ^ (2 ^ (k + 1)) - 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have e1 : (3 : ℤ) ^ (2 ^ (k + 1 + 1)) - 1 = (3 ^ (2 ^ (k + 1)) - 1) * (3 ^ (2 ^ (k + 1)) + 1) := by
      rw [pow_succ 2 (k + 1), pow_mul]; ring
    have e2 : (2 : ℤ) ^ (k + 1 + 3) = 2 ^ (k + 3) * 2 := by ring
    rw [e1, e2]
    apply mul_dvd_mul ih
    have h2 : (2 : ℤ) ∣ 3 ^ (2 ^ (k + 1)) - 1 := (dvd_pow_self 2 (by omega)).trans ih
    have e3 : (3 : ℤ) ^ (2 ^ (k + 1)) + 1 = (3 ^ (2 ^ (k + 1)) - 1) + 2 := by ring
    rw [e3]; exact dvd_add h2 (dvd_refl 2)

/-- `3^{n/4} ≡ 1 (mod n)` for `n = 2^e`, `e ≥ 3` (so `Q ≡ 1`, `ξ^Q = ξ` on `μ_n`). -/
theorem H4_three_pow_quarter {n e : ℕ} (hne : n = 2 ^ e) (he : 3 ≤ e) : (3 : ZMod n) ^ (n / 4) = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 3 := ⟨e - 3, by omega⟩
  have h4 : n / 4 = 2 ^ (k + 1) := by
    rw [hne, show 2 ^ (k + 3) = 2 ^ (k + 1) * 4 by ring]
    exact Nat.mul_div_cancel _ (by norm_num)
  have hd := H4_two_pow_dvd k
  have hz : (((3 ^ (2 ^ (k + 1)) - 1 : ℤ)) : ZMod n) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hne]; push_cast; exact hd
  push_cast at hz
  rw [h4]; exact sub_eq_zero.mp hz

theorem H4_QQ_cast {n e : ℕ} (hne : n = 2 ^ e) (he : 3 ≤ e) : ((QQ n : ℕ) : ZMod n) = 1 := by
  unfold QQ; push_cast; exact H4_three_pow_quarter hne he

theorem H4_QQ_odd (n : ℕ) : Odd (QQ n) := by
  unfold QQ; exact Odd.pow (by decide)

theorem H4_QQ_pos (n : ℕ) : 1 ≤ QQ n := by
  unfold QQ; exact Nat.one_le_pow _ _ (by norm_num)

variable {n : ℕ} [NeZero n]

theorem H4_half_val (n : ℕ) [NeZero n] : (half n).val = n / 2 := by
  unfold half
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.div_lt_self (Nat.pos_of_ne_zero (NeZero.ne n)) (by norm_num))]

theorem H4_half_add_half (hn : Even n) : half n + half n = 0 := by
  unfold half
  rw [← Nat.cast_add, show n / 2 + n / 2 = n by obtain ⟨r, hr⟩ := hn; omega, ZMod.natCast_self]

theorem H4_neg_half (hn : Even n) : -half n = half n :=
  neg_eq_of_add_eq_zero_right (H4_half_add_half hn)

theorem H4_two_mul_half (hn : Even n) : 2 * half n = 0 := by
  rw [two_mul, H4_half_add_half hn]

theorem H4_half_ne_zero (h2 : 2 ≤ n) : half n ≠ 0 := by
  intro h
  have := congrArg ZMod.val h
  rw [H4_half_val, ZMod.val_zero] at this
  omega

/-- The elements killed by `2` in `ℤ/n` (`n` even) are `0` and `n/2`. -/
theorem H4_two_mul_eq_zero (hn : Even n) (hbig : 3 ≤ n) (x : ZMod n) (hx : 2 * x = 0) : x = 0 ∨ x = half n := by
  have hv := congrArg ZMod.val hx
  rw [ZMod.val_mul, ZMod.val_zero] at hv
  have hlt := ZMod.val_lt x
  have h2val : (2 : ZMod n).val = 2 := by
    rw [show (2 : ZMod n) = ((2 : ℕ) : ZMod n) by norm_num, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  rw [h2val] at hv
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hv
  have hq2 : q < 2 := by
    by_contra hc
    have : n * 2 ≤ n * q := Nat.mul_le_mul_left n (by omega)
    omega
  obtain ⟨r, hr⟩ := hn
  interval_cases q
  · left
    rw [← ZMod.natCast_zmod_val x, show x.val = 0 by omega, Nat.cast_zero]
  · right
    rw [← ZMod.natCast_zmod_val x]; unfold half; congr 1; omega

end Arith

/-! ## Part C — roots of unity of order `n` -/

section Roots

variable {n : ℕ} {L : Type*} [Field L]

theorem H4_pow_half {ω : L} (hω : IsPrimitiveRoot ω n) (hn : Even n) (h2 : 2 ≤ n) : ω ^ (n / 2) = -1 := by
  have hsq : (ω ^ (n / 2)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.mp hn)]; exact hω.pow_eq_one
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact absurd h (hω.pow_ne_one_of_pos_of_lt (by omega) (by omega))
  · exact h

theorem H4_pow_val_half [NeZero n] {ω : L} (hω : IsPrimitiveRoot ω n) (hn : Even n) (h2 : 2 ≤ n) :
    ω ^ (half n).val = -1 := by
  rw [H4_half_val]; exact H4_pow_half hω hn h2

end Roots

/-! ## Part D — Steps 3 and 4 (any field) -/

theorem thm_3_1_step3_proved (n : ℕ) [NeZero n] (h4 : 4 ∣ n) {L : Type*} [Field L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (h : ZMod n → L) (s0 : L) (hs : s0 ^ 2 = 1) (x : ZMod n)
    (hF1 : ∀ z ∈ ({x, x + half n} : Set (ZMod n)), h (3 * z) = (ω ^ z.val) ^ 6 * h z ^ 3)
    (hF3 : ∀ z ∈ ({x, x + half n} : Set (ZMod n)), h z * h (-z) = (ω ^ z.val) ^ (n / 2)) :
    s0 * h (3 * x) * h (3 * x + half n) = (ω ^ (2 * x).val) ^ 6 * (s0 * h x * h (x + half n)) ^ 3 ∧
      (s0 * h x * h (x + half n)) * (s0 * h (-x) * h (-x + half n)) = (ω ^ (2 * x).val) ^ (n / 2) := by
  have hn : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h4)
  have hn0 : n ≠ 0 := NeZero.ne n
  have h2 : 2 ≤ n := by obtain ⟨r, hr⟩ := h4; omega
  have hω1 : ω ^ n = 1 := hω.pow_eq_one
  have hmem1 : x ∈ ({x, x + half n} : Set (ZMod n)) := Set.mem_insert _ _
  have hmem2 : x + half n ∈ ({x, x + half n} : Set (ZMod n)) := Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hEm : ω ^ (half n).val = -1 := H4_pow_val_half hω hn h2
  have hEx : ω ^ (x + half n).val = -ω ^ x.val := by
    rw [H4_pow_val_add hω1, hEm]; ring
  have hE2 : ω ^ (2 * x).val = ω ^ x.val * ω ^ x.val := by
    rw [two_mul, H4_pow_val_add hω1]
  have h3x : 3 * x + half n = 3 * (x + half n) := by
    have : 3 * (x + half n) = 3 * x + half n + (half n + half n) := by ring
    rw [this, H4_half_add_half hn, add_zero]
  have hnx : -x + half n = -(x + half n) := by
    rw [neg_add, H4_neg_half hn]
  have hev : Even (n / 2) := by
    obtain ⟨r, hr⟩ := h4; exact ⟨r, by omega⟩
  constructor
  · rw [h3x, hF1 x hmem1, hF1 _ hmem2, hEx, hE2]
    have hs3 : s0 ^ 3 = s0 := by rw [pow_succ, hs, one_mul]
    have : (-ω ^ x.val) ^ 6 = (ω ^ x.val) ^ 6 := by ring
    rw [this]
    linear_combination (-(ω ^ x.val) ^ 12 * h x ^ 3 * h (x + half n) ^ 3) * hs3
  · rw [hnx]
    have e1 := hF3 x hmem1
    have e2 := hF3 _ hmem2
    rw [hEx, Even.neg_pow hev] at e2
    rw [hE2, mul_pow]
    linear_combination (h x * h (-x) * h (x + half n) * h (-(x + half n))) * hs +
      (ω ^ x.val) ^ (n / 2) * e2 + h (x + half n) * h (-(x + half n)) * e1

theorem thm_3_1_step4_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) {L : Type*} [Field L] (ω : L)
    (hω : IsPrimitiveRoot ω n) (h : ZMod n → L) (hF3 : F3 ω h) :
    h ((n / 4 : ℕ) : ZMod n) * h (((n / 4 : ℕ) : ZMod n) + half n) = 1 ∧ h 0 ^ 2 = 1 ∧ h 0 = h 0 ^ 3 ∧
      h (half n) ^ 2 = 1 := by
  obtain ⟨t, ht1, hnt⟩ := H4_shape hne he
  have hn : Even n := ⟨4 * t, by omega⟩
  have h2 : 2 ≤ n := by omega
  have hm : ω ^ (n / 2) = -1 := H4_pow_half hω hn h2
  have h00 : h 0 ^ 2 = 1 := by
    have := hF3 0
    rw [neg_zero, H4_pow_val_zero, one_pow] at this
    rw [sq]; exact this
  refine ⟨?_, h00, ?_, ?_⟩
  · have hneg : ((n / 4 : ℕ) : ZMod n) + half n = -((n / 4 : ℕ) : ZMod n) := by
      apply eq_neg_of_add_eq_zero_left
      unfold half
      rw [← Nat.cast_add, ← Nat.cast_add, show n / 4 + n / 2 + n / 4 = n by omega, ZMod.natCast_self]
    rw [hneg, hF3, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), ← pow_mul,
      show n / 4 * (n / 2) = n / 2 * (n / 4) by ring, pow_mul, hm]
    exact Even.neg_one_pow ⟨t, by omega⟩
  · rw [pow_succ, h00, one_mul]
  · have := hF3 (half n)
    rw [H4_neg_half hn, H4_half_val, hm, Even.neg_one_pow ⟨2 * t, by omega⟩] at this
    rw [sq]; exact this

/-! ## Part E — Step 2, the generic identities along the orbit `{3^k}` -/

section Step2Generic

variable {K : Type*} [Field K]

/-- `t_k := ξ_0^{2k3^k} θ^{3^k}` (s3_pow2.tex:30). -/
def H4_t (ξ0 θ : K) (j : ℕ) : K := ξ0 ^ (2 * j * 3 ^ j) * θ ^ (3 ^ j)

theorem H4_step2a (ξ0 θ : K) (k : ℕ) : ξ0 ^ (2 * (k + 1) * 3 ^ (k + 1)) * θ ^ (3 ^ (k + 1)) =
    (ξ0 ^ (3 ^ k)) ^ 6 * (ξ0 ^ (2 * k * 3 ^ k) * θ ^ (3 ^ k)) ^ 3 := by
  have e1 : 2 * (k + 1) * 3 ^ (k + 1) = 3 ^ k * 6 + 2 * k * 3 ^ k * 3 := by ring
  have e2 : 3 ^ (k + 1) = 3 ^ k * 3 := by ring
  rw [e1, e2, pow_add, pow_mul ξ0 (3 ^ k) 6, pow_mul ξ0 (2 * k * 3 ^ k) 3, pow_mul θ (3 ^ k) 3]
  ring

theorem H4_step2c (ξ0 θ : K) (k : ℕ) : -1 / (ξ0 ^ (2 * (k + 1) * 3 ^ (k + 1)) * θ ^ (3 ^ (k + 1))) =
    ((ξ0 ^ (3 ^ k))⁻¹) ^ 6 * (-1 / (ξ0 ^ (2 * k * 3 ^ k) * θ ^ (3 ^ k))) ^ 3 := by
  rw [H4_step2a]
  simp only [div_eq_mul_inv, mul_inv, inv_pow]
  ring

theorem H4_theta_of {θ : K} {Q : ℕ} (hQ1 : 1 ≤ Q) (hθ0 : θ ≠ 0) (hQ : θ ^ Q = -θ) : θ ^ (Q - 1) = -1 := by
  have : θ ^ (Q - 1) * θ = -1 * θ := by rw [pow_sub_one_mul (by omega), hQ]; ring
  exact mul_right_cancel₀ hθ0 this

theorem H4_step2b {n : ℕ} [NeZero n] (h4 : 4 ∣ n) {ξ0 θ : K} (hξ1 : ξ0 ^ n = 1) (hm : ξ0 ^ (n / 2) = -1)
    (h3q : (3 : ZMod n) ^ (n / 4) = 1) (hθ : θ ^ (3 ^ (n / 4) - 1) = -1) (k : ℕ) :
    ξ0 ^ (2 * (k + n / 4) * 3 ^ (k + n / 4)) * θ ^ (3 ^ (k + n / 4)) = ξ0 ^ (2 * k * 3 ^ k) * θ ^ (3 ^ k) := by
  have hQ1 : 1 ≤ 3 ^ (n / 4) := Nat.one_le_pow _ _ (by norm_num)
  have hθQ : θ ^ (3 ^ (n / 4)) = -θ := by
    rw [← pow_sub_one_mul (by omega), hθ]; ring
  have hodd : Odd (3 ^ k) := Odd.pow (by decide)
  have hθpart : θ ^ (3 ^ (k + n / 4)) = -θ ^ (3 ^ k) := by
    rw [pow_add, mul_comm, pow_mul, hθQ, hodd.neg_pow]
  have hexp : 2 * (k + n / 4) * 3 ^ (k + n / 4) = (2 * k * 3 ^ k + n / 2 * 3 ^ k) * 3 ^ (n / 4) := by
    rw [pow_add, show n / 2 = 2 * (n / 4) by obtain ⟨r, hr⟩ := h4; omega]; ring
  have hξpart : ξ0 ^ (2 * (k + n / 4) * 3 ^ (k + n / 4)) = -ξ0 ^ (2 * k * 3 ^ k) := by
    rw [hexp, H4_pow_congr hξ1 (b := 2 * k * 3 ^ k + n / 2 * 3 ^ k) (by push_cast; rw [h3q, mul_one]),
      pow_add, pow_mul ξ0 (n / 2) (3 ^ k), hm, hodd.neg_one_pow]
    ring
  rw [hθpart, hξpart]; ring

end Step2Generic

/-! ## Part F — facts about solutions of the norm-free system (no hypotheses) -/

section NF

variable {n : ℕ} [NeZero n]

/-- (L1) iterated: `y_{s+2j} = y_s^{3^j}`. -/
theorem H4_L1_iter {K : Type*} [CommRing K] (y : ZMod n → K) (hL1 : L1 3 ((2 : ℕ) : ℤ) y) :
    ∀ (j : ℕ) (s : ZMod n), y (s + ((2 * j : ℕ) : ZMod n)) = y s ^ (3 ^ j) := by
  intro j
  induction j with
  | zero => intro s; simp
  | succ j ih =>
    intro s
    have h1 := hL1 (s + ((2 * j : ℕ) : ZMod n))
    have e : s + ((2 * j : ℕ) : ZMod n) + ((((2 : ℕ) : ℤ)) : ZMod n) = s + ((2 * (j + 1) : ℕ) : ZMod n) := by
      push_cast; ring
    rw [e, ih] at h1
    rw [h1, ← pow_mul, pow_succ]

theorem H4_L1_half {e : ℕ} (hne : n = 2 ^ e) (he : 3 ≤ e) {K : Type*} [CommRing K] (y : ZMod n → K)
    (hL1 : L1 3 ((2 : ℕ) : ℤ) y) (s : ZMod n) : y (s + half n) = y s ^ (3 ^ (n / 4)) := by
  obtain ⟨t, ht1, hnt⟩ := H4_shape hne he
  have := H4_L1_iter y hL1 (n / 4) s
  rw [show 2 * (n / 4) = n / 2 by omega] at this
  exact this

theorem H4_nm_eq {e : ℕ} (hne : n = 2 ^ e) (he : 3 ≤ e) {K : Type*} [CommRing K] (y : ZMod n → K)
    (hL1 : L1 3 ((2 : ℕ) : ℤ) y) (s : ZMod n) : Nm n (y s) = y s * y (s + half n) := by
  rw [H4_L1_half hne he y hL1 s]; unfold Nm; rw [pow_add, pow_one]

/-- (L3) and `R(m) = 1` give `R = δ_m`. -/
theorem H4_R_of_NF {K : Type*} [CommRing K] (hn : Even n) (y : ZMod n → K) (hL3 : L3 0 y)
    (hRm : R y (half n) = 1) : ∀ s : ZMod n, R y s = if s = half n then 1 else 0 := by
  have hR3 : ∀ s : ZMod n, s.val < n / 2 → R y s = 0 := by
    intro s hs; unfold R; rw [← hL3 s hs]; apply Finset.sum_congr rfl; intro t _; rw [add_comm t s]
  have hneg : ∀ s : ZMod n, R y s = R y (-s) := by
    intro s; unfold R
    rw [← Equiv.sum_comp (Equiv.addRight s) (fun t => y t * y (t + -s))]
    apply Finset.sum_congr rfl; intro t _
    simp only [Equiv.coe_addRight, add_neg_cancel_right]; ring
  intro s
  split_ifs with hs
  · rw [hs, hRm]
  · rcases lt_trichotomy s.val (n / 2) with hlt | heq | hgt
    · exact hR3 s hlt
    · exfalso; apply hs; rw [← ZMod.natCast_zmod_val s, heq]; rfl
    · rw [hneg]; apply hR3
      have hs0 : s ≠ 0 := by intro h0; rw [h0, ZMod.val_zero] at hgt; omega
      rw [ZMod.neg_val, ite_eq_right hs0]
      have := ZMod.val_lt s
      obtain ⟨r, hr⟩ := hn; omega

/-- The correlation computation: `ŷ(ξ)ŷ(ξ^{-1}) = ∑_s R(s) ξ^{-s} = ξ^m` when `R = δ_m`. -/
theorem H4_F3_of_R {K : Type*} [Field K] (hn : Even n) {ω : K} (hω1 : ω ^ n = 1) (y : ZMod n → K)
    (hR : ∀ s : ZMod n, R y s = if s = half n then 1 else 0) (k : ZMod n) :
    dft ω y k * dft ω y (-k) = (ω ^ k.val) ^ (n / 2) := by
  unfold dft
  simp_rw [H4_pow_val_mul hω1]
  rw [Finset.sum_mul_sum]
  have step : ∀ t : ZMod n, ∑ u, (y t * ω ^ ((k * t).val)) * (y u * ω ^ ((-k * u).val)) =
      ∑ s, y t * y (t + s) * ω ^ ((-(k * s)).val) := by
    intro t
    rw [← Equiv.sum_comp (Equiv.addLeft t)]
    apply Finset.sum_congr rfl
    intro s _
    simp only [Equiv.coe_addLeft]
    have : ω ^ ((k * t).val) * ω ^ ((-k * (t + s)).val) = ω ^ ((-(k * s)).val) := by
      rw [← H4_pow_val_add hω1]; congr 2; ring
    linear_combination (y t * y (t + s)) * this
  rw [Finset.sum_congr rfl (fun t _ => step t), Finset.sum_comm]
  have hRs : ∀ s : ZMod n, ∑ t, y t * y (t + s) * ω ^ ((-(k * s)).val) =
      (if s = half n then 1 else 0) * ω ^ ((-(k * s)).val) := by
    intro s; rw [← hR s, R, Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun s _ => hRs s)]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [H4_pow_val_mul_nat hω1, ← mul_neg, H4_neg_half hn]
  rfl

theorem H4_NF_F3 {e : ℕ} (hne : n = 2 ^ e) (he : 3 ≤ e) {K : Type*} [Field K] {ω : K}
    (hω : IsPrimitiveRoot ω n) (y : ZMod n → K) (hL3 : L3 0 y) (hRm : R y (half n) = 1) : F3 ω (dft ω y) := by
  obtain ⟨t, ht1, hnt⟩ := H4_shape hne he
  have hn : Even n := ⟨4 * t, by omega⟩
  exact H4_F3_of_R hn hω.pow_eq_one y (H4_R_of_NF hn y hL3 hRm)

theorem H4_S_eq_dft {K : Type*} [Field K] (hn : Even n) (h2 : 2 ≤ n) {ω : K} (hω : IsPrimitiveRoot ω n)
    (y : ZMod n → K) : dft ω y (half n) = S y := by
  unfold dft S sgn
  rw [H4_pow_val_half hω hn h2]
  apply Finset.sum_congr rfl; intro t _; ring

/-- Frobenius on `θ = ŷ(ξ_0)`: `θ^Q = -θ` (s3_pow2.tex:28-30, via `y_{t+m} = y_t^Q` and `ξ_0^Q = ξ_0`). -/
theorem H4_frob {K : Type*} [Field K] [CharP K 3] {e : ℕ} (hne : n = 2 ^ e) (he : 3 ≤ e)
    {ω : K} (hω : IsPrimitiveRoot ω n) (y : ZMod n → K) (hL1 : L1 3 ((2 : ℕ) : ℤ) y) :
    dft ω y 1 ^ QQ n = -dft ω y 1 := by
  obtain ⟨t, ht1, hnt⟩ := H4_shape hne he
  have hn : Even n := ⟨4 * t, by omega⟩
  have hω1 : ω ^ n = 1 := hω.pow_eq_one
  have hEm : ω ^ (half n).val = -1 := H4_pow_val_half hω hn (by omega)
  have hrw : ∀ u : ZMod n, (ω ^ (1 : ZMod n).val) ^ u.val = ω ^ u.val := by
    intro u; rw [H4_pow_val_mul hω1, one_mul]
  unfold dft
  simp_rw [hrw]
  unfold QQ
  rw [sum_pow_char_pow]
  have hterm : ∀ u : ZMod n, (y u * ω ^ u.val) ^ 3 ^ (n / 4) = -(y (u + half n) * ω ^ (u + half n).val) := by
    intro u
    rw [mul_pow, ← H4_L1_half hne he y hL1 u, ← pow_mul,
      H4_pow_congr hω1 (b := u.val) (by push_cast; rw [H4_three_pow_quarter hne he, mul_one]),
      H4_pow_val_add hω1, hEm]
    ring
  rw [Finset.sum_congr rfl (fun u _ => hterm u), Finset.sum_neg_distrib]
  congr 1
  exact Equiv.sum_comp (Equiv.addRight (half n)) (fun u => y u * ω ^ u.val)

theorem H4_QQ_ge {e : ℕ} (hne : n = 2 ^ e) (he : 3 ≤ e) : 3 ≤ QQ n := by
  obtain ⟨t, ht1, hnt⟩ := H4_shape hne he
  unfold QQ
  calc 3 = 3 ^ 1 := by norm_num
    _ ≤ 3 ^ (n / 4) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- Step 2, first half, for `y` a solution: `θ = ŷ(ξ_0) ≠ 0` and `θ^{Q-1} = -1`. -/
theorem H4_NF_theta {e : ℕ} (hne : n = 2 ^ e) (he : 3 ≤ e) {K : Type*} [Field K] [CharP K 3] {ξ0 : K}
    (hξ0 : IsPrimitiveRoot ξ0 n) (y : ZMod n → K) (hL1 : L1 3 ((2 : ℕ) : ℤ) y) (hL3 : L3 0 y)
    (hRm : R y (half n) = 1) : dft ξ0 y 1 ≠ 0 ∧ dft ξ0 y 1 ^ (QQ n - 1) = -1 := by
  have hF3 := H4_NF_F3 hne he hξ0 y hL3 hRm 1
  have h0 : dft ξ0 y 1 ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hF3
    exact pow_ne_zero _ (pow_ne_zero _ (hξ0.ne_zero (NeZero.ne n))) hF3.symm
  exact ⟨h0, H4_theta_of (H4_QQ_pos n) h0 (H4_frob hne he hξ0 y hL1)⟩

end NF

theorem thm_3_1_step2_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) :
    (∀ y ∈ NFSet n 2, dft ξ0 y 1 ≠ 0 ∧ dft ξ0 y 1 ^ (QQ n - 1) = -1) ∧
    ∀ θ : GaloisField 3 (n / 2), θ ^ (QQ n - 1) = -1 →
      (∀ k : ℕ, ξ0 ^ (2 * (k + 1) * 3 ^ (k + 1)) * θ ^ (3 ^ (k + 1)) =
        (ξ0 ^ (3 ^ k)) ^ 6 * (ξ0 ^ (2 * k * 3 ^ k) * θ ^ (3 ^ k)) ^ 3) ∧
      (∀ k : ℕ, ξ0 ^ (2 * (k + n / 4) * 3 ^ (k + n / 4)) * θ ^ (3 ^ (k + n / 4)) = ξ0 ^ (2 * k * 3 ^ k) * θ ^ (3 ^ k)) ∧
      (∀ k : ℕ, -1 / (ξ0 ^ (2 * (k + 1) * 3 ^ (k + 1)) * θ ^ (3 ^ (k + 1))) =
        ((ξ0 ^ (3 ^ k))⁻¹) ^ 6 * (-1 / (ξ0 ^ (2 * k * 3 ^ k) * θ ^ (3 ^ k))) ^ 3) := by
  obtain ⟨t, ht1, hnt⟩ := H4_shape hne he
  have hn : Even n := ⟨4 * t, by omega⟩
  have h4 : 4 ∣ n := ⟨2 * t, by omega⟩
  have hm : ξ0 ^ (n / 2) = -1 := H4_pow_half hξ0 hn (by omega)
  refine ⟨?_, ?_⟩
  · intro y hy
    obtain ⟨hL1, hL3, hRm, _⟩ := hy
    exact H4_NF_theta hne he hξ0 y hL1 hL3 hRm
  · intro θ hθ
    exact ⟨fun k => H4_step2a ξ0 θ k,
      fun k => H4_step2b h4 hξ0.pow_eq_one hm (H4_three_pow_quarter hne he) hθ k,
      fun k => H4_step2c ξ0 θ k⟩

/-! ## Part G — the layer recursion as a fixed point (Steps 3-4 of the paper, s3_pow2.tex:37-57)

`H4_Gam top s c g` puts `top` on the top layer (odd `k`), `c` at `0`, and `s · g(z) · g(z + n/2)` at an even `k ≠ 0`,
where `z = k.val / 2` (so `2z = k`). Its iterates stabilise after `e` rounds; the result is its unique fixed point. -/

section Gam

variable {n : ℕ} [NeZero n] {K : Type*}

open Classical in
noncomputable def H4_Gam [Mul K] (top : ZMod n → K) (s c : K) (g : ZMod n → K) : ZMod n → K := fun k =>
  if Odd k.val then top k else if k = 0 then c else
    s * g ((k.val / 2 : ℕ) : ZMod n) * g (((k.val / 2 : ℕ) : ZMod n) + half n)

open Classical in
theorem H4_Gam_apply [Mul K] (top : ZMod n → K) (s c : K) (g : ZMod n → K) (k : ZMod n) :
    H4_Gam top s c g k = if Odd k.val then top k else if k = 0 then c else
      s * g ((k.val / 2 : ℕ) : ZMod n) * g (((k.val / 2 : ℕ) : ZMod n) + half n) := rfl

noncomputable def H4_fix [Mul K] (e : ℕ) (top : ZMod n → K) (s c : K) : ZMod n → K :=
  (H4_Gam top s c)^[e] (fun _ => c)

theorem H4_hf_val (k : ZMod n) : (((k.val / 2 : ℕ) : ZMod n)).val = k.val / 2 := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (ZMod.val_lt k))]

theorem H4_two_mul_hf (k : ZMod n) (hk : ¬ Odd k.val) : 2 * ((k.val / 2 : ℕ) : ZMod n) = k := by
  have he : 2 * (k.val / 2) = k.val := Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hk))
  calc 2 * ((k.val / 2 : ℕ) : ZMod n) = ((2 * (k.val / 2) : ℕ) : ZMod n) := by push_cast; ring
    _ = k := by rw [he, ZMod.natCast_zmod_val]

theorem H4_layer_hf {e : ℕ} (hne : n = 2 ^ e) (i : ℕ) (hi : i + 1 ≤ e) (k : ZMod n) (hk : ¬ Odd k.val)
    (hdiv : ¬ 2 ^ (i + 1) ∣ k.val) :
    ¬ 2 ^ i ∣ (((k.val / 2 : ℕ) : ZMod n)).val ∧ ¬ 2 ^ i ∣ (((k.val / 2 : ℕ) : ZMod n) + half n).val := by
  have hev : 2 ∣ k.val := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hk)
  have hkv : k.val / 2 * 2 = k.val := Nat.div_mul_cancel hev
  have hA : ¬ 2 ^ i ∣ k.val / 2 := by
    intro hd; apply hdiv; rw [pow_succ, ← hkv]; exact Nat.mul_dvd_mul_right hd 2
  have hlt := ZMod.val_lt k
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have hn2 : n / 2 = 2 ^ e' := by
    rw [hne, pow_succ]; exact Nat.mul_div_cancel _ (by norm_num)
  have hnn : n = 2 * 2 ^ e' := by rw [hne, pow_succ]; ring
  refine ⟨by rw [H4_hf_val]; exact hA, ?_⟩
  rw [ZMod.val_add, H4_hf_val, H4_half_val]
  have hsum : k.val / 2 + n / 2 < n := by omega
  rw [Nat.mod_eq_of_lt hsum]
  intro hd
  apply hA
  have h2i : 2 ^ i ∣ n / 2 := by rw [hn2]; exact pow_dvd_pow 2 (by omega)
  exact (Nat.dvd_add_left h2i).mp hd

theorem H4_Gam_agree [Mul K] {e : ℕ} (hne : n = 2 ^ e) (top : ZMod n → K) (s c : K) :
    ∀ i, i ≤ e → ∀ (g g' : ZMod n → K) (k : ZMod n), ¬ 2 ^ i ∣ k.val →
      (H4_Gam top s c)^[i] g k = (H4_Gam top s c)^[i] g' k := by
  intro i
  induction i with
  | zero => intro _ g g' k hk; exact absurd (by simp) hk
  | succ i ih =>
    intro hi g g' k hk
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', H4_Gam_apply, H4_Gam_apply]
    split_ifs with hodd hk0
    · rfl
    · rfl
    · obtain ⟨h1, h2⟩ := H4_layer_hf hne i hi k hodd hk
      rw [ih (by omega) g g' _ h1, ih (by omega) g g' _ h2]

theorem H4_Gam_zero [Mul K] (top : ZMod n → K) (s c : K) (g : ZMod n → K) : H4_Gam top s c g 0 = c := by
  unfold H4_Gam; simp

theorem H4_nonzero_ndvd {e : ℕ} (hne : n = 2 ^ e) (k : ZMod n) (hk : k ≠ 0) : ¬ 2 ^ e ∣ k.val := by
  intro hd
  have hlt : k.val < 2 ^ e := by have := ZMod.val_lt k; omega
  exact hk ((ZMod.val_eq_zero k).mp (Nat.eq_zero_of_dvd_of_lt hd hlt))

theorem H4_fix_eq [Mul K] {e : ℕ} (hne : n = 2 ^ e) (he : 1 ≤ e) (top : ZMod n → K) (s c : K) :
    H4_Gam top s c (H4_fix e top s c) = H4_fix e top s c := by
  funext k
  by_cases hk : k = 0
  · subst hk
    rw [H4_Gam_zero]; unfold H4_fix
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    rw [Function.iterate_succ_apply', H4_Gam_zero]
  · unfold H4_fix
    rw [← Function.iterate_succ_apply' (H4_Gam top s c), Function.iterate_succ_apply]
    exact H4_Gam_agree hne top s c e le_rfl _ _ k (H4_nonzero_ndvd hne k hk)

theorem H4_fix_unique [Mul K] {e : ℕ} (hne : n = 2 ^ e) (he : 1 ≤ e) (top : ZMod n → K) (s c : K)
    (g : ZMod n → K) (hg : H4_Gam top s c g = g) : g = H4_fix e top s c := by
  funext k
  by_cases hk : k = 0
  · subst hk
    rw [← hg, H4_Gam_zero, ← H4_fix_eq hne he, H4_Gam_zero]
  · rw [← Function.iterate_fixed hg e]
    exact H4_Gam_agree hne top s c e le_rfl _ _ k (H4_nonzero_ndvd hne k hk)

end Gam

/-! ## Part H — the top layer: odd residues are `±3^j` (from Step 1), and the values `t_j`, `-1/t_j` -/

section Top

variable {n : ℕ} [NeZero n] {K : Type*} [Field K]

open Classical in
noncomputable def H4_top (ξ0 θ : K) (k : ZMod n) : K :=
  if hk : ∃ j : ℕ, k = (3 : ZMod n) ^ j then H4_t ξ0 θ hk.choose
  else if hk' : ∃ j : ℕ, k = -(3 : ZMod n) ^ j then -1 / H4_t ξ0 θ hk'.choose else 0

theorem H4_top_pos {ξ0 θ : K} (hwd : ∀ i j : ℕ, (3 : ZMod n) ^ i = 3 ^ j → H4_t ξ0 θ i = H4_t ξ0 θ j)
    (j : ℕ) : H4_top ξ0 θ ((3 : ZMod n) ^ j) = H4_t ξ0 θ j := by
  have hex : ∃ i : ℕ, (3 : ZMod n) ^ j = 3 ^ i := ⟨j, rfl⟩
  unfold H4_top; rw [dite_eq_left hex]
  exact hwd _ _ hex.choose_spec.symm

theorem H4_top_neg {ξ0 θ : K} (hwd : ∀ i j : ℕ, (3 : ZMod n) ^ i = 3 ^ j → H4_t ξ0 θ i = H4_t ξ0 θ j)
    (hdisj : ∀ i j : ℕ, -(3 : ZMod n) ^ j ≠ 3 ^ i) (j : ℕ) :
    H4_top ξ0 θ (-(3 : ZMod n) ^ j) = -1 / H4_t ξ0 θ j := by
  have hn1 : ¬ ∃ i : ℕ, -(3 : ZMod n) ^ j = 3 ^ i := fun ⟨i, hi⟩ => hdisj i j hi
  have hex : ∃ i : ℕ, -(3 : ZMod n) ^ j = -3 ^ i := ⟨j, rfl⟩
  unfold H4_top; rw [dite_eq_right hn1, dite_eq_left hex]
  rw [hwd hex.choose j (neg_inj.mp hex.choose_spec).symm]

theorem H4_t_periodic {p : ℕ} {ξ0 θ : K} (hwrap : ∀ k, H4_t ξ0 θ (k + p) = H4_t ξ0 θ k) :
    ∀ q r, H4_t ξ0 θ (r + p * q) = H4_t ξ0 θ r := by
  intro q; induction q with
  | zero => intro r; simp
  | succ q ih => intro r; rw [mul_add_one, ← add_assoc, hwrap, ih]

theorem H4_t_wd {ξ0 θ : K} (hord : orderOf (3 : ZMod n) = n / 4) (hpos : 0 < n / 4)
    (hwrap : ∀ k, H4_t ξ0 θ (k + n / 4) = H4_t ξ0 θ k) :
    ∀ i j : ℕ, (3 : ZMod n) ^ i = 3 ^ j → H4_t ξ0 θ i = H4_t ξ0 θ j := by
  intro i j hij
  have hfin : IsOfFinOrder (3 : ZMod n) := orderOf_pos_iff.mp (by rw [hord]; exact hpos)
  have hmod := hfin.pow_inj_mod.mp hij
  rw [hord] at hmod
  rw [← Nat.mod_add_div i (n / 4), ← Nat.mod_add_div j (n / 4), H4_t_periodic hwrap, H4_t_periodic hwrap, hmod]

theorem H4_odd_cases (horb : ∀ x : ZMod n, Odd x.val → orbit 3 x = orbit 3 1 ∨ orbit 3 x = inv (orbit 3 1))
    (x : ZMod n) (hx : Odd x.val) : ∃ j : ℕ, x = (3 : ZMod n) ^ j ∨ x = -(3 : ZMod n) ^ j := by
  have hself : x ∈ orbit 3 x := by
    unfold orbit; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨0, by simp⟩
  rcases horb x hx with h | h
  · rw [h] at hself
    unfold orbit at hself; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hself
    obtain ⟨j, hj⟩ := hself
    exact ⟨j, Or.inl (by simpa using hj)⟩
  · rw [h] at hself
    unfold Xia.inv orbit at hself
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hself
    obtain ⟨w, ⟨j, hj⟩, hw⟩ := hself
    exact ⟨j, Or.inr (by rw [← hw, hj]; simp)⟩

theorem H4_neg_ne (hdisj : Disjoint (orbit 3 (1 : ZMod n)) (inv (orbit 3 1))) (i j : ℕ) :
    -(3 : ZMod n) ^ j ≠ 3 ^ i := by
  intro h
  have h1 : (3 : ZMod n) ^ i ∈ orbit 3 (1 : ZMod n) := by
    unfold orbit; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨i, by simp⟩
  have h2 : (3 : ZMod n) ^ i ∈ inv (orbit 3 (1 : ZMod n)) := by
    unfold Xia.inv; rw [Finset.mem_image]; refine ⟨3 ^ j, ?_, h⟩
    unfold orbit; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨j, by simp⟩
  exact Finset.disjoint_left.mp hdisj h1 h2

theorem H4_odd_val_pow3 (hn : Even n) (j : ℕ) : Odd ((3 : ZMod n) ^ j).val := by
  rw [show (3 : ZMod n) ^ j = ((3 ^ j : ℕ) : ZMod n) by push_cast; rfl, ZMod.val_natCast, Nat.odd_iff,
    Nat.mod_mod_of_dvd _ (even_iff_two_dvd.mp hn), ← Nat.odd_iff]
  exact Odd.pow (by decide)

theorem H4_odd_val_neg (hn : Even n) (x : ZMod n) (hx : Odd x.val) : Odd (-x).val := by
  have hx0 : x ≠ 0 := by intro h0; rw [h0, ZMod.val_zero] at hx; exact absurd hx (by decide)
  rw [ZMod.neg_val, ite_eq_right hx0]
  have := ZMod.val_lt x
  obtain ⟨r, hr⟩ := hn; obtain ⟨q, hq⟩ := hx
  exact ⟨r - q - 1, by omega⟩

theorem H4_E3 {ω : K} (hω1 : ω ^ n = 1) (j : ℕ) : ω ^ ((3 : ZMod n) ^ j).val = ω ^ (3 ^ j) := by
  rw [← H4_pow_val_natCast hω1 (3 ^ j)]; push_cast; rfl

theorem H4_three_mul_ne {e : ℕ} (hne : n = 2 ^ e) (he : 3 ≤ e) (k : ZMod n) (hk : k ≠ 0) :
    (3 : ZMod n) * k ≠ 0 := by
  intro h0
  apply hk
  have hq := H4_three_pow_quarter hne he
  obtain ⟨t, ht1, hnt⟩ := H4_shape hne he
  calc k = (3 : ZMod n) ^ (n / 4) * k := by rw [hq, one_mul]
    _ = 3 ^ (n / 4 - 1) * (3 * k) := by rw [← mul_assoc, pow_sub_one_mul (by omega)]
    _ = 0 := by rw [h0, mul_zero]

end Top

/-! ## Part I — the Fourier side: every `h` with (F1),(F3),(F4) is the fixed point of its own parameters, and
the fixed point built from admissible parameters satisfies (F1),(F3),(F4) -/

section Fourier

variable {n : ℕ} [NeZero n] {K : Type*} [Field K]

theorem H4_F1_iff (ω : K) (h : ZMod n → K) :
    F1 3 2 ω h ↔ ∀ k : ZMod n, h (3 * k) = (ω ^ k.val) ^ 6 * h k ^ 3 := by
  have e6 : ∀ x : K, x ^ ((3 : ℤ) * 2) = x ^ 6 := by
    intro x; rw [show (3 : ℤ) * 2 = ((6 : ℕ) : ℤ) by norm_num, zpow_natCast]
  unfold F1
  simp only [Nat.cast_ofNat, e6]

theorem H4_F1_iter {ω : K} (hω1 : ω ^ n = 1) {h : ZMod n → K}
    (hF1 : ∀ k : ZMod n, h (3 * k) = (ω ^ k.val) ^ 6 * h k ^ 3) :
    ∀ (j : ℕ) (k : ZMod n), h ((3 : ZMod n) ^ j * k) = (ω ^ k.val) ^ (2 * j * 3 ^ j) * h k ^ (3 ^ j) := by
  intro j
  induction j with
  | zero => intro k; simp
  | succ j ih =>
    intro k
    have hx : ω ^ ((3 : ZMod n) ^ j * k).val = (ω ^ k.val) ^ (3 ^ j) := by
      rw [H4_pow_val_mul_nat hω1 k (3 ^ j)]; congr 2; push_cast; ring
    rw [show (3 : ZMod n) ^ (j + 1) * k = 3 * (3 ^ j * k) by ring, hF1, ih, hx, H4_step2a]

theorem H4_pow3_half {ξ0 : K} (hm : ξ0 ^ (n / 2) = -1) (j : ℕ) : (ξ0 ^ (3 ^ j)) ^ (n / 2) = -1 := by
  rw [← pow_mul, mul_comm (3 ^ j) (n / 2), pow_mul, hm, Odd.neg_one_pow (Odd.pow (by decide))]

theorem H4_pow_one_val {ω : K} (hω1 : ω ^ n = 1) : ω ^ (1 : ZMod n).val = ω := by
  rw [← Nat.cast_one, H4_pow_val_natCast hω1, pow_one]

/-- For `h` with (F1),(F3): `h(1)^{Q-1} = -1` (Step 2 on the Fourier side). -/
theorem H4_G_theta {e : ℕ} (hne : n = 2 ^ e) (he : 3 ≤ e) {ω : K} (hω : IsPrimitiveRoot ω n)
    {h : ZMod n → K} (hF1 : ∀ k : ZMod n, h (3 * k) = (ω ^ k.val) ^ 6 * h k ^ 3) (hF3 : F3 ω h) :
    h 1 ^ (QQ n - 1) = -1 := by
  obtain ⟨t, ht1, hnt⟩ := H4_shape hne he
  have hn : Even n := ⟨4 * t, by omega⟩
  have hω1 := hω.pow_eq_one
  have hm : ω ^ (n / 2) = -1 := H4_pow_half hω hn (by omega)
  have hv1 := H4_pow_one_val (n := n) hω1
  have hit := H4_F1_iter hω1 hF1 (n / 4) 1
  rw [H4_three_pow_quarter hne he, one_mul, hv1] at hit
  have hQ : h 1 ^ QQ n = -h 1 := by
    have e1 : ω ^ (2 * (n / 4) * 3 ^ (n / 4)) = -1 := by
      rw [show 2 * (n / 4) = n / 2 by omega, pow_mul, hm, Odd.neg_one_pow (Odd.pow (by decide))]
    rw [e1] at hit; unfold QQ; linear_combination hit
  have h0 : h 1 ≠ 0 := by
    intro h0; have := hF3 1; rw [h0, zero_mul, hv1, hm] at this; norm_num at this
  exact H4_theta_of (H4_QQ_pos n) h0 hQ

/-- Uniqueness half: a function with (F1),(F3),(F4) is the fixed point of the layer recursion with parameters
`(h(1), h(-1), h(1 ↦ 0))`, i.e. `(θ, S, ŷ(1))`. -/
theorem H4_G_fixed {e : ℕ} (hne : n = 2 ^ e) (he : 3 ≤ e) {ξ0 : K} (hξ0 : IsPrimitiveRoot ξ0 n)
    (horb : ∀ x : ZMod n, Odd x.val → orbit 3 x = orbit 3 1 ∨ orbit 3 x = inv (orbit 3 1))
    (hdisj' : ∀ i j : ℕ, -(3 : ZMod n) ^ j ≠ 3 ^ i) {h : ZMod n → K}
    (hwd : ∀ i j : ℕ, (3 : ZMod n) ^ i = 3 ^ j → H4_t ξ0 (h 1) i = H4_t ξ0 (h 1) j)
    (hF1 : F1 3 2 ξ0 h) (hF3 : F3 ξ0 h) (hF4 : F4 h) :
    H4_Gam (H4_top ξ0 (h 1)) (h (half n)) (h 0) h = h := by
  obtain ⟨t, ht1, hnt⟩ := H4_shape hne he
  have hn : Even n := ⟨4 * t, by omega⟩
  have hω1 := hξ0.pow_eq_one
  have hm : ξ0 ^ (n / 2) = -1 := H4_pow_half hξ0 hn (by omega)
  have hF1' := (H4_F1_iff ξ0 h).mp hF1
  have hm2 : h (half n) ^ 2 = 1 := (thm_3_1_step4_proved n e hne he ξ0 hξ0 h hF3).2.2.2
  have hpos : ∀ j : ℕ, h ((3 : ZMod n) ^ j) = H4_t ξ0 (h 1) j := by
    intro j
    have := H4_F1_iter hω1 hF1' j 1
    rw [mul_one, H4_pow_one_val hω1] at this
    rw [this]; rfl
  have hneg : ∀ j : ℕ, h (-(3 : ZMod n) ^ j) = -1 / H4_t ξ0 (h 1) j := by
    intro j
    have h3 := hF3 ((3 : ZMod n) ^ j)
    rw [H4_E3 hω1, H4_pow3_half hm, hpos] at h3
    have hne0 : H4_t ξ0 (h 1) j ≠ 0 := by intro h0; rw [h0, zero_mul] at h3; norm_num at h3
    rw [eq_div_iff hne0, mul_comm]; exact h3
  funext k
  rw [H4_Gam_apply]
  split_ifs with hodd hk0
  · obtain ⟨j, hj | hj⟩ := H4_odd_cases horb k hodd
    · rw [hj, H4_top_pos hwd, hpos]
    · rw [hj, H4_top_neg hwd hdisj', hneg]
  · rw [hk0]
  · have h2z := H4_two_mul_hf k hodd
    have h4z := hF4 ((k.val / 2 : ℕ) : ZMod n)
    rw [h2z] at h4z
    linear_combination (h (half n)) * h4z + h k * hm2

/-- Existence half: the fixed point built from `(θ, s, c)` with `θ^{Q-1} = -1`, `s^2 = c^2 = 1` satisfies
(F1),(F3),(F4) and has parameters `(θ, s, c)`. -/
theorem H4_fix_props {e : ℕ} (hne : n = 2 ^ e) (he : 3 ≤ e) {ξ0 : K} (hξ0 : IsPrimitiveRoot ξ0 n)
    (horb : ∀ x : ZMod n, Odd x.val → orbit 3 x = orbit 3 1 ∨ orbit 3 x = inv (orbit 3 1))
    (hdisj' : ∀ i j : ℕ, -(3 : ZMod n) ^ j ≠ 3 ^ i)
    {θ s c : K} (hwd : ∀ i j : ℕ, (3 : ZMod n) ^ i = 3 ^ j → H4_t ξ0 θ i = H4_t ξ0 θ j)
    (hθ : θ ^ (QQ n - 1) = -1) (hs : s ^ 2 = 1) (hc : c ^ 2 = 1) :
    F1 3 2 ξ0 (H4_fix e (H4_top (n := n) ξ0 θ) s c) ∧ F3 ξ0 (H4_fix e (H4_top (n := n) ξ0 θ) s c) ∧
      F4 (H4_fix e (H4_top (n := n) ξ0 θ) s c) ∧ H4_fix e (H4_top (n := n) ξ0 θ) s c 1 = θ ∧
      H4_fix e (H4_top (n := n) ξ0 θ) s c (half n) = s ∧ H4_fix e (H4_top (n := n) ξ0 θ) s c 0 = c := by
  have hfix : H4_Gam (H4_top (n := n) ξ0 θ) s c (H4_fix e (H4_top (n := n) ξ0 θ) s c) =
      H4_fix e (H4_top (n := n) ξ0 θ) s c := H4_fix_eq hne (by omega) _ s c
  generalize H4_fix e (H4_top (n := n) ξ0 θ) s c = h at hfix ⊢
  obtain ⟨t, ht1, hnt⟩ := H4_shape hne he
  have hn : Even n := ⟨4 * t, by omega⟩
  have h4 : 4 ∣ n := ⟨2 * t, by omega⟩
  have h3n : 3 ≤ n := by omega
  have hω1 : ξ0 ^ n = 1 := hξ0.pow_eq_one
  have hm : ξ0 ^ (n / 2) = -1 := H4_pow_half hξ0 hn (by omega)
  -- the fixed-point equation, read off at odd `k`, at `0`, and at `2z ≠ 0`
  have hP1 : ∀ k : ZMod n, Odd k.val → h k = H4_top ξ0 θ k := by
    intro k hk; rw [← hfix, H4_Gam_apply, ite_eq_left hk]
  have hP0 : h 0 = c := by rw [← hfix, H4_Gam_zero]
  have hP2 : ∀ z : ZMod n, 2 * z ≠ 0 → h (2 * z) = s * h z * h (z + half n) := by
    intro z hz
    have h2val : (2 : ZMod n).val = 2 := by
      rw [show (2 : ZMod n) = ((2 : ℕ) : ZMod n) by norm_num, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have hnodd : ¬ Odd (2 * z).val := by
      rw [Nat.not_odd_iff_even, ZMod.val_mul, h2val, Nat.even_iff,
        Nat.mod_mod_of_dvd _ (even_iff_two_dvd.mp hn)]
      omega
    have hfz := congrFun hfix (2 * z)
    rw [H4_Gam_apply, ite_eq_right hnodd, ite_eq_right hz] at hfz
    have hw2 := H4_two_mul_hf (2 * z) hnodd
    have hdiff : 2 * ((((2 * z).val / 2 : ℕ) : ZMod n) - z) = 0 := by rw [mul_sub, hw2, sub_self]
    rcases H4_two_mul_eq_zero hn h3n _ hdiff with hd | hd
    · rw [sub_eq_zero] at hd; rw [← hfz, hd]
    · rw [sub_eq_iff_eq_add] at hd
      rw [← hfz, hd, show half n + z + half n = z by
        rw [add_comm (half n) z, add_assoc, H4_half_add_half hn, add_zero], add_comm (half n) z]
      ring
  -- the values on the top layer
  have hθ0 : θ ≠ 0 := by
    intro h0; rw [h0, zero_pow (by have := H4_QQ_ge hne he; omega)] at hθ; norm_num at hθ
  have ht0 : ∀ j, H4_t ξ0 θ j ≠ 0 := fun j =>
    mul_ne_zero (pow_ne_zero _ (hξ0.ne_zero (NeZero.ne n))) (pow_ne_zero _ hθ0)
  have hpos : ∀ j : ℕ, h ((3 : ZMod n) ^ j) = H4_t ξ0 θ j := by
    intro j; rw [hP1 _ (H4_odd_val_pow3 hn j), H4_top_pos hwd]
  have hneg : ∀ j : ℕ, h (-(3 : ZMod n) ^ j) = -1 / H4_t ξ0 θ j := by
    intro j; rw [hP1 _ (H4_odd_val_neg hn _ (H4_odd_val_pow3 hn j)), H4_top_neg hwd hdisj']
  have hE3h : ∀ j : ℕ, (ξ0 ^ (3 ^ j)) ^ (n / 2) = -1 := H4_pow3_half hm
  have hE3n : ∀ j : ℕ, ξ0 ^ (-(3 : ZMod n) ^ j).val = (ξ0 ^ (3 ^ j))⁻¹ := by
    intro j; rw [H4_pow_val_neg hω1, H4_E3 hω1]
  -- (F1) and (F3) layer by layer (Step 3 of the paper)
  have hP4 : ∀ i, i ≤ e → ∀ k : ZMod n, ¬ 2 ^ i ∣ k.val →
      h (3 * k) = (ξ0 ^ k.val) ^ 6 * h k ^ 3 ∧ h k * h (-k) = (ξ0 ^ k.val) ^ (n / 2) := by
    intro i
    induction i with
    | zero => intro _ k hk; exact absurd (by simp) hk
    | succ i ih =>
      intro hi k hk
      by_cases hodd : Odd k.val
      · obtain ⟨j, hj | hj⟩ := H4_odd_cases horb k hodd
        · subst hj
          rw [show (3 : ZMod n) * 3 ^ j = 3 ^ (j + 1) by ring, hpos, hpos, hneg, H4_E3 hω1]
          refine ⟨H4_step2a ξ0 θ j, ?_⟩
          rw [hE3h]; field_simp [ht0 j]
        · subst hj
          rw [show (3 : ZMod n) * -3 ^ j = -3 ^ (j + 1) by ring, neg_neg, hneg, hneg, hpos, hE3n]
          refine ⟨H4_step2c ξ0 θ j, ?_⟩
          rw [inv_pow, hE3h]; field_simp [ht0 j]
      · have hk0 : k ≠ 0 := by intro h0; apply hk; rw [h0, ZMod.val_zero]; exact dvd_zero _
        obtain ⟨hz1, hz2⟩ := H4_layer_hf hne i hi k hodd hk
        have h2z := H4_two_mul_hf k hodd
        generalize ((k.val / 2 : ℕ) : ZMod n) = z at hz1 hz2 h2z
        obtain ⟨a1, a3⟩ := ih (by omega) z hz1
        obtain ⟨b1, b3⟩ := ih (by omega) (z + half n) hz2
        obtain ⟨c1, c3⟩ := thm_3_1_step3_proved n h4 ξ0 hξ0 h s hs z
          (by
            intro w hw
            rcases Set.mem_insert_iff.mp hw with rfl | hw
            · exact a1
            · rw [Set.mem_singleton_iff] at hw; subst hw; exact b1)
          (by
            intro w hw
            rcases Set.mem_insert_iff.mp hw with rfl | hw
            · exact a3
            · rw [Set.mem_singleton_iff] at hw; subst hw; exact b3)
        have hk' : h k = s * h z * h (z + half n) := by
          rw [← h2z]; exact hP2 z (by rw [h2z]; exact hk0)
        have h3k : h (3 * k) = s * h (3 * z) * h (3 * z + half n) := by
          rw [← h2z, show (3 : ZMod n) * (2 * z) = 2 * (3 * z) by ring]
          exact hP2 _ (by rw [show (2 : ZMod n) * (3 * z) = 3 * (2 * z) by ring, h2z];
                          exact H4_three_mul_ne hne he k hk0)
        have hmk : h (-k) = s * h (-z) * h (-z + half n) := by
          rw [← h2z, show -(2 * z) = 2 * (-z) by ring]
          exact hP2 _ (by rw [show (2 : ZMod n) * -z = -(2 * z) by ring, h2z]; exact neg_ne_zero.mpr hk0)
        rw [h2z] at c1 c3
        exact ⟨by rw [h3k, hk', c1], by rw [hk', hmk, c3]⟩
  have hall : ∀ k : ZMod n, h (3 * k) = (ξ0 ^ k.val) ^ 6 * h k ^ 3 ∧ h k * h (-k) = (ξ0 ^ k.val) ^ (n / 2) := by
    intro k
    by_cases hk0 : k = 0
    · subst hk0
      simp only [mul_zero, neg_zero, H4_pow_val_zero, one_pow, one_mul, hP0]
      exact ⟨by rw [pow_succ, hc, one_mul], by rw [← sq, hc]⟩
    · exact hP4 e le_rfl k (H4_nonzero_ndvd hne k hk0)
  have hF3 : F3 ξ0 h := fun k => (hall k).2
  -- `h(-1) = S` (Step 4)
  have hhm : h (half n) = s := by
    have hι : 2 * ((n / 4 : ℕ) : ZMod n) = half n := by
      unfold half; rw [show n / 2 = 2 * (n / 4) by omega]; push_cast; ring
    have := hP2 ((n / 4 : ℕ) : ZMod n) (by rw [hι]; exact H4_half_ne_zero (by omega))
    rw [hι] at this
    have h1 := (thm_3_1_step4_proved n e hne he ξ0 hξ0 h hF3).1
    rw [this]; linear_combination s * h1
  refine ⟨(H4_F1_iff ξ0 h).mpr (fun k => (hall k).1), hF3, ?_, ?_, hhm, hP0⟩
  · intro k
    by_cases h2k : 2 * k = 0
    · rcases H4_two_mul_eq_zero hn h3n k h2k with rfl | rfl
      · rw [zero_add, mul_zero]; ring
      · rw [two_mul]
    · rw [hP2 k h2k, hhm]; linear_combination (-(h k * h (k + half n))) * hs
  · have := hpos 0
    rw [pow_zero] at this
    rw [this]; simp [H4_t]

end Fourier

/-! ## Part J — Section 2.2 for `n = 2^e`, `e` odd (Xia's system = norm-free system + two norms) -/

section Xia22

variable {n : ℕ} [NeZero n]

theorem H4_R_of_L2 {K : Type*} [CommRing K] (hn : Even n) (y : ZMod n → K) (hL2 : L2 (-1) y) :
    R y (half n) = -(n : K) := by
  unfold R
  have hterm : ∀ t : ZMod n, y t * y (t + half n) = -1 := by
    intro t
    by_cases ht : t.val < n / 2
    · exact hL2 t ht
    · have ht' : (t + half n).val < n / 2 := by
        rw [ZMod.val_add, H4_half_val]
        have := ZMod.val_lt t
        obtain ⟨r, hr⟩ := hn
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
      have := hL2 (t + half n) ht'
      rw [add_assoc, H4_half_add_half hn, add_zero] at this
      rw [mul_comm]; exact this
  rw [Finset.sum_congr rfl (fun t _ => hterm t), Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  ring

theorem H4_neg_n_eq_one {e : ℕ} (hne : n = 2 ^ e) (heo : Odd e) {K : Type*} [Field K] [CharP K 3] :
    -(n : K) = 1 := by
  have h3 : ((3 : ℕ) : K) = 0 := CharP.cast_eq_zero K 3
  have h2 : (2 : K) = -1 := by push_cast at h3; linear_combination h3
  rw [hne]; push_cast; rw [h2, heo.neg_one_pow]; ring

theorem H4_xia_to_nf {e : ℕ} (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e)
    (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ XiaSet n 2) : y ∈ NFSet n 2 := by
  obtain ⟨t, ht1, hnt⟩ := H4_shape hne he
  have hn : Even n := ⟨4 * t, by omega⟩
  obtain ⟨hL1, hL2, hL3, hL4⟩ := hy
  exact ⟨hL1, hL3, by rw [H4_R_of_L2 hn y hL2, H4_neg_n_eq_one hne heo], hL4⟩

theorem H4_xia_norms {e : ℕ} (hne : n = 2 ^ e) (he : 3 ≤ e)
    (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ XiaSet n 2) : Nm n (y 0) = -1 ∧ Nm n (y 1) = -1 := by
  obtain ⟨t, ht1, hnt⟩ := H4_shape hne he
  obtain ⟨hL1, hL2, -, -⟩ := hy
  have h1v : (1 : ZMod n).val = 1 := by rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, ?_⟩
  · rw [H4_nm_eq hne he y hL1]; exact hL2 0 (by rw [ZMod.val_zero]; omega)
  · rw [H4_nm_eq hne he y hL1]; exact hL2 1 (by rw [h1v]; omega)

theorem H4_nf_to_xia {e : ℕ} (hne : n = 2 ^ e) (he : 3 ≤ e)
    (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2) (h0 : Nm n (y 0) = -1) (h1 : Nm n (y 1) = -1) :
    y ∈ XiaSet n 2 := by
  obtain ⟨hL1, hL3, -, hL4⟩ := hy
  refine ⟨hL1, ?_, hL3, hL4⟩
  intro s _
  rw [← H4_nm_eq hne he y hL1 s]
  have hodd3 : ∀ a : ℕ, Odd (3 ^ a) := fun a => Odd.pow (by decide)
  obtain ⟨a, ha | ha⟩ := Nat.even_or_odd' s.val
  · have hs : s = 0 + ((2 * a : ℕ) : ZMod n) := by rw [zero_add, ← ha, ZMod.natCast_zmod_val]
    rw [hs, H4_L1_iter y hL1 a 0]
    unfold Nm at h0 ⊢
    rw [pow_right_comm, h0, (hodd3 a).neg_one_pow]
  · have hs : s = 1 + ((2 * a : ℕ) : ZMod n) := by
      rw [← ZMod.natCast_zmod_val s, ha]; push_cast; ring
    rw [hs, H4_L1_iter y hL1 a 1]
    unfold Nm at h1 ⊢
    rw [pow_right_comm, h1, (hodd3 a).neg_one_pow]

end Xia22

/-! ## Part K — Theorem 3.1 (bijection and count) and Corollary 3.2 -/

theorem H4_one_ne_neg_one {K : Type*} [Field K] [CharP K 3] : (1 : K) ≠ -1 := by
  intro h
  have h2 : ((2 : ℕ) : K) = 0 := by push_cast; linear_combination h
  rw [CharP.cast_eq_zero_iff K 3] at h2
  norm_num at h2

theorem H4_dftA_eq {n : ℕ} [NeZero n] (ξ0 : GaloisField 3 (n / 2)) (y : ZMod n → GaloisField 3 (n / 2)) :
    dftA ξ0 y = dft ξ0 y := by
  funext k; simp only [dftA, Algebra.algebraMap_self, RingHom.id_apply]

/-- Glue for linking: `n = 2^e`, `e ≥ 3` gives the hypotheses `Even n`, `¬ 3 ∣ n` of Proposition 2.4. -/
theorem H4_even_of_pow2 {n e : ℕ} (hne : n = 2 ^ e) (he : 3 ≤ e) : Even n := by
  obtain ⟨t, -, hnt⟩ := H4_shape hne he; exact ⟨4 * t, by omega⟩

theorem H4_not3_of_pow2 {n e : ℕ} (hne : n = 2 ^ e) : ¬ 3 ∣ n := by
  intro h; rw [hne] at h
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

/-- MapsTo, with no hypotheses: `(ŷ(ξ_0), S, ŷ(1))` of a solution lies in the target set. -/
theorem H4_mapsTo {n e : ℕ} [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2) :
    paramMap n ξ0 y ∈ ({θ | θ ^ (QQ n - 1) = -1} ×ˢ (({1, -1} : Set (GaloisField 3 (n / 2))) ×ˢ {1, -1})) := by
  obtain ⟨t, ht1, hnt⟩ := H4_shape hne he
  have hn : Even n := ⟨4 * t, by omega⟩
  obtain ⟨hL1, hL3, hRm, _⟩ := hy
  have hF3 := H4_NF_F3 hne he hξ0 y hL3 hRm
  obtain ⟨_, h00, _, hmm⟩ := thm_3_1_step4_proved n e hne he ξ0 hξ0 (dft ξ0 y) hF3
  rw [H4_S_eq_dft hn (by omega) hξ0] at hmm
  simp only [paramMap, Set.mem_prod, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact ⟨(H4_NF_theta hne he hξ0 y hL1 hL3 hRm).2, sq_eq_one_iff.mp hmm, sq_eq_one_iff.mp h00⟩

/-- Theorem 3.1, bijection, parametrized by Proposition 2.4 (`hP24` = `prop_2_4_bij` with `L := F`, `ω := ξ0`)
and Step 1 (`hStep1` = `thm_3_1_step1 n e`). -/
theorem thm_3_1_bij_of (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n)
    (hP24 : Set.BijOn (dftA ξ0) (NFSet n 2) {h | F1 3 2 ξ0 h ∧ F3 ξ0 h ∧ F4 h})
    (hStep1 : padicValNat 2 (3 ^ (n / 2) - 1) = e + 1 ∧ padicValNat 2 (QQ n - 1) = e ∧
      orderOf (3 : ZMod n) = 2 ^ (e - 2) ∧
      (∀ x : ZMod n, IsUnit x → ∃ k : ℕ, x = (3 : ZMod n) ^ k ∨ x = -(3 : ZMod n) ^ k) ∧
      (∀ k : ℕ, (-1 : ZMod n) ≠ (3 : ZMod n) ^ k) ∧
      (∀ x : ZMod n, Odd x.val → orbit 3 x = orbit 3 1 ∨ orbit 3 x = inv (orbit 3 1)) ∧
      Disjoint (orbit 3 (1 : ZMod n)) (inv (orbit 3 1)) ∧
      ∀ (j : ℕ), 1 ≤ j → j ≤ e - 1 → ∀ x : ZMod n, addOrderOf x = 2 ^ j →
        ∃ z : ZMod n, addOrderOf z = 2 ^ (j + 1) ∧ {w : ZMod n | 2 * w = x} = {z, z + half n} ∧
          addOrderOf (z + half n) = 2 ^ (j + 1)) :
    Set.BijOn (paramMap n ξ0) (NFSet n 2)
      ({θ | θ ^ (QQ n - 1) = -1} ×ˢ (({1, -1} : Set (GaloisField 3 (n / 2))) ×ˢ {1, -1})) := by
  obtain ⟨-, -, hord, -, -, horb, hdisj, -⟩ := hStep1
  obtain ⟨t, ht1, hnt⟩ := H4_shape hne he
  have hn : Even n := ⟨4 * t, by omega⟩
  have h4 : 4 ∣ n := ⟨2 * t, by omega⟩
  have hm : ξ0 ^ (n / 2) = -1 := H4_pow_half hξ0 hn (by omega)
  have hdisj' := H4_neg_ne hdisj
  have hord' : orderOf (3 : ZMod n) = n / 4 := by
    rw [hord]
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 3 := ⟨e - 3, by omega⟩
    rw [show k + 3 - 2 = k + 1 by omega, hne, show 2 ^ (k + 3) = 2 ^ (k + 1) * 4 by ring,
      Nat.mul_div_cancel _ (by norm_num)]
  have hwd : ∀ θ : GaloisField 3 (n / 2), θ ^ (QQ n - 1) = -1 →
      ∀ i j : ℕ, (3 : ZMod n) ^ i = 3 ^ j → H4_t ξ0 θ i = H4_t ξ0 θ j := fun θ hθ =>
    H4_t_wd hord' (by omega) (fun k => H4_step2b h4 hξ0.pow_eq_one hm (H4_three_pow_quarter hne he) hθ k)
  refine ⟨fun y hy => H4_mapsTo hne he ξ0 hξ0 y hy, ?_, ?_⟩
  · intro y1 hy1 y2 hy2 heq
    apply hP24.injOn hy1 hy2
    have hG1 := hP24.mapsTo hy1
    have hG2 := hP24.mapsTo hy2
    rw [H4_dftA_eq] at hG1 hG2 ⊢
    rw [H4_dftA_eq]
    obtain ⟨a1, a3, a4⟩ := hG1
    obtain ⟨b1, b3, b4⟩ := hG2
    simp only [paramMap, Prod.mk.injEq] at heq
    obtain ⟨e1, eS, e0⟩ := heq
    rw [← H4_S_eq_dft hn (by omega) hξ0, ← H4_S_eq_dft hn (by omega) hξ0] at eS
    have fx1 := H4_G_fixed hne he hξ0 horb hdisj'
      (hwd _ (H4_G_theta hne he hξ0 ((H4_F1_iff _ _).mp a1) a3)) a1 a3 a4
    have fx2 := H4_G_fixed hne he hξ0 horb hdisj'
      (hwd _ (H4_G_theta hne he hξ0 ((H4_F1_iff _ _).mp b1) b3)) b1 b3 b4
    rw [← e1, ← eS, ← e0] at fx2
    exact (H4_fix_unique hne (by omega) _ _ _ _ fx1).trans (H4_fix_unique hne (by omega) _ _ _ _ fx2).symm
  · rintro ⟨θ, s, c⟩ hT
    simp only [Set.mem_prod, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hT
    obtain ⟨hθ, hs, hc⟩ := hT
    have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> ring
    have hc2 : c ^ 2 = 1 := by rcases hc with rfl | rfl <;> ring
    obtain ⟨f1, f3, f4, v1, vm, v0⟩ := H4_fix_props hne he hξ0 horb hdisj' (hwd θ hθ) hθ hs2 hc2
    obtain ⟨y, hy, hyh⟩ := hP24.surjOn ⟨f1, f3, f4⟩
    refine ⟨y, hy, ?_⟩
    rw [H4_dftA_eq] at hyh
    simp only [paramMap]
    rw [← H4_S_eq_dft hn (by omega) hξ0, hyh, v1, vm, v0]

/-- Theorem 3.1, count, parametrized by `thm_3_1_xi0` (D), `prop_2_4_bij` with `L := F` (A, for every primitive
`ω`), `thm_3_1_step1` (C) and `thm_3_1_theta_set` (E). -/
theorem thm_3_1_card_of (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e)
    (hXi0 : (∃ ξ0 : GaloisField 3 (n / 2), IsPrimitiveRoot ξ0 n) ∧
      ∀ ξ : GaloisField 3 (n / 2), ξ ^ n = 1 → ξ ^ QQ n = ξ)
    (hP24 : ∀ ω : GaloisField 3 (n / 2), IsPrimitiveRoot ω n →
      Set.BijOn (dftA ω) (NFSet n 2) {h | F1 3 2 ω h ∧ F3 ω h ∧ F4 h})
    (hStep1 : padicValNat 2 (3 ^ (n / 2) - 1) = e + 1 ∧ padicValNat 2 (QQ n - 1) = e ∧
      orderOf (3 : ZMod n) = 2 ^ (e - 2) ∧
      (∀ x : ZMod n, IsUnit x → ∃ k : ℕ, x = (3 : ZMod n) ^ k ∨ x = -(3 : ZMod n) ^ k) ∧
      (∀ k : ℕ, (-1 : ZMod n) ≠ (3 : ZMod n) ^ k) ∧
      (∀ x : ZMod n, Odd x.val → orbit 3 x = orbit 3 1 ∨ orbit 3 x = inv (orbit 3 1)) ∧
      Disjoint (orbit 3 (1 : ZMod n)) (inv (orbit 3 1)) ∧
      ∀ (j : ℕ), 1 ≤ j → j ≤ e - 1 → ∀ x : ZMod n, addOrderOf x = 2 ^ j →
        ∃ z : ZMod n, addOrderOf z = 2 ^ (j + 1) ∧ {w : ZMod n | 2 * w = x} = {z, z + half n} ∧
          addOrderOf (z + half n) = 2 ^ (j + 1))
    (hTheta : Nat.card {θ : GaloisField 3 (n / 2) // θ ^ (QQ n - 1) = -1} = QQ n - 1 ∧
      2 * (QQ n - 1) ∣ 3 ^ (n / 2) - 1 ∧
      {θ : GaloisField 3 (n / 2) | θ ^ (QQ n - 1) = -1} =
        {θ | θ ^ (2 * (QQ n - 1)) = 1} \ {θ | θ ^ (QQ n - 1) = 1}) :
    Nat.card (NFSet n 2) = 4 * (QQ n - 1) := by
  obtain ⟨ξ0, hξ0⟩ := hXi0.1
  have hb := thm_3_1_bij_of n e hne he ξ0 hξ0 (hP24 ξ0 hξ0) hStep1
  rw [Nat.card_congr (Set.BijOn.equiv _ hb), Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod,
    Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
  have h1 : Nat.card ({θ | θ ^ (QQ n - 1) = -1} : Set (GaloisField 3 (n / 2))) = QQ n - 1 := hTheta.1
  have h2 : Nat.card ({1, -1} : Set (GaloisField 3 (n / 2))) = 2 := by
    rw [Nat.card_coe_set_eq, Set.ncard_pair H4_one_ne_neg_one]
  rw [h1, h2]; ring

/-- Corollary 3.2, EXACTLY as stated (no hypotheses needed). -/
theorem cor_3_2_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e)
    (ξ0 : GaloisField 3 (n / 2)) (hξ0 : IsPrimitiveRoot ξ0 n) :
    (XiaSet n 2).Nonempty ↔
      ∃ θ s1 h1 : GaloisField 3 (n / 2), θ ^ (QQ n - 1) = -1 ∧ (s1 = 1 ∨ s1 = -1) ∧ (h1 = 1 ∨ h1 = -1) ∧
        ∃ y ∈ NFSet n 2, paramMap n ξ0 y = (θ, s1, h1) ∧ Nm n (y 0) = -1 ∧ Nm n (y 1) = -1 := by
  constructor
  · rintro ⟨y, hy⟩
    have hyNF := H4_xia_to_nf hne he heo y hy
    have hmem := H4_mapsTo hne he ξ0 hξ0 y hyNF
    simp only [paramMap, Set.mem_prod, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    obtain ⟨n0, n1⟩ := H4_xia_norms hne he y hy
    exact ⟨_, _, _, hmem.1, hmem.2.1, hmem.2.2, y, hyNF, rfl, n0, n1⟩
  · rintro ⟨θ, s1, h1, -, -, -, y, hy, -, n0, n1⟩
    exact ⟨y, H4_nf_to_xia hne he y hy n0 n1⟩

end Xia.Proofs

#print axioms Xia.Proofs.thm_3_1_step2_proved
#print axioms Xia.Proofs.thm_3_1_step3_proved
#print axioms Xia.Proofs.thm_3_1_step4_proved
#print axioms Xia.Proofs.thm_3_1_bij_of
#print axioms Xia.Proofs.thm_3_1_card_of
#print axioms Xia.Proofs.cor_3_2_proved
