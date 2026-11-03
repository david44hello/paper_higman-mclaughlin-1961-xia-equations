/- Xia/Proofs/Prop24.lean — proofs of the rows fourier_inversion, prop_2_4_F1, prop_2_4_F3, prop_2_4_F4, prop_2_4_more, prop_2_4_bij of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry

namespace Xia.Proofs

open Xia Finset

set_option linter.unusedSectionVars false

/-- Normalise a goal `(a : ZMod n) = (b : ZMod n)` built from `.val`s, numerals and `half`, then close it by `ring`. -/
macro "h10_cast" : tactic =>
  `(tactic| ((try simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_zero,
      Nat.cast_one, ZMod.natCast_zmod_val, ZMod.natCast_val, ZMod.cast_id, id_eq, half]) <;> ring))

/-! ## Arithmetic of `ZMod n` and of a primitive root `ω` -/

section Omega

variable {n : ℕ} [NeZero n] {L : Type*} [Field L] {ω : L}

/-- Exponents of `ω` only matter modulo `n`. -/
theorem H10_pow_congr (hω : IsPrimitiveRoot ω n) {a b : ℕ} (h : (a : ZMod n) = (b : ZMod n)) :
    ω ^ a = ω ^ b := by
  rw [pow_eq_pow_mod a hω.pow_eq_one, pow_eq_pow_mod b hω.pow_eq_one,
    (ZMod.natCast_eq_natCast_iff' a b n).mp h]

/-- `(n/2 : ZMod n).val = n/2`. -/
theorem H10_half_val : (half n : ZMod n).val = n / 2 := by
  unfold half
  rw [ZMod.val_natCast]
  have := NeZero.pos n
  exact Nat.mod_eq_of_lt (by omega)

/-- For even `n`: `m + m = 0`. -/
theorem H10_two_half (hn : Even n) : half n + half n = (0 : ZMod n) := by
  unfold half
  rw [← Nat.cast_add]
  have h2 : n % 2 = 0 := Nat.even_iff.mp hn
  have : n / 2 + n / 2 = n := by omega
  rw [this, ZMod.natCast_self]

/-- For even `n`: `m ≠ 0`. -/
theorem H10_half_ne_zero (hn : Even n) : half n ≠ (0 : ZMod n) := by
  intro h
  have h1 := congrArg ZMod.val h
  rw [H10_half_val, ZMod.val_zero] at h1
  have := NeZero.pos n
  have h2 : n % 2 = 0 := Nat.even_iff.mp hn
  omega

/-- For even `n`: `-m = m`. -/
theorem H10_neg_half (hn : Even n) : -half n = (half n : ZMod n) :=
  neg_eq_of_add_eq_zero_left (H10_two_half hn)

/-- For even `n`: if `t.val ≥ m` then `(t + m).val < m`. -/
theorem H10_add_half_val_lt (hn : Even n) (t : ZMod n) (ht : ¬ t.val < n / 2) :
    (t + half n).val < n / 2 := by
  rw [ZMod.val_add, H10_half_val]
  have hlt := ZMod.val_lt t
  have h2 : n % 2 = 0 := Nat.even_iff.mp hn
  rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- `ω^{n/2} = -1` for even `n`. -/
theorem H10_omega_half (hω : IsPrimitiveRoot ω n) (hn : Even n) : ω ^ (n / 2) = -1 := by
  have hpos := NeZero.pos n
  have h2 : n % 2 = 0 := Nat.even_iff.mp hn
  have hne : n / 2 ≠ 0 := by omega
  have hd : n / 2 ∣ n := Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero h2)
  have hp := hω.pow_of_dvd hne hd
  have e : n / (n / 2) = 2 := Nat.div_eq_of_eq_mul_left (by omega) (by omega)
  rw [e] at hp
  exact hp.eq_neg_one_of_two_right

/-- `(ω^{k})^{-1} = ω^{-k}`. -/
theorem H10_inv_pow (hω : IsPrimitiveRoot ω n) (k : ZMod n) : (ω ^ k.val)⁻¹ = ω ^ (-k).val := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_add, ← pow_zero ω]
  apply H10_pow_congr hω
  simp

/-- Orthogonality: `∑_k ω^{kj} = n [j = 0]`. -/
theorem H10_orth (hω : IsPrimitiveRoot ω n) (j : ZMod n) :
    ∑ k : ZMod n, (ω ^ k.val) ^ j.val = if j = 0 then (n : L) else 0 := by
  split_ifs with hj
  · subst hj
    simp [ZMod.card]
  · have hx1 : ω ^ j.val ≠ 1 := by
      intro h
      apply hj
      have hdvd := (hω.pow_eq_one_iff_dvd _).mp h
      exact (ZMod.val_eq_zero j).mp (Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt j))
    have hsum : ω ^ j.val * ∑ k : ZMod n, (ω ^ k.val) ^ j.val = ∑ k : ZMod n, (ω ^ k.val) ^ j.val := by
      rw [mul_sum]
      refine Fintype.sum_equiv (Equiv.addRight (1 : ZMod n)) _ _ (fun k => ?_)
      simp only [Equiv.coe_addRight]
      simp only [← pow_mul, ← pow_add]
      apply H10_pow_congr hω
      h10_cast
    have h0 : (ω ^ j.val - 1) * ∑ k : ZMod n, (ω ^ k.val) ^ j.val = 0 := by
      rw [sub_mul, hsum, one_mul, sub_self]
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (sub_eq_zero.mp h) hx1
    · exact h

/-! ## The transform `dft` -/

/-- Fourier inversion: `y_t = n^{-1} ∑_k ŷ(ω^k) ω^{-kt}`. -/
theorem H10_inversion (hω : IsPrimitiveRoot ω n) (hnL : (n : L) ≠ 0) (y : ZMod n → L) (t : ZMod n) :
    y t = (n : L)⁻¹ * ∑ k : ZMod n, dft ω y k * ((ω ^ k.val)⁻¹) ^ t.val := by
  have h1 : ∀ k u : ZMod n, y u * (ω ^ k.val) ^ u.val * ((ω ^ k.val)⁻¹) ^ t.val
      = y u * (ω ^ k.val) ^ (u - t).val := by
    intro k u
    rw [H10_inv_pow hω, mul_assoc]
    congr 1
    simp only [← pow_mul, ← pow_add]
    apply H10_pow_congr hω
    h10_cast
  have key : ∑ k : ZMod n, dft ω y k * ((ω ^ k.val)⁻¹) ^ t.val = (n : L) * y t := by
    unfold dft
    simp_rw [sum_mul, h1]
    rw [sum_comm]
    simp_rw [← mul_sum, H10_orth hω, sub_eq_zero, mul_ite, mul_zero]
    rw [sum_ite_eq']
    simp only [mem_univ, ite_true]
    ring
  rw [key, ← mul_assoc, inv_mul_cancel₀ hnL, one_mul]

/-- The transform of the inverse transform is the identity. -/
theorem H10_dft_inv (hω : IsPrimitiveRoot ω n) (hnL : (n : L) ≠ 0) (h : ZMod n → L) (j : ZMod n) :
    dft ω (fun t => (n : L)⁻¹ * ∑ k : ZMod n, h k * ((ω ^ k.val)⁻¹) ^ t.val) j = h j := by
  have h1 : ∀ t k : ZMod n, h k * ((ω ^ k.val)⁻¹) ^ t.val * (ω ^ j.val) ^ t.val
      = h k * (ω ^ t.val) ^ (j - k).val := by
    intro t k
    rw [H10_inv_pow hω, mul_assoc]
    congr 1
    simp only [← pow_mul, ← pow_add]
    apply H10_pow_congr hω
    h10_cast
  unfold dft
  simp_rw [mul_assoc ((n : L)⁻¹), sum_mul, h1]
  rw [← mul_sum, sum_comm]
  simp_rw [← mul_sum, H10_orth hω, sub_eq_zero, mul_ite, mul_zero]
  rw [sum_ite_eq]
  simp only [mem_univ, ite_true]
  rw [mul_comm (h j), ← mul_assoc, inv_mul_cancel₀ hnL, one_mul]

/-- `dft` is injective when `n` is invertible. -/
theorem H10_dft_inj (hω : IsPrimitiveRoot ω n) (hnL : (n : L) ≠ 0) {z z' : ZMod n → L}
    (h : ∀ k, dft ω z k = dft ω z' k) : z = z' := by
  funext t
  rw [H10_inversion hω hnL z t, H10_inversion hω hnL z' t]
  simp only [h]

/-- `ŷ(-1) = S`. -/
theorem H10_dft_half (hω : IsPrimitiveRoot ω n) (hn : Even n) (z : ZMod n → L) : dft ω z (half n) = S z := by
  unfold dft S sgn
  rw [H10_half_val, H10_omega_half hω hn]
  exact sum_congr rfl (fun t _ => mul_comm _ _)

/-- Linearity of `dft` in a scalar factor. -/
theorem H10_dft_smul (c : L) (g : ZMod n → L) (k : ZMod n) :
    dft ω (fun r => c * g r) k = c * dft ω g k := by
  unfold dft
  rw [mul_sum]
  exact sum_congr rfl (fun _ _ => mul_assoc _ _ _)

/-- `ŷ(ξ) ŷ(ξ^{-1}) = ∑_s R(s) ξ^s`. -/
theorem H10_dft_R (hω : IsPrimitiveRoot ω n) (z : ZMod n → L) (k : ZMod n) :
    dft ω z k * dft ω z (-k) = dft ω (R z) k := by
  unfold dft R
  rw [sum_mul_sum, sum_comm]
  have hrhs : (∑ s : ZMod n, (∑ u : ZMod n, z u * z (u + s)) * (ω ^ k.val) ^ s.val)
      = ∑ u : ZMod n, ∑ s : ZMod n, z u * z (u + s) * (ω ^ k.val) ^ s.val := by
    simp_rw [sum_mul]
    exact sum_comm
  rw [hrhs]
  refine sum_congr rfl (fun u _ => ?_)
  refine Fintype.sum_equiv (Equiv.subRight u) _ _ (fun t => ?_)
  simp only [Equiv.subRight_apply]
  rw [show u + (t - u) = t by abel]
  have hp : (ω ^ k.val) ^ t.val * (ω ^ (-k).val) ^ u.val = (ω ^ k.val) ^ (t - u).val := by
    simp only [← pow_mul, ← pow_add]
    apply H10_pow_congr hω
    h10_cast
  rw [← hp]
  ring

/-- `∑_s [s = m] ξ^s = ξ^m`. -/
theorem H10_dft_delta (k : ZMod n) :
    dft ω (fun s => if s = half n then (1 : L) else 0) k = (ω ^ k.val) ^ (n / 2) := by
  unfold dft
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]
  rw [H10_half_val]

end Omega

/-! ## The auxiliary sequences `c(r)` and `d(r)` of the (F4) proof -/

/-- `c(r) := ∑_t (-1)^t y_t y_{r-t}` (s2_xia.tex:99). -/
def H10_C {n : ℕ} [NeZero n] {K : Type*} [CommRing K] (z : ZMod n → K) (r : ZMod n) : K :=
  ∑ t, sgn t * z t * z (r - t)

/-- `d(r) := ∑_{2s = r} y_s`, so that `∑_r d(r) ξ^r = ŷ(ξ^2)`. -/
def H10_D {n : ℕ} [NeZero n] {K : Type*} [CommRing K] (z : ZMod n → K) (r : ZMod n) : K :=
  ∑ s, if 2 * s = r then z s else 0

section Omega2

variable {n : ℕ} [NeZero n] {L : Type*} [Field L] {ω : L}

/-- `ŷ(ξ) ŷ(-ξ) = ∑_r c(r) ξ^r`. -/
theorem H10_dft_C (hω : IsPrimitiveRoot ω n) (hn : Even n) (z : ZMod n → L) (k : ZMod n) :
    dft ω z k * dft ω z (k + half n) = dft ω (H10_C z) k := by
  unfold dft H10_C
  rw [sum_mul_sum, sum_comm]
  have hrhs : (∑ r : ZMod n, (∑ t : ZMod n, sgn t * z t * z (r - t)) * (ω ^ k.val) ^ r.val)
      = ∑ t : ZMod n, ∑ r : ZMod n, sgn t * z t * z (r - t) * (ω ^ k.val) ^ r.val := by
    simp_rw [sum_mul]
    exact sum_comm
  rw [hrhs]
  refine sum_congr rfl (fun t _ => ?_)
  refine Fintype.sum_equiv (Equiv.addLeft t) _ _ (fun u => ?_)
  simp only [Equiv.coe_addLeft]
  rw [show t + u - t = u by abel]
  have hp : (ω ^ k.val) ^ u.val * (ω ^ (k + half n).val) ^ t.val = sgn t * (ω ^ k.val) ^ (t + u).val := by
    unfold sgn
    rw [← H10_omega_half hω hn]
    simp only [← pow_mul, ← pow_add]
    apply H10_pow_congr hω
    h10_cast
  calc z u * (ω ^ k.val) ^ u.val * (z t * (ω ^ (k + half n).val) ^ t.val)
      = z u * z t * ((ω ^ k.val) ^ u.val * (ω ^ (k + half n).val) ^ t.val) := by ring
    _ = _ := by rw [hp]; ring

/-- `ŷ(ξ^2) = ∑_r d(r) ξ^r`. -/
theorem H10_dft_D (hω : IsPrimitiveRoot ω n) (z : ZMod n → L) (k : ZMod n) :
    dft ω z (2 * k) = dft ω (H10_D z) k := by
  unfold dft H10_D
  simp only [sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  simp only [sum_ite_eq, mem_univ, ite_true]
  refine sum_congr rfl (fun s _ => ?_)
  congr 1
  simp only [← pow_mul]
  apply H10_pow_congr hω
  h10_cast

/-- (F3) for `ŷ` is `R(s) = [s = m]` for all `s`. -/
theorem H10_F3_iff (hω : IsPrimitiveRoot ω n) (hnL : (n : L) ≠ 0) (z : ZMod n → L) :
    F3 ω (dft ω z) ↔ ∀ s, R z s = if s = half n then 1 else 0 := by
  unfold F3
  constructor
  · intro h
    have : R z = fun s => if s = half n then (1 : L) else 0 :=
      H10_dft_inj hω hnL (fun k => by rw [← H10_dft_R hω, h k, H10_dft_delta])
    exact fun s => congrFun this s
  · intro h k
    rw [H10_dft_R hω, show R z = fun s => if s = half n then (1 : L) else 0 from funext h, H10_dft_delta]

/-- (F4) for `ŷ` is `c(r) = S d(r)` for all `r`. -/
theorem H10_F4_iff (hω : IsPrimitiveRoot ω n) (hnL : (n : L) ≠ 0) (hn : Even n) (z : ZMod n → L) :
    F4 (dft ω z) ↔ ∀ r, H10_C z r = S z * H10_D z r := by
  unfold F4
  constructor
  · intro h
    have : H10_C z = fun r => S z * H10_D z r :=
      H10_dft_inj hω hnL (fun k => by
        rw [← H10_dft_C hω hn, h k, H10_dft_smul, H10_dft_half hω hn, H10_dft_D hω])
    exact fun r => congrFun this r
  · intro h k
    rw [H10_dft_C hω hn, show H10_C z = fun r => S z * H10_D z r from funext h, H10_dft_smul,
      H10_dft_half hω hn, H10_dft_D hω]

/-- The key computation for (F1): `ξ^6 ŷ(ξ)^3 = ∑_t y_{t-2}^3 ξ^{3t}` in characteristic 3. -/
theorem H10_F1_key [CharP L 3] (hω : IsPrimitiveRoot ω n) (z : ZMod n → L) (k : ZMod n) :
    (ω ^ k.val) ^ (((3 : ℕ) : ℤ) * 2) * dft ω z k ^ 3
      = dft ω (fun t => z (t - 2) ^ 3) (((3 : ℕ) : ZMod n) * k) := by
  rw [show ((3 : ℕ) : ℤ) * 2 = ((6 : ℕ) : ℤ) by norm_num, zpow_natCast]
  unfold dft
  rw [sum_pow_char 3, mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight (2 : ZMod n)) _ _ (fun t => ?_)
  simp only [Equiv.coe_addRight, add_sub_cancel_right]
  have hp : (ω ^ k.val) ^ 6 * ((ω ^ k.val) ^ t.val) ^ 3
      = (ω ^ (((3 : ℕ) : ZMod n) * k).val) ^ (t + 2).val := by
    simp only [← pow_mul, ← pow_add]
    apply H10_pow_congr hω
    h10_cast
  rw [mul_pow, ← hp]
  ring

/-- (F1) for `ŷ` is `y_{s+2} = y_s^3` for all `s` (characteristic 3, `3 ∤ n`). -/
theorem H10_F1_iff [CharP L 3] (hω : IsPrimitiveRoot ω n) (hnL : (n : L) ≠ 0) (h3 : ¬ 3 ∣ n)
    (z : ZMod n → L) : F1 3 2 ω (dft ω z) ↔ ∀ s, z (s + 2) = z s ^ 3 := by
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have hsurj : ∀ j : ZMod n, ∃ k : ZMod n, ((3 : ℕ) : ZMod n) * k = j := by
    intro j
    refine ⟨((ZMod.unitOfCoprime 3 hcop)⁻¹ : (ZMod n)ˣ) * j, ?_⟩
    rw [← mul_assoc, ← ZMod.coe_unitOfCoprime 3 hcop, Units.mul_inv, one_mul]
  constructor
  · intro h
    have heq : z = fun t => z (t - 2) ^ 3 := H10_dft_inj hω hnL (fun j => by
      obtain ⟨k, rfl⟩ := hsurj j
      rw [← H10_F1_key hω z k]
      exact h k)
    intro s
    have hs := congrFun heq (s + 2)
    simp only [add_sub_cancel_right] at hs
    exact hs
  · intro h k
    show dft ω z (((3 : ℕ) : ZMod n) * k) = (ω ^ k.val) ^ (((3 : ℕ) : ℤ) * 2) * dft ω z k ^ 3
    rw [H10_F1_key hω z k]
    congr 1
    funext t
    rw [← h (t - 2), sub_add_cancel]

end Omega2

/-! ## Combinatorics of the sign `(-1)^t`, of `R`, `c`, `d` (any even `n`) -/

section Comb

variable {n : ℕ} [NeZero n] {K : Type*} [CommRing K]

theorem H10_sgn_add (hn : Even n) (a b : ZMod n) : (sgn (a + b) : K) = sgn a * sgn b := by
  unfold sgn
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hn.neg_one_pow, pow_add]

theorem H10_sgn_mul_self (t : ZMod n) : (sgn t : K) * sgn t = 1 := by
  unfold sgn
  rw [← pow_add]
  exact Even.neg_one_pow ⟨t.val, rfl⟩

theorem H10_sgn_zero : (sgn (0 : ZMod n) : K) = 1 := by
  unfold sgn
  simp

theorem H10_sgn_neg (hn : Even n) (t : ZMod n) : (sgn (-t) : K) = sgn t := by
  have h := H10_sgn_add (K := K) hn (-t) t
  rw [neg_add_cancel, H10_sgn_zero] at h
  calc (sgn (-t) : K) = sgn (-t) * (sgn t * sgn t) := by rw [H10_sgn_mul_self, mul_one]
    _ = (sgn (-t) * sgn t) * sgn t := by ring
    _ = sgn t := by rw [← h, one_mul]

theorem H10_sgn_sub (hn : Even n) (r t : ZMod n) : (sgn (r - t) : K) = sgn r * sgn t := by
  rw [sub_eq_add_neg, H10_sgn_add hn, H10_sgn_neg hn]

theorem H10_sgn_two_mul (hn : Even n) (s : ZMod n) : (sgn (2 * s) : K) = 1 := by
  rw [two_mul, H10_sgn_add hn, H10_sgn_mul_self]

/-- Every `r` is `2s` or has `(-1)^r = -1`. -/
theorem H10_even_or_odd (r : ZMod n) : (∃ s : ZMod n, r = 2 * s) ∨ (sgn r : K) = -1 := by
  rcases Nat.even_or_odd r.val with ⟨c, hc⟩ | h
  · left
    refine ⟨(c : ZMod n), ?_⟩
    rw [← ZMod.natCast_zmod_val r, hc]
    push_cast
    ring
  · right
    unfold sgn
    exact h.neg_one_pow

/-- `2x = 0` iff `x ∈ {0, m}`. -/
theorem H10_two_mul_zero (hn : Even n) (x : ZMod n) (hx : 2 * x = 0) : x = 0 ∨ x = half n := by
  have hc : ((2 * x.val : ℕ) : ZMod n) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_ofNat, hx]
  have hv : (2 * x.val) % n = 0 := by rw [← ZMod.val_natCast, hc, ZMod.val_zero]
  have hlt := ZMod.val_lt x
  have h2 : n % 2 = 0 := Nat.even_iff.mp hn
  by_cases hsm : 2 * x.val < n
  · left
    rw [Nat.mod_eq_of_lt hsm] at hv
    exact (ZMod.val_eq_zero x).mp (by omega)
  · right
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hv
    have hval : x.val = n / 2 := by omega
    rw [← ZMod.natCast_zmod_val x, hval]
    rfl

theorem H10_two_mul_iff (hn : Even n) (s s0 : ZMod n) : 2 * s = 2 * s0 ↔ s = s0 ∨ s = s0 + half n := by
  constructor
  · intro h
    have hx : 2 * (s - s0) = 0 := by rw [mul_sub, h, sub_self]
    rcases H10_two_mul_zero hn _ hx with h0 | h0
    · left
      exact sub_eq_zero.mp h0
    · right
      rw [← h0]
      ring
  · rintro (h | h)
    · rw [h]
    · rw [h, mul_add, two_mul (half n), H10_two_half hn, add_zero]

/-- `d(2 s_0) = y_{s_0} + y_{s_0+m}`. -/
theorem H10_D_two_mul (hn : Even n) (y : ZMod n → K) (s0 : ZMod n) :
    H10_D y (2 * s0) = y s0 + y (s0 + half n) := by
  unfold H10_D
  have hne : s0 ≠ s0 + half n := by
    intro h
    apply H10_half_ne_zero hn
    calc half n = s0 + half n - s0 := by ring
      _ = 0 := by rw [← h, sub_self]
  have hsplit : ∀ s : ZMod n, (if 2 * s = 2 * s0 then y s else 0)
      = (if s = s0 then y s else 0) + (if s = s0 + half n then y s else 0) := by
    intro s
    have hiff := H10_two_mul_iff hn s s0
    by_cases h1 : s = s0
    · rw [ite_eq_left (hiff.mpr (Or.inl h1)), ite_eq_left h1, ite_eq_right (by rw [h1]; exact hne), add_zero]
    · by_cases h2 : s = s0 + half n
      · rw [ite_eq_left (hiff.mpr (Or.inr h2)), ite_eq_right h1, ite_eq_left h2, zero_add]
      · rw [ite_eq_right (fun h => (hiff.mp h).elim h1 h2), ite_eq_right h1, ite_eq_right h2, add_zero]
  rw [sum_congr rfl (fun s _ => hsplit s), sum_add_distrib, sum_ite_eq', sum_ite_eq']
  simp only [mem_univ, ite_true]

/-- `c(r) = (-1)^r c(r)` (substitute `t ↦ r - t`). -/
theorem H10_C_eq_sgn_mul (hn : Even n) (y : ZMod n → K) (r : ZMod n) : H10_C y r = sgn r * H10_C y r := by
  unfold H10_C
  rw [mul_sum]
  refine Fintype.sum_equiv (Equiv.subLeft r) _ _ (fun t => ?_)
  simp only [Equiv.subLeft_apply]
  rw [sub_sub_cancel, H10_sgn_sub hn r t]
  have hs := H10_sgn_mul_self (K := K) r
  linear_combination (-(sgn t * y t * y (r - t))) * hs

/-- (L4) holds for every `s`, not only `s < m`. -/
theorem H10_L4_all (hn : Even n) {y : ZMod n → K} (h4 : L4 y) (s : ZMod n) :
    H10_C y (2 * s) = (y s + y (s + half n)) * S y := by
  by_cases hs : s.val < n / 2
  · exact h4 s hs
  · have h : H10_C y (2 * (s + half n)) = (y (s + half n) + y (s + half n + half n)) * S y :=
      h4 (s + half n) (H10_add_half_val_lt hn s hs)
    rw [(H10_two_mul_iff hn (s + half n) s).mpr (Or.inr rfl),
      show s + half n + half n = s by rw [add_assoc, H10_two_half hn, add_zero]] at h
    rw [h]
    ring

/-- `R(-s) = R(s)`. -/
theorem H10_R_neg (y : ZMod n → K) (s : ZMod n) : R y (-s) = R y s := by
  unfold R
  exact Fintype.sum_equiv (Equiv.subRight s) _ _ (fun t => by
    simp only [Equiv.subRight_apply, sub_add_cancel, ← sub_eq_add_neg]
    ring)

/-- (L3) gives `R(s) = 0` for every `s ≠ m`. -/
theorem H10_R_zero (hn : Even n) (y : ZMod n → K) (h3 : L3 0 y) (s : ZMod n) (hs : s ≠ half n) :
    R y s = 0 := by
  have hR : ∀ s : ZMod n, s.val < n / 2 → R y s = 0 := by
    intro s hs
    rw [← h3 s hs]
    unfold R
    simp only [add_comm s]
  by_cases h : s.val < n / 2
  · exact hR s h
  · have hne : s.val ≠ n / 2 := by
      intro he
      apply hs
      rw [← ZMod.natCast_zmod_val s, he]
      rfl
    have hlt := ZMod.val_lt s
    have h2 : n % 2 = 0 := Nat.even_iff.mp hn
    have hneg := H10_R_neg y (-s)
    rw [neg_neg] at hneg
    rw [hneg]
    apply hR
    rw [ZMod.neg_val', Nat.mod_eq_of_lt (by omega)]
    omega

/-- (L3) with `R(m) = 1` is `R(s) = [s = m]` for all `s`. -/
theorem H10_L3R_iff (hn : Even n) (y : ZMod n → K) :
    (L3 0 y ∧ R y (half n) = 1) ↔ ∀ s, R y s = if s = half n then 1 else 0 := by
  constructor
  · rintro ⟨h3, hm⟩ s
    split_ifs with hs
    · rw [hs, hm]
    · exact H10_R_zero hn y h3 s hs
  · intro h
    refine ⟨fun s hs => ?_, by rw [h, ite_eq_left rfl]⟩
    have hne : s ≠ half n := by
      intro he
      rw [he, H10_half_val] at hs
      exact lt_irrefl _ hs
    have hRs := h s
    rw [ite_eq_right hne] at hRs
    exact (show ∑ t, y t * y (s + t) = R y s by unfold R; simp only [add_comm s]).trans hRs

end Comb

section CombField

variable {n : ℕ} [NeZero n] {K : Type*} [Field K]

/-- (L4) is `c(r) = S d(r)` for all `r` (needs `2 ≠ 0`). -/
theorem H10_L4_iff (h2 : (2 : K) ≠ 0) (hn : Even n) (y : ZMod n → K) :
    L4 y ↔ ∀ r, H10_C y r = S y * H10_D y r := by
  constructor
  · intro h4 r
    rcases H10_even_or_odd (K := K) r with ⟨s, rfl⟩ | hodd
    · rw [H10_L4_all hn h4 s, H10_D_two_mul hn]
      ring
    · have hD : H10_D y r = 0 := by
        unfold H10_D
        refine sum_eq_zero (fun s _ => ite_eq_right ?_)
        intro hs
        have h1 := H10_sgn_two_mul (K := K) hn s
        rw [hs, hodd] at h1
        apply h2
        linear_combination -h1
      have hC := H10_C_eq_sgn_mul hn y r
      rw [hodd] at hC
      have h2C : (2 : K) * H10_C y r = 0 := by linear_combination hC
      rw [hD, mul_zero]
      exact (mul_eq_zero.mp h2C).resolve_left h2
  · intro h s _
    show H10_C y (2 * s) = _
    rw [h, H10_D_two_mul hn]
    ring

theorem H10_two_ne_zero [CharP K 3] : (2 : K) ≠ 0 := by
  have h := (CharP.cast_eq_zero_iff K 3 2).not.mpr (by decide)
  simpa using h

end CombField

/-! ## Characteristic 3, transport along `F → L`, the roots of `X^q - X` -/

theorem H10_charP_L (n : ℕ) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] : CharP L 3 :=
  charP_of_injective_algebraMap (algebraMap (GaloisField 3 (n / 2)) L).injective 3

theorem H10_nL {n : ℕ} {L : Type*} [Field L] [CharP L 3] (h3 : ¬ 3 ∣ n) : (n : L) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff L 3]
  exact h3

section Transport

variable {n : ℕ} [NeZero n] {F L : Type*} [Field F] [Field L] [Algebra F L]

theorem H10_map_sgn (t : ZMod n) : algebraMap F L (sgn t) = sgn t := by
  simp [sgn]

theorem H10_map_R (y : ZMod n → F) (s : ZMod n) :
    R (fun t => algebraMap F L (y t)) s = algebraMap F L (R y s) := by
  simp [R]

theorem H10_map_S (y : ZMod n → F) : S (fun t => algebraMap F L (y t)) = algebraMap F L (S y) := by
  simp [S, H10_map_sgn]

theorem H10_map_C (y : ZMod n → F) (r : ZMod n) :
    H10_C (fun t => algebraMap F L (y t)) r = algebraMap F L (H10_C y r) := by
  simp [H10_C, H10_map_sgn]

theorem H10_map_D (y : ZMod n → F) (r : ZMod n) :
    H10_D (fun t => algebraMap F L (y t)) r = algebraMap F L (H10_D y r) := by
  simp only [H10_D, map_sum]
  refine sum_congr rfl (fun s _ => ?_)
  split_ifs <;> simp

end Transport

/-- In any extension `L` of a finite field `F`, the solutions of `x^{|F|} = x` are exactly the elements of `F`. -/
theorem H10_mem_range {F L : Type*} [Field F] [Fintype F] [Field L] [Algebra F L] (x : L)
    (hx : x ^ Fintype.card F = x) : ∃ a : F, algebraMap F L a = x := by
  classical
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hP : (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial L) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero L hq
  have hdeg : (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial L).natDegree = Fintype.card F :=
    FiniteField.X_pow_card_sub_X_natDegree_eq L hq
  have hroot : ∀ b : L, b ^ Fintype.card F = b →
      b ∈ (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial L).roots.toFinset := by
    intro b hb
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP, Polynomial.IsRoot.def, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, hb, sub_self]
  have hsub : univ.image (algebraMap F L) ⊆
      (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial L).roots.toFinset := by
    intro b hb
    obtain ⟨a, -, rfl⟩ := mem_image.mp hb
    exact hroot _ (by rw [← map_pow, FiniteField.pow_card])
  have hcard : (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial L).roots.toFinset.card ≤
      (univ.image (algebraMap F L)).card := by
    rw [card_image_of_injective _ (algebraMap F L).injective, card_univ]
    calc _ ≤ Multiset.card (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial L).roots :=
          Multiset.toFinset_card_le _
      _ ≤ _ := Polynomial.card_roots' _
      _ = _ := hdeg
  have heq := eq_of_subset_of_card_le hsub hcard
  have hxm := hroot x hx
  rw [← heq] at hxm
  obtain ⟨a, -, ha⟩ := mem_image.mp hxm
  exact ⟨a, ha⟩

/-! ## The statements -/

/-- Coverage — s2_xia.tex:74, :76: the inversion formula and `S = ŷ(-1)`. -/
theorem fourier_inversion_proved (n : ℕ) [NeZero n] (hn : Even n) {L : Type*} [Field L] (ω : L)
    (hω : IsPrimitiveRoot ω n) (hnL : (n : L) ≠ 0) (y : ZMod n → L) :
    (∀ t : ZMod n, y t = (n : L)⁻¹ * ∑ k : ZMod n, dft ω y k * ((ω ^ k.val)⁻¹) ^ t.val) ∧
      dft ω y (half n) = S y :=
  ⟨fun t => H10_inversion hω hnL y t, H10_dft_half hω hn y⟩

/-- Row 4b — Proposition 2.4 (s2_xia.tex:86): (F1) is equivalent to (L1). -/
theorem prop_2_4_F1_proved (n : ℕ) [NeZero n] (_hn : Even n) (h3 : ¬ 3 ∣ n) {L : Type*} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2)) :
    L1 3 2 y ↔ F1 3 2 ω (dftA ω y) := by
  have := H10_charP_L n (L := L)
  rw [show dftA ω y = dft ω (fun t => algebraMap (GaloisField 3 (n / 2)) L (y t)) from rfl,
    H10_F1_iff hω (H10_nL h3) h3]
  unfold L1
  refine forall_congr' (fun s => ?_)
  rw [Int.cast_ofNat, ← map_pow, (algebraMap (GaloisField 3 (n / 2)) L).injective.eq_iff]

/-- Row 4c — Proposition 2.4 (s2_xia.tex:86): (F3) is equivalent to (L3) together with `R(m) = 1`. -/
theorem prop_2_4_F3_proved (n : ℕ) [NeZero n] (hn : Even n) (h3 : ¬ 3 ∣ n) {L : Type*} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2)) :
    (L3 0 y ∧ R y (half n) = 1) ↔ F3 ω (dftA ω y) := by
  have := H10_charP_L n (L := L)
  rw [H10_L3R_iff hn, show dftA ω y = dft ω (fun t => algebraMap (GaloisField 3 (n / 2)) L (y t)) from rfl,
    H10_F3_iff hω (H10_nL h3)]
  refine forall_congr' (fun s => ?_)
  rw [H10_map_R]
  split_ifs
  · rw [← map_one (algebraMap (GaloisField 3 (n / 2)) L), (algebraMap (GaloisField 3 (n / 2)) L).injective.eq_iff]
  · rw [← map_zero (algebraMap (GaloisField 3 (n / 2)) L), (algebraMap (GaloisField 3 (n / 2)) L).injective.eq_iff]

/-- Row 4d — Proposition 2.4 (s2_xia.tex:86): (F4) is equivalent to (L4). -/
theorem prop_2_4_F4_proved (n : ℕ) [NeZero n] (hn : Even n) (h3 : ¬ 3 ∣ n) {L : Type*} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2)) :
    L4 y ↔ F4 (dftA ω y) := by
  have := H10_charP_L n (L := L)
  rw [H10_L4_iff H10_two_ne_zero hn,
    show dftA ω y = dft ω (fun t => algebraMap (GaloisField 3 (n / 2)) L (y t)) from rfl,
    H10_F4_iff hω (H10_nL h3) hn]
  refine forall_congr' (fun r => ?_)
  rw [H10_map_C, H10_map_S, H10_map_D, ← map_mul, (algebraMap (GaloisField 3 (n / 2)) L).injective.eq_iff]

/-- Row 4e — Proposition 2.4 (s2_xia.tex:86-88): for a solution, `ŷ` has no zero on `μ_n`,
`ŷ(ξ^{3^j}) = ξ^{2j3^j} ŷ(ξ)^{3^j}` for every `j ≥ 0`, and `S^2 = (-1)^m`. -/
theorem prop_2_4_more_proved (n : ℕ) [NeZero n] (hn : Even n) (h3 : ¬ 3 ∣ n) {L : Type*} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2))
    (hy : y ∈ NFSet n 2) :
    (∀ k, dftA ω y k ≠ 0) ∧
      (∀ (j : ℕ) (k : ZMod n), dftA ω y ((3 : ZMod n) ^ j * k) = (ω ^ k.val) ^ (2 * j * 3 ^ j) * dftA ω y k ^ (3 ^ j)) ∧
      S y ^ 2 = (-1) ^ (n / 2) := by
  have := H10_charP_L n (L := L)
  obtain ⟨h1, h3', hR, _⟩ := hy
  have hF1 : F1 3 2 ω (dftA ω y) := (prop_2_4_F1_proved n hn h3 ω hω y).mp h1
  have hF3 : F3 ω (dftA ω y) := (prop_2_4_F3_proved n hn h3 ω hω y).mp ⟨h3', hR⟩
  refine ⟨fun k hk => ?_, fun j k => ?_, ?_⟩
  · have h := hF3 k
    rw [hk, zero_mul] at h
    exact pow_ne_zero _ (pow_ne_zero _ (hω.ne_zero (NeZero.ne n))) h.symm
  · induction j with
    | zero => simp
    | succ j ih =>
      have e : (3 : ZMod n) ^ (j + 1) * k = ((3 : ℕ) : ZMod n) * ((3 : ZMod n) ^ j * k) := by
        push_cast
        ring
      rw [e, hF1 ((3 : ZMod n) ^ j * k), ih]
      have hp : (ω ^ ((3 : ZMod n) ^ j * k).val) ^ (((3 : ℕ) : ℤ) * 2) = (ω ^ k.val) ^ (6 * 3 ^ j) := by
        rw [show ((3 : ℕ) : ℤ) * 2 = ((6 : ℕ) : ℤ) by norm_num, zpow_natCast]
        simp only [← pow_mul]
        apply H10_pow_congr hω
        h10_cast
      rw [hp]
      generalize ω ^ k.val = x
      generalize dftA ω y k = w
      rw [mul_pow, ← pow_mul, ← pow_mul, ← mul_assoc, ← pow_add, pow_succ 3 j]
      congr 2
      ring
  · have hm := hF3 (half n)
    have hS : dftA ω y (half n) = algebraMap (GaloisField 3 (n / 2)) L (S y) :=
      (H10_dft_half hω hn (fun t => algebraMap (GaloisField 3 (n / 2)) L (y t))).trans (H10_map_S y)
    rw [H10_neg_half hn, hS, H10_half_val, H10_omega_half hω hn] at hm
    apply (algebraMap (GaloisField 3 (n / 2)) L).injective
    rw [map_pow, sq, hm, map_pow, map_neg, map_one]

/-- Row 4a — Proposition 2.4 (s2_xia.tex:78-80): `y ↦ ŷ` is a bijection from the solutions of the norm-free system
onto the functions `ŷ : μ_n → L` with (F1), (F3), (F4). -/
theorem prop_2_4_bij_proved (n : ℕ) [NeZero n] (hn : Even n) (h3 : ¬ 3 ∣ n) {L : Type*} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) :
    Set.BijOn (dftA ω) (NFSet n 2) {h | F1 3 2 ω h ∧ F3 ω h ∧ F4 h} := by
  have := H10_charP_L n (L := L)
  have hnL : (n : L) ≠ 0 := H10_nL h3
  refine ⟨fun y hy => ?_, fun y _ y' _ hyy => ?_, fun h hh => ?_⟩
  · obtain ⟨h1, h3', hR, h4⟩ := hy
    show F1 3 2 ω (dftA ω y) ∧ F3 ω (dftA ω y) ∧ F4 (dftA ω y)
    exact ⟨(prop_2_4_F1_proved n hn h3 ω hω y).mp h1, (prop_2_4_F3_proved n hn h3 ω hω y).mp ⟨h3', hR⟩,
      (prop_2_4_F4_proved n hn h3 ω hω y).mp h4⟩
  · have hz := H10_dft_inj hω hnL (z := fun t => algebraMap (GaloisField 3 (n / 2)) L (y t))
      (z' := fun t => algebraMap (GaloisField 3 (n / 2)) L (y' t)) (fun k => congrFun hyy k)
    funext t
    exact (algebraMap (GaloisField 3 (n / 2)) L).injective (congrFun hz t)
  · obtain ⟨hF1, hF3, hF4⟩ := hh
    obtain ⟨z, hdz⟩ : ∃ z : ZMod n → L, dft ω z = h := ⟨_, funext (H10_dft_inv hω hnL h)⟩
    have hL1z : ∀ s, z (s + 2) = z s ^ 3 := (H10_F1_iff hω hnL h3 z).mp (by rw [hdz]; exact hF1)
    have hiter : ∀ (t : ZMod n) (j : ℕ), z (t + ((2 * j : ℕ) : ZMod n)) = z t ^ (3 ^ j) := by
      intro t j
      induction j with
      | zero => simp
      | succ j ih =>
        have e : t + ((2 * (j + 1) : ℕ) : ZMod n) = t + ((2 * j : ℕ) : ZMod n) + 2 := by
          push_cast
          ring
        rw [e, hL1z, ih, ← pow_mul, ← pow_succ]
    have hfix : ∀ t, z t ^ (3 ^ (n / 2)) = z t := by
      intro t
      have := hiter t (n / 2)
      rw [Nat.two_mul_div_two_of_even hn, ZMod.natCast_self, add_zero] at this
      exact this.symm
    let : Fintype (GaloisField 3 (n / 2)) := Fintype.ofFinite _
    have hcard : Fintype.card (GaloisField 3 (n / 2)) = 3 ^ (n / 2) := by
      rw [Fintype.card_eq_nat_card]
      have hpos := NeZero.pos n
      have h2 : n % 2 = 0 := Nat.even_iff.mp hn
      exact GaloisField.card 3 (n / 2) (by omega)
    have hrange : ∀ t, ∃ a : GaloisField 3 (n / 2), algebraMap (GaloisField 3 (n / 2)) L a = z t :=
      fun t => H10_mem_range (z t) (by rw [hcard]; exact hfix t)
    choose y hy using hrange
    have hdy : dftA ω y = h := by
      rw [← hdz]
      show dft ω (fun t => algebraMap (GaloisField 3 (n / 2)) L (y t)) = dft ω z
      congr 1
      funext t
      exact hy t
    refine ⟨y, ?_, hdy⟩
    have hF3y : F3 ω (dftA ω y) := by rw [hdy]; exact hF3
    have hL3R := (prop_2_4_F3_proved n hn h3 ω hω y).mpr hF3y
    show L1 3 2 y ∧ L3 0 y ∧ R y (half n) = 1 ∧ L4 y
    exact ⟨(prop_2_4_F1_proved n hn h3 ω hω y).mpr (by rw [hdy]; exact hF1), hL3R.1, hL3R.2,
      (prop_2_4_F4_proved n hn h3 ω hω y).mpr (by rw [hdy]; exact hF4)⟩

#print axioms fourier_inversion_proved
#print axioms prop_2_4_F1_proved
#print axioms prop_2_4_F3_proved
#print axioms prop_2_4_F4_proved
#print axioms prop_2_4_more_proved
#print axioms prop_2_4_bij_proved

end Xia.Proofs
