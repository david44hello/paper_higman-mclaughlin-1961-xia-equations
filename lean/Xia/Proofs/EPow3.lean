/- Xia/Proofs/EPow3.lean — proofs of the rows intro_e_pow3 of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import Xia.Defs.Symmetry

namespace Xia.Proofs

open Xia Finset

/-- In any commutative ring: `y^2+y+1 = 0` and `3 ∤ m` give `(y^m)^2 + y^m + 1 = 0`. -/
theorem H35_ring_core {R : Type*} [CommRing R] (y : R) (h0 : y ^ 2 + y + 1 = 0) (m : ℕ) (hm : ¬ 3 ∣ m) :
    (y ^ m) ^ 2 + y ^ m + 1 = 0 := by
  have h3 : y ^ 3 = 1 := by linear_combination (y - 1) * h0
  obtain ⟨q, rfl | rfl⟩ : ∃ q, m = 3 * q + 1 ∨ m = 3 * q + 2 := ⟨m / 3, by omega⟩
  · have hy : y ^ (3 * q + 1) = y := by
      rw [pow_add, pow_mul, h3, one_pow, one_mul, pow_one]
    rw [hy]
    exact h0
  · have hy : y ^ (3 * q + 2) = y ^ 2 := by
      rw [pow_add, pow_mul, h3, one_pow, one_mul]
    rw [hy]
    linear_combination y * h3 + h0

/-- `x^2+x+1 ∣ (x^m)^2 + x^m + 1` when `3 ∤ m` (computed in `ZMod (x^2+x+1)`). -/
theorem H35_dvd_core (x m : ℕ) (hm : ¬ 3 ∣ m) : x ^ 2 + x + 1 ∣ (x ^ m) ^ 2 + x ^ m + 1 := by
  have h0 : (x : ZMod (x ^ 2 + x + 1)) ^ 2 + x + 1 = 0 := by
    have hself := ZMod.natCast_self (x ^ 2 + x + 1)
    push_cast at hself
    exact hself
  rw [← CharP.cast_eq_zero_iff (ZMod (x ^ 2 + x + 1)) (x ^ 2 + x + 1)]
  push_cast
  exact H35_ring_core _ h0 m hm

/-- A divisor strictly between `1` and `N` rules out primality of `N`. -/
theorem H35_not_prime_of_dvd {d N : ℕ} (hd : d ∣ N) (h1 : 1 < d) (h2 : d < N) : ¬ N.Prime := by
  intro hp
  rcases hp.eq_one_or_self_of_dvd d hd with h | h <;> omega

/-- Part (1): for `e = 3^k m`, `m > 1`, `3 ∤ m`, the number `2^{2·3^k}+2^{3^k}+1` is a proper divisor of `pp (2^e)`. -/
theorem H35_part1 (e k m : ℕ) (he : e = 3 ^ k * m) (hm1 : 1 < m) (hm3 : ¬ 3 ∣ m) :
    (2 ^ (2 * 3 ^ k) + 2 ^ 3 ^ k + 1) ∣ pp (2 ^ e) ∧ 1 < 2 ^ (2 * 3 ^ k) + 2 ^ 3 ^ k + 1 ∧
      2 ^ (2 * 3 ^ k) + 2 ^ 3 ^ k + 1 < pp (2 ^ e) := by
  have hpe : pp (2 ^ e) = ((2 ^ 3 ^ k) ^ m) ^ 2 + (2 ^ 3 ^ k) ^ m + 1 := by
    rw [pp, he, pow_mul]
  have hd : 2 ^ (2 * 3 ^ k) + 2 ^ 3 ^ k + 1 = (2 ^ 3 ^ k) ^ 2 + 2 ^ 3 ^ k + 1 := by
    rw [mul_comm, pow_mul]
  rw [hpe, hd]
  have hx2 : 2 ≤ 2 ^ 3 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_pow _ _ (by norm_num))
  have hxm : 2 ^ 3 ^ k < (2 ^ 3 ^ k) ^ m := by
    calc 2 ^ 3 ^ k = (2 ^ 3 ^ k) ^ 1 := (pow_one _).symm
      _ < (2 ^ 3 ^ k) ^ m := Nat.pow_lt_pow_right (by omega) hm1
  have hxm2 : (2 ^ 3 ^ k) ^ 2 < ((2 ^ 3 ^ k) ^ m) ^ 2 := Nat.pow_lt_pow_left hxm (by norm_num)
  refine ⟨H35_dvd_core _ m hm3, ?_, ?_⟩
  · have : 0 < (2 ^ 3 ^ k) ^ 2 := by positivity
    omega
  · omega

/-- Part (2): `pp (2^e)` prime with `e > 0` forces `e = 3^k`. -/
theorem H35_part2 (e : ℕ) (he : 0 < e) (hp : (pp (2 ^ e)).Prime) : ∃ k : ℕ, e = 3 ^ k := by
  obtain ⟨k, m, hm3, hem⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.pos_iff_ne_zero.mp he) 3 (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hem
    omega
  rcases Nat.lt_or_ge 1 m with hm1 | hm1
  · obtain ⟨hdvd, hlo, hhi⟩ := H35_part1 e k m hem hm1 hm3
    exact absurd hp (H35_not_prime_of_dvd hdvd hlo hhi)
  · refine ⟨k, ?_⟩
    have : m = 1 := by omega
    rw [hem, this, mul_one]

/-- Part (3): the four numerical facts for `e = 3^4, …, 3^7`. -/
theorem H35_part3 :
    Nat.Prime 487 ∧ 487 ∣ pp (2 ^ 3 ^ 4) ∧ Nat.Prime 80191 ∧ 80191 ∣ pp (2 ^ 3 ^ 5) ∧
      Nat.Prime 39367 ∧ 39367 ∣ pp (2 ^ 3 ^ 6) ∧ Nat.Prime 209953 ∧ 209953 ∣ pp (2 ^ 3 ^ 7) ∧
        209953 < 3 * 10 ^ 5 := by
  refine ⟨by norm_num, ?_, by norm_num, ?_, by norm_num, ?_, by norm_num, ?_, by norm_num⟩ <;>
    exact Nat.dvd_of_mod_eq_zero (by decide +kernel)

/-- `pp (2^(3^k))` is not prime for `k = 4, 5, 6, 7`. -/
theorem H35_not_prime_small (k : ℕ) (hk4 : 4 ≤ k) (hk7 : k ≤ 7) : ¬ (pp (2 ^ 3 ^ k)).Prime := by
  obtain ⟨_, h4, _, h5, _, h6, _, h7, _⟩ := H35_part3
  obtain rfl | rfl | rfl | rfl : k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  · exact H35_not_prime_of_dvd h4 (by norm_num) (by decide +kernel)
  · exact H35_not_prime_of_dvd h5 (by norm_num) (by decide +kernel)
  · exact H35_not_prime_of_dvd h6 (by norm_num) (by decide +kernel)
  · exact H35_not_prime_of_dvd h7 (by norm_num) (by decide +kernel)

/-- Part (4): `pp (2^e)` prime and `2^e ≥ 2·10^11` give `e = 3^k` with `k ≥ 8`. -/
theorem H35_part4 (e : ℕ) (hp : (pp (2 ^ e)).Prime) (hbig : 2 * 10 ^ 11 ≤ 2 ^ e) :
    ∃ k : ℕ, 8 ≤ k ∧ e = 3 ^ k := by
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      norm_num at hbig
    · exact h
  obtain ⟨k, rfl⟩ := H35_part2 e he0 hp
  refine ⟨k, ?_, rfl⟩
  have hk4 : 4 ≤ k := by
    by_contra hlt
    have h3k : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2k : 2 ^ 3 ^ k ≤ 2 ^ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) h3k
    have : (2 : ℕ) ^ 3 ^ 3 < 2 * 10 ^ 11 := by norm_num
    omega
  by_contra hlt
  exact H35_not_prime_small k hk4 (by omega) hp

theorem intro_e_pow3_proved :
    (∀ e k m : ℕ, e = 3 ^ k * m → 1 < m → ¬ 3 ∣ m →
      (2 ^ (2 * 3 ^ k) + 2 ^ 3 ^ k + 1) ∣ pp (2 ^ e) ∧ 1 < 2 ^ (2 * 3 ^ k) + 2 ^ 3 ^ k + 1 ∧
        2 ^ (2 * 3 ^ k) + 2 ^ 3 ^ k + 1 < pp (2 ^ e)) ∧
    (∀ e : ℕ, 0 < e → (pp (2 ^ e)).Prime → ∃ k : ℕ, e = 3 ^ k) ∧
    (Nat.Prime 487 ∧ 487 ∣ pp (2 ^ 3 ^ 4) ∧ Nat.Prime 80191 ∧ 80191 ∣ pp (2 ^ 3 ^ 5) ∧
      Nat.Prime 39367 ∧ 39367 ∣ pp (2 ^ 3 ^ 6) ∧ Nat.Prime 209953 ∧ 209953 ∣ pp (2 ^ 3 ^ 7) ∧ 209953 < 3 * 10 ^ 5) ∧
    ∀ e : ℕ, (pp (2 ^ e)).Prime → 2 * 10 ^ 11 ≤ 2 ^ e → ∃ k : ℕ, 8 ≤ k ∧ e = 3 ^ k :=
  ⟨H35_part1, H35_part2, H35_part3, H35_part4⟩

end Xia.Proofs

#print axioms Xia.Proofs.intro_e_pow3_proved
