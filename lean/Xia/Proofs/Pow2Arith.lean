/- Xia/Proofs/Pow2Arith.lean — proofs of the rows thm_3_1_xi0, thm_3_1_theta_set, thm_3_1_step1, sec_3_2_setup, rem_3_6, thm_4_1_pow2 of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry

namespace Xia.Proofs

open Xia Finset

/-! ## 1. Powers of 3 modulo powers of 2 (lifting the exponent, by hand) -/

/-- `3^(2^(k+1)) = 1 + 2^(k+3)·(odd)`, i.e. `v_2(3^(2^(k+1)) - 1) = k+3`. -/
theorem H3_three_pow (k : ℕ) : ∃ m : ℕ, 3 ^ (2 ^ (k + 1)) = 1 + 2 ^ (k + 3) * (2 * m + 1) := by
  induction k with
  | zero => exact ⟨0, by norm_num⟩
  | succ k ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨m + 2 ^ (k + 1) * (2 * m + 1) ^ 2, ?_⟩
    rw [pow_succ 2 (k + 1), pow_mul, hm]
    ring

theorem H3_padic (a m : ℕ) : padicValNat 2 (2 ^ a * (2 * m + 1)) = a := by
  have h1 : 2 * m + 1 ≠ 0 := by omega
  have h2 : ¬ 2 ∣ 2 * m + 1 := by omega
  rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) h1, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd h2, add_zero]

theorem H3_mod (k m : ℕ) : (1 + 2 ^ (k + 3) * (2 * m + 1)) % 2 ^ (k + 4) = 1 + 2 ^ (k + 3) := by
  have h : 1 + 2 ^ (k + 3) * (2 * m + 1) = (1 + 2 ^ (k + 3)) + 2 ^ (k + 4) * m := by ring
  rw [h, Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  have h3 : 2 ^ (k + 4) = 2 * 2 ^ (k + 3) := by ring
  have h4 : 0 < 2 ^ (k + 3) := pow_pos two_pos _
  have h5 : 2 ^ (k + 3) = 8 * 2 ^ k := by ring
  have h6 : 0 < 2 ^ k := pow_pos two_pos _
  omega

theorem H3_divs (k n : ℕ) (hn : n = 2 ^ (k + 3)) : n / 2 = 2 ^ (k + 2) ∧ n / 4 = 2 ^ (k + 1) ∧
    n / 8 = 2 ^ k := by
  subst hn
  refine ⟨?_, ?_, ?_⟩
  · rw [show 2 ^ (k + 3) = 2 ^ (k + 2) * 2 by ring, Nat.mul_div_cancel _ (by norm_num)]
  · rw [show 2 ^ (k + 3) = 2 ^ (k + 1) * 4 by ring, Nat.mul_div_cancel _ (by norm_num)]
  · rw [show 2 ^ (k + 3) = 2 ^ k * 8 by ring, Nat.mul_div_cancel _ (by norm_num)]

theorem H3_pow_one_add {M : Type*} [Monoid M] (x : M) (d a : ℕ) (hx : x ^ d = 1) (ha : d ∣ a) :
    x ^ (1 + a) = x := by
  obtain ⟨c, rfl⟩ := ha
  rw [pow_add, pow_one, pow_mul, hx, one_pow, mul_one]

theorem H3_pow_pred {M : Type*} [Monoid M] (x : M) (a : ℕ) (ha : 1 ≤ a) : x ^ a = x ^ (a - 1) * x := by
  rw [← pow_succ, Nat.sub_add_cancel ha]

theorem H3_sub_one_mul (P l : ℕ) (hP : 1 ≤ P) : (P - 1) * l + l = P * l := by
  obtain ⟨P', rfl⟩ : ∃ P', P = P' + 1 := ⟨P - 1, by omega⟩
  rw [Nat.add_sub_cancel]; ring

/-- For `n = 2^(k+3)`: `Q = 3^(n/4) = 1 + n·(2m+1)`. -/
theorem H3_QQ (k n : ℕ) (hn : n = 2 ^ (k + 3)) : ∃ m : ℕ, QQ n = 1 + n * (2 * m + 1) := by
  obtain ⟨m, hm⟩ := H3_three_pow k
  refine ⟨m, ?_⟩
  rw [QQ, (H3_divs k n hn).2.1, hm, hn]

/-- Every `n`-th root of unity (`n = 2^(k+3)`) is fixed by `x ↦ x^Q`. -/
theorem H3_root_fixed {M : Type*} [Monoid M] (k n : ℕ) (hn : n = 2 ^ (k + 3)) (ξ : M) (hξ : ξ ^ n = 1) :
    ξ ^ QQ n = ξ := by
  obtain ⟨m, hm⟩ := H3_QQ k n hn
  rw [hm]
  exact H3_pow_one_add ξ n _ hξ (Dvd.intro _ rfl)

/-! ## 2. The group `(ℤ/2^(k+3))^×` and the action of `3` -/

section ZModPow2

variable (k : ℕ)

theorem H3_three_pow_eq_one : (3 : ZMod (2 ^ (k + 3))) ^ (2 ^ (k + 1)) = 1 := by
  obtain ⟨m, hm⟩ := H3_three_pow k
  have h : (3 : ZMod (2 ^ (k + 3))) ^ (2 ^ (k + 1)) = ((3 ^ (2 ^ (k + 1)) : ℕ) : ZMod (2 ^ (k + 3))) := by
    simp
  rw [h, hm, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero, Nat.cast_one]

theorem H3_three_pow_ne_one : (3 : ZMod (2 ^ (k + 3))) ^ (2 ^ k) ≠ 1 := by
  have h : (3 : ZMod (2 ^ (k + 3))) ^ (2 ^ k) = ((3 ^ (2 ^ k) : ℕ) : ZMod (2 ^ (k + 3))) := by simp
  have h1 : (1 : ZMod (2 ^ (k + 3))) = ((1 : ℕ) : ZMod (2 ^ (k + 3))) := Nat.cast_one.symm
  rw [h, h1, Ne, ZMod.natCast_eq_natCast_iff']
  cases k with
  | zero => norm_num
  | succ k =>
    obtain ⟨m, hm⟩ := H3_three_pow k
    rw [hm, show k + 1 + 3 = k + 4 from rfl, H3_mod]
    have h16 : 2 ^ (k + 4) = 16 * 2 ^ k := by ring
    have h8 : 2 ^ (k + 3) = 8 * 2 ^ k := by ring
    have h0 : 0 < 2 ^ k := pow_pos two_pos _
    rw [Nat.mod_eq_of_lt (by omega : 1 < 2 ^ (k + 4))]
    omega

theorem H3_orderOf_three : orderOf (3 : ZMod (2 ^ (k + 3))) = 2 ^ (k + 1) :=
  orderOf_eq_prime_pow (H3_three_pow_ne_one k) (H3_three_pow_eq_one k)

theorem H3_neg_one_ne_pow (j : ℕ) : (-1 : ZMod (2 ^ (k + 3))) ≠ 3 ^ j := by
  intro h
  have hd : 8 ∣ 2 ^ (k + 3) := ⟨2 ^ k, by ring⟩
  have h8 := congrArg (ZMod.castHom hd (ZMod 8)) h
  simp only [map_neg, map_one, map_pow, map_ofNat] at h8
  have h32 : (3 : ZMod 8) ^ 2 = 1 := by decide
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
  · rw [pow_mul, h32, one_pow] at h8
    exact absurd h8 (by decide)
  · rw [pow_succ, pow_mul, h32, one_pow, one_mul] at h8
    exact absurd h8 (by decide)

theorem H3_isUnit_three : IsUnit (3 : ZMod (2 ^ (k + 3))) :=
  IsUnit.of_pow_eq_one (H3_three_pow_eq_one k) (pow_ne_zero _ two_ne_zero)

/-- `(ℤ/2^(k+3))^× = {±3^j}`. -/
theorem H3_unit_decomp (x : ZMod (2 ^ (k + 3))) (hx : IsUnit x) :
    ∃ j : ℕ, x = 3 ^ j ∨ x = -3 ^ j := by
  classical
  obtain ⟨u3, hu3⟩ : ∃ u : (ZMod (2 ^ (k + 3)))ˣ, (u : ZMod (2 ^ (k + 3))) = 3 :=
    ⟨_, (H3_isUnit_three k).unit_spec⟩
  have hord : orderOf u3 = 2 ^ (k + 1) := by
    rw [← orderOf_units, hu3, H3_orderOf_three]
  have hcardG : Nat.card (ZMod (2 ^ (k + 3)))ˣ = 2 ^ (k + 2) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp
  have hindex : (Subgroup.zpowers u3).index = 2 := by
    have h := Subgroup.card_mul_index (Subgroup.zpowers u3)
    rw [Nat.card_zpowers, hord, hcardG] at h
    have h' : 2 ^ (k + 1) * (Subgroup.zpowers u3).index = 2 ^ (k + 1) * 2 := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left (pow_pos two_pos _) h'
  have hpow : ∀ v : (ZMod (2 ^ (k + 3)))ˣ, v ∈ Subgroup.zpowers u3 →
      ∃ j : ℕ, (v : ZMod (2 ^ (k + 3))) = 3 ^ j := by
    intro v hv
    rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hv
    obtain ⟨j, rfl⟩ := hv
    exact ⟨j, by rw [Units.val_pow_eq_pow_val, hu3]⟩
  have hneg : (-1 : (ZMod (2 ^ (k + 3)))ˣ) ∉ Subgroup.zpowers u3 := by
    intro h
    obtain ⟨j, hj⟩ := hpow _ h
    exact H3_neg_one_ne_pow k j (by simpa using hj)
  by_cases hxH : hx.unit ∈ Subgroup.zpowers u3
  · obtain ⟨j, hj⟩ := hpow _ hxH
    exact ⟨j, Or.inl (by simpa using hj)⟩
  · have hm : hx.unit * (-1) ∈ Subgroup.zpowers u3 := by
      rw [Subgroup.mul_mem_iff_of_index_two hindex]
      exact iff_of_false hxH hneg
    obtain ⟨j, hj⟩ := hpow _ hm
    have hj' : -x = 3 ^ j := by simpa using hj
    exact ⟨j, Or.inr (by rw [← hj', neg_neg])⟩

theorem H3_isUnit_of_odd (x : ZMod (2 ^ (k + 3))) (hx : Odd x.val) : IsUnit x := by
  rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega)]
  exact Nat.coprime_two_right.mpr hx

end ZModPow2

/-! ## 3. Orbits of `k ↦ 3k` -/

theorem H3_orbit_mul_pow {N : ℕ} [NeZero N] (c : ZMod N) (P : ℕ) (hP : (3 : ZMod N) ^ P = 1)
    (hP0 : 1 ≤ P) (i : ℕ) : orbit 3 (c * 3 ^ i) = orbit 3 c := by
  ext j
  simp only [orbit, Finset.mem_filter, Finset.mem_univ, true_and, Nat.cast_ofNat]
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨l + i, by ring⟩
  · rintro ⟨l, rfl⟩
    refine ⟨l + (P - 1) * i, ?_⟩
    have hexp : l + (P - 1) * i + i = l + P * i := by
      rw [add_assoc, H3_sub_one_mul P i hP0]
    calc (3 : ZMod N) ^ l * c = 3 ^ (l + P * i) * c := by rw [pow_add, pow_mul, hP, one_pow, mul_one]
      _ = 3 ^ (l + (P - 1) * i + i) * c := by rw [hexp]
      _ = 3 ^ (l + (P - 1) * i) * (c * 3 ^ i) := by ring

theorem H3_orbit_neg_one {N : ℕ} [NeZero N] : orbit 3 (-1 : ZMod N) = inv (orbit 3 1) := by
  ext j
  simp only [orbit, inv, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Nat.cast_ofNat]
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨3 ^ l * 1, ⟨l, rfl⟩, by ring⟩
  · rintro ⟨a, ⟨l, rfl⟩, rfl⟩
    exact ⟨l, by ring⟩

theorem H3_inv_inv {N : ℕ} [NeZero N] (O : Finset (ZMod N)) : inv (inv O) = O := by
  simp [inv, Finset.image_image]

theorem H3_inv_card {N : ℕ} [NeZero N] (O : Finset (ZMod N)) : (inv O).card = O.card :=
  Finset.card_image_of_injective _ neg_injective

section ZModPow2Orbits

variable (k : ℕ)

theorem H3_orbit_odd (x : ZMod (2 ^ (k + 3))) (hx : Odd x.val) :
    orbit 3 x = orbit 3 1 ∨ orbit 3 x = inv (orbit 3 1) := by
  obtain ⟨j, rfl | rfl⟩ := H3_unit_decomp k x (H3_isUnit_of_odd k x hx)
  · left
    rw [← one_mul ((3 : ZMod (2 ^ (k + 3))) ^ j),
      H3_orbit_mul_pow 1 _ (H3_three_pow_eq_one k) Nat.one_le_two_pow]
  · right
    rw [← H3_orbit_neg_one, show -(3 : ZMod (2 ^ (k + 3))) ^ j = -1 * 3 ^ j by ring,
      H3_orbit_mul_pow (-1) _ (H3_three_pow_eq_one k) Nat.one_le_two_pow]

theorem H3_disjoint : Disjoint (orbit 3 (1 : ZMod (2 ^ (k + 3)))) (inv (orbit 3 1)) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [orbit, inv, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Nat.cast_ofNat] at ha hb
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨b, ⟨l, rfl⟩, hb⟩ := hb
  apply H3_neg_one_ne_pow k (i + (2 ^ (k + 1) - 1) * l)
  have hP := H3_three_pow_eq_one k
  have hexp : (2 ^ (k + 1) - 1) * l + l = 2 ^ (k + 1) * l := H3_sub_one_mul _ l Nat.one_le_two_pow
  calc (-1 : ZMod (2 ^ (k + 3))) = -((3 ^ (2 ^ (k + 1))) ^ l) := by rw [hP, one_pow]
    _ = -(3 ^ ((2 ^ (k + 1) - 1) * l + l)) := by rw [hexp, pow_mul]
    _ = -(3 ^ l * 1) * 3 ^ ((2 ^ (k + 1) - 1) * l) := by ring
    _ = 3 ^ i * 1 * 3 ^ ((2 ^ (k + 1) - 1) * l) := by rw [hb]
    _ = 3 ^ (i + (2 ^ (k + 1) - 1) * l) := by ring

theorem H3_orbit_one_card : (orbit 3 (1 : ZMod (2 ^ (k + 3)))).card = 2 ^ (k + 1) := by
  have hO : orbit 3 (1 : ZMod (2 ^ (k + 3))) =
      (range (2 ^ (k + 1))).image (fun i => (3 : ZMod (2 ^ (k + 3))) ^ i) := by
    ext j
    simp only [orbit, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_range, Nat.cast_ofNat, mul_one]
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨i % 2 ^ (k + 1), Nat.mod_lt _ (pow_pos two_pos _), ?_⟩
      rw [← H3_orderOf_three k, pow_mod_orderOf]
    · rintro ⟨i, -, rfl⟩
      exact ⟨i, rfl⟩
  rw [hO, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  rw [Finset.coe_range, ← H3_orderOf_three k] at ha hb
  exact pow_injOn_Iio_orderOf ha hb hab

theorem H3_half_eq : half (2 ^ (k + 3)) = ((2 ^ (k + 2) : ℕ) : ZMod (2 ^ (k + 3))) := by
  rw [half, (H3_divs k _ rfl).1]

theorem H3_two_mul_half : (2 : ZMod (2 ^ (k + 3))) * half (2 ^ (k + 3)) = 0 := by
  rw [H3_half_eq, show (2 : ZMod (2 ^ (k + 3))) = ((2 : ℕ) : ZMod (2 ^ (k + 3))) by norm_cast,
    ← Nat.cast_mul, show 2 * 2 ^ (k + 2) = 2 ^ (k + 3) by ring, ZMod.natCast_self]

theorem H3_two_mul_eq_zero (d : ZMod (2 ^ (k + 3))) (hd : 2 * d = 0) :
    d = 0 ∨ d = half (2 ^ (k + 3)) := by
  have hlt := ZMod.val_lt d
  rw [← ZMod.natCast_zmod_val d] at hd ⊢
  rw [show (2 : ZMod (2 ^ (k + 3))) = ((2 : ℕ) : ZMod (2 ^ (k + 3))) by norm_cast, ← Nat.cast_mul,
    ZMod.natCast_eq_zero_iff] at hd
  have hd' : 2 * 2 ^ (k + 2) ∣ 2 * d.val := by
    rw [show 2 * 2 ^ (k + 2) = 2 ^ (k + 3) by ring]; exact hd
  obtain ⟨c, hc⟩ := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) hd'
  rw [hc] at hlt
  have hc2 : c < 2 := by
    by_contra hcon
    rw [not_lt] at hcon
    have h1 : 2 ^ (k + 2) * 2 ≤ 2 ^ (k + 2) * c := Nat.mul_le_mul_left _ hcon
    have h2 : 2 ^ (k + 3) = 2 ^ (k + 2) * 2 := by ring
    omega
  interval_cases c
  · left; rw [hc]; simp
  · right; rw [hc, H3_half_eq, mul_one]

theorem H3_addOrder_half (j : ℕ) (hj : 1 ≤ j) (x z : ZMod (2 ^ (k + 3))) (hx : addOrderOf x = 2 ^ j)
    (hz : 2 * z = x) : addOrderOf z = 2 ^ (j + 1) := by
  have key : ∀ i : ℕ, (2 ^ (i + 1)) • z = (2 ^ i) • x := by
    intro i; rw [nsmul_eq_mul, nsmul_eq_mul, ← hz]; push_cast; ring
  apply addOrderOf_eq_prime_pow
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [key i]
    apply nsmul_ne_zero_of_lt_addOrderOf (pow_ne_zero _ two_ne_zero)
    rw [hx, pow_succ]
    have := pow_pos (two_pos : 0 < 2) i
    omega
  · rw [key j, ← hx]
    exact addOrderOf_nsmul_eq_zero x

theorem H3_exists_half (j : ℕ) (hj : j ≤ k + 2) (x : ZMod (2 ^ (k + 3))) (hx : addOrderOf x = 2 ^ j) :
    ∃ z : ZMod (2 ^ (k + 3)), 2 * z = x := by
  have h0 : (2 ^ (k + 2)) • x = 0 := by
    rw [← addOrderOf_dvd_iff_nsmul_eq_zero, hx]; exact pow_dvd_pow 2 hj
  rw [nsmul_eq_mul, ← ZMod.natCast_zmod_val x, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h0
  have h0' : 2 ^ (k + 2) * 2 ∣ 2 ^ (k + 2) * x.val := by
    rw [show 2 ^ (k + 2) * 2 = 2 ^ (k + 3) by ring]; exact h0
  obtain ⟨b, hb⟩ := Nat.dvd_of_mul_dvd_mul_left (pow_pos two_pos _) h0'
  refine ⟨(b : ZMod (2 ^ (k + 3))), ?_⟩
  rw [← ZMod.natCast_zmod_val x, hb, Nat.cast_mul, Nat.cast_ofNat]

theorem H3_sqrt_set (x z : ZMod (2 ^ (k + 3))) (hz : 2 * z = x) :
    {w : ZMod (2 ^ (k + 3)) | 2 * w = x} = {z, z + half (2 ^ (k + 3))} := by
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hw
    have hd : 2 * (w - z) = 0 := by rw [mul_sub, hw, hz, sub_self]
    rcases H3_two_mul_eq_zero k (w - z) hd with h | h
    · left; exact sub_eq_zero.mp h
    · right; rw [← h]; ring
  · rintro (rfl | rfl)
    · exact hz
    · rw [mul_add, hz, H3_two_mul_half, add_zero]

theorem H3_topOrbits : topOrbits (2 ^ (k + 3)) 3 = {orbit 3 1, inv (orbit 3 1)} := by
  ext O
  simp only [topOrbits, topLayer, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  have hN : 1 < 2 ^ (k + 3) := by
    have : 2 ^ (k + 3) = 8 * 2 ^ k := by ring
    have := pow_pos (two_pos : 0 < 2) k
    omega
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact H3_orbit_odd k x hx
  · rintro (rfl | rfl)
    · refine ⟨1, ?_, rfl⟩
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hN]
      exact odd_one
    · refine ⟨-1, ?_, H3_orbit_neg_one⟩
      have h1 : (-1 : ZMod (2 ^ (k + 3))) = ((2 ^ (k + 3) - 1 : ℕ) : ZMod (2 ^ (k + 3))) := by
        rw [Nat.cast_sub hN.le, ZMod.natCast_self, Nat.cast_one, zero_sub]
      rw [h1, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      have : 2 ^ (k + 3) = 2 * 2 ^ (k + 2) := by ring
      exact ⟨2 ^ (k + 2) - 1, by omega⟩

end ZModPow2Orbits

/-! ## 4. Finite-field facts -/

theorem H3_two_ne_zero (m : ℕ) : (2 : GaloisField 3 m) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : GaloisField 3 m) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff (GaloisField 3 m) 3] at h'
  norm_num at h'

theorem H3_neg_one_ne_one (m : ℕ) : (-1 : GaloisField 3 m) ≠ 1 := by
  intro h
  apply H3_two_ne_zero m
  calc (2 : GaloisField 3 m) = 1 - (-1) := by ring
    _ = 0 := by rw [h, sub_self]

/-- A finite field contains a primitive `d`-th root of unity for every `d ∣ |K| - 1`. -/
theorem H3_exists_prim {K : Type*} [Field K] [Finite K] (d : ℕ) (hd : d ∣ Nat.card K - 1) (hd0 : d ≠ 0) :
    ∃ ζ : K, IsPrimitiveRoot ζ d := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units] at hg
  have hc : Nat.card K - 1 ≠ 0 := by
    have : 1 < Nat.card K := Finite.one_lt_card
    omega
  have hdiv : (Nat.card K - 1) / d ∣ orderOf g := by rw [hg]; exact Nat.div_dvd_of_dvd hd
  have hne : (Nat.card K - 1) / d ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hc) hd) (Nat.pos_of_ne_zero hd0)).ne'
  have ho : orderOf (g ^ ((Nat.card K - 1) / d)) = d := by
    rw [orderOf_pow_of_dvd hne hdiv, hg, Nat.div_div_self hd hc]
  refine ⟨((g ^ ((Nat.card K - 1) / d) : Kˣ) : K), ?_⟩
  have := IsPrimitiveRoot.orderOf (g ^ ((Nat.card K - 1) / d))
  rw [ho] at this
  exact IsPrimitiveRoot.coe_units_iff.mpr this

/-! ## 5. The six statements -/

/-- Row 7a — Theorem 3.1 "fix `ξ_0 ∈ F` of order `n`" with Step 1 (`μ_n ⊂ k_0 ⊂ F`). -/
theorem thm_3_1_xi0_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) :
    (∃ ξ0 : GaloisField 3 (n / 2), IsPrimitiveRoot ξ0 n) ∧
      ∀ ξ : GaloisField 3 (n / 2), ξ ^ n = 1 → ξ ^ QQ n = ξ := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 3 := ⟨e - 3, by omega⟩
  obtain ⟨hn2, -, -⟩ := H3_divs k n hne
  refine ⟨?_, fun ξ hξ => H3_root_fixed k n hne ξ hξ⟩
  apply H3_exists_prim
  · rw [GaloisField.card 3 (n / 2) (by rw [hn2]; positivity), hn2]
    obtain ⟨m, hm⟩ := H3_three_pow (k + 1)
    rw [show 2 ^ (k + 2) = 2 ^ (k + 1 + 1) from rfl, hm, Nat.add_sub_cancel_left, hne]
    exact ⟨2 * (2 * m + 1), by ring⟩
  · rw [hne]; positivity

/-- Row 7d — s3_pow2.tex:17. -/
theorem thm_3_1_theta_set_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) :
    Nat.card {θ : GaloisField 3 (n / 2) // θ ^ (QQ n - 1) = -1} = QQ n - 1 ∧ 2 * (QQ n - 1) ∣ 3 ^ (n / 2) - 1 ∧
      {θ : GaloisField 3 (n / 2) | θ ^ (QQ n - 1) = -1} =
        {θ | θ ^ (2 * (QQ n - 1)) = 1} \ {θ | θ ^ (QQ n - 1) = 1} := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 3 := ⟨e - 3, by omega⟩
  obtain ⟨hn2, hn4, -⟩ := H3_divs k n hne
  obtain ⟨m, hm⟩ := H3_QQ k n hne
  have hQ1 : QQ n - 1 = n * (2 * m + 1) := by rw [hm, Nat.add_sub_cancel_left]
  have hQpos : 0 < QQ n - 1 := by rw [hQ1, hne]; positivity
  have hcard : 3 ^ (n / 2) = QQ n ^ 2 := by
    rw [QQ, ← pow_mul, hn2, hn4]; congr 1
  have hdvd : 2 * (QQ n - 1) ∣ 3 ^ (n / 2) - 1 := by
    rw [hcard, hQ1, hm, hne]
    have h : (1 + 2 ^ (k + 3) * (2 * m + 1)) ^ 2 =
        2 * (2 ^ (k + 3) * (2 * m + 1)) * (1 + 2 ^ (k + 2) * (2 * m + 1)) + 1 := by ring
    rw [h, Nat.add_sub_cancel]
    exact Dvd.intro _ rfl
  have hset : {θ : GaloisField 3 (n / 2) | θ ^ (QQ n - 1) = -1} =
      {θ | θ ^ (2 * (QQ n - 1)) = 1} \ {θ | θ ^ (QQ n - 1) = 1} := by
    ext θ
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff]
    constructor
    · intro h
      exact ⟨by rw [pow_mul', h]; norm_num, by rw [h]; exact H3_neg_one_ne_one _⟩
    · rintro ⟨h1, h2⟩
      rw [pow_mul', pow_two] at h1
      rcases mul_self_eq_one_iff.mp h1 with h | h
      · exact absurd h h2
      · exact h
  refine ⟨?_, hdvd, hset⟩
  have hdvd2 : 2 * (QQ n - 1) ∣ Nat.card (GaloisField 3 (n / 2)) - 1 := by
    rw [GaloisField.card 3 (n / 2) (by rw [hn2]; positivity)]; exact hdvd
  obtain ⟨ζ, hζ⟩ := H3_exists_prim (K := GaloisField 3 (n / 2)) (2 * (QQ n - 1)) hdvd2 (by omega)
  have hζ1 : ζ ^ (QQ n - 1) = -1 := by
    have h1 : ζ ^ (QQ n - 1) * ζ ^ (QQ n - 1) = 1 := by
      rw [← pow_two, ← pow_mul']; exact hζ.pow_eq_one
    have h2 : ζ ^ (QQ n - 1) ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by omega) (by omega)
    rcases mul_self_eq_one_iff.mp h1 with h | h
    · exact absurd h h2
    · exact h
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hprim : IsPrimitiveRoot (ζ ^ 2) (QQ n - 1) := hζ.pow (by omega) rfl
  have hcardR : (Polynomial.nthRootsFinset (QQ n - 1) (1 : GaloisField 3 (n / 2))).card = QQ n - 1 :=
    hprim.card_nthRootsFinset
  let eqv : {θ : GaloisField 3 (n / 2) // θ ^ (QQ n - 1) = -1} ≃
      {x : GaloisField 3 (n / 2) // x ∈ Polynomial.nthRootsFinset (QQ n - 1) (1 : GaloisField 3 (n / 2))} :=
    { toFun := fun θ => ⟨ζ⁻¹ * θ.1, by
        rw [Polynomial.mem_nthRootsFinset hQpos, mul_pow, inv_pow, hζ1, θ.2]; norm_num⟩
      invFun := fun x => ⟨ζ * x.1, by
        have hx := (Polynomial.mem_nthRootsFinset hQpos (1 : GaloisField 3 (n / 2))).mp x.2
        rw [mul_pow, hζ1, hx, mul_one]⟩
      left_inv := fun θ => by ext; simp [hζ0]
      right_inv := fun x => by ext; simp [hζ0] }
  rw [Nat.card_congr eqv, Nat.card_eq_finsetCard, hcardR]

/-- Row 7e — proof of Theorem 3.1, Step 1 (s3_pow2.tex:31-35). -/
theorem thm_3_1_step1_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) :
    padicValNat 2 (3 ^ (n / 2) - 1) = e + 1 ∧ padicValNat 2 (QQ n - 1) = e ∧
      orderOf (3 : ZMod n) = 2 ^ (e - 2) ∧
      (∀ x : ZMod n, IsUnit x → ∃ k : ℕ, x = (3 : ZMod n) ^ k ∨ x = -(3 : ZMod n) ^ k) ∧
      (∀ k : ℕ, (-1 : ZMod n) ≠ (3 : ZMod n) ^ k) ∧
      (∀ x : ZMod n, Odd x.val → orbit 3 x = orbit 3 1 ∨ orbit 3 x = inv (orbit 3 1)) ∧
      Disjoint (orbit 3 (1 : ZMod n)) (inv (orbit 3 1)) ∧
      ∀ (j : ℕ), 1 ≤ j → j ≤ e - 1 → ∀ x : ZMod n, addOrderOf x = 2 ^ j →
        ∃ z : ZMod n, addOrderOf z = 2 ^ (j + 1) ∧ {w : ZMod n | 2 * w = x} = {z, z + half n} ∧
          addOrderOf (z + half n) = 2 ^ (j + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 3 := ⟨e - 3, by omega⟩
  subst hne
  obtain ⟨hn2, hn4, -⟩ := H3_divs k _ rfl
  refine ⟨?_, ?_, ?_, H3_unit_decomp k, H3_neg_one_ne_pow k, H3_orbit_odd k, H3_disjoint k, ?_⟩
  · obtain ⟨m, hm⟩ := H3_three_pow (k + 1)
    rw [hn2, show 2 ^ (k + 2) = 2 ^ (k + 1 + 1) from rfl, hm, Nat.add_sub_cancel_left, H3_padic]
  · obtain ⟨m, hm⟩ := H3_three_pow k
    rw [QQ, hn4, hm, Nat.add_sub_cancel_left, H3_padic]
  · rw [H3_orderOf_three, show k + 3 - 2 = k + 1 by omega]
  · intro j hj1 hj2 x hx
    obtain ⟨z, hz⟩ := H3_exists_half k j (by omega) x hx
    refine ⟨z, H3_addOrder_half k j hj1 x z hx hz, H3_sqrt_set k x z hz, ?_⟩
    apply H3_addOrder_half k j hj1 x _ hx
    rw [mul_add, hz, H3_two_mul_half, add_zero]

/-- Coverage — s3_pow2.tex:85-96 (set-up of Section 3.2), `n = 2^e`, `e ≥ 4`. -/
theorem sec_3_2_setup_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 4 ≤ e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) :
    QQ n = qq n ^ 2 ∧ orderOf (iota n ξ0) = 4 ∧ iota n ξ0 ^ QQ n = iota n ξ0 ∧ iota n ξ0 ^ 9 = iota n ξ0 ∧
      (∀ x ∈ (Vsp n : Set (GaloisField 3 (n / 2))), ∀ x' ∈ (Vsp n : Set (GaloisField 3 (n / 2))), x + x' ∈ Vsp n) ∧
      (∀ θ : GaloisField 3 (n / 2), (θ ∈ Vsp n ∧ θ ≠ 0) ↔ θ ^ (QQ n - 1) = -1) ∧
      qq n % 4 = 1 ∧ iota n ξ0 ^ qq n = iota n ξ0 ∧ qq n % n = 1 + n / 2 ∧
      (∀ θ : GaloisField 3 (n / 2), θ ^ (QQ n - 1) = -1 →
        (θ ^ (1 + qq n)) ^ (qq n - 1) = -1 ∧ (θ ^ (1 + qq n)) ^ qq n = -θ ^ (1 + qq n) ∧
          (θ ^ (1 + qq n)) ^ QQ n = θ ^ (1 + qq n)) ∧
      ∀ x : GaloisField 3 (n / 2), Nm n x = yPlus n x ^ 2 - yMinus n x ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 4 := ⟨e - 4, by omega⟩
  have hdivs := H3_divs (k + 1) n hne
  have hn2 : n / 2 = 2 ^ (k + 3) := hdivs.1
  have hn4 : n / 4 = 2 ^ (k + 2) := hdivs.2.1
  have hn8 : n / 8 = 2 ^ (k + 1) := hdivs.2.2
  have hn : n = 2 ^ (k + 2) * 4 := by rw [hne]; ring
  have h4n : 4 ∣ n := ⟨2 ^ (k + 2), by rw [hn]; ring⟩
  obtain ⟨m, hm⟩ := H3_three_pow k
  have hq : qq n = 1 + 2 ^ (k + 3) * (2 * m + 1) := by rw [qq, hn8, hm]
  have hq1 : 1 ≤ qq n := by rw [hq]; omega
  obtain ⟨m', hm'⟩ := H3_QQ (k + 1) n hne
  have hQ1 : 1 ≤ QQ n := by rw [hm']; omega
  have hQpos : QQ n - 1 ≠ 0 := by
    rw [hm', Nat.add_sub_cancel_left]; exact (Nat.mul_pos (by rw [hne]; positivity) (by omega)).ne'
  have hQq : QQ n = qq n ^ 2 := by
    rw [QQ, qq, hn4, hn8, ← pow_mul]; congr 1
  have hιprim : IsPrimitiveRoot (iota n ξ0) 4 := hξ0.pow (by rw [hne]; positivity) (by omega)
  have hι4 : iota n ξ0 ^ 4 = 1 := hιprim.pow_eq_one
  refine ⟨hQq, hιprim.eq_orderOf.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ι^Q = ι
    rw [hm']
    exact H3_pow_one_add _ 4 _ hι4 (Dvd.dvd.mul_right h4n _)
  · -- ι^9 = ι
    exact H3_pow_one_add _ 4 8 hι4 (by norm_num)
  · -- V is closed under addition
    intro x hx x' hx'
    simp only [Vsp, Set.mem_ofPred_eq, QQ] at hx hx' ⊢
    rw [add_pow_char_pow, hx, hx', neg_add]
  · -- non-zero elements of V = parameters
    intro θ
    simp only [Vsp, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h, h0⟩
      rw [H3_pow_pred θ _ hQ1] at h
      have h' : θ ^ (QQ n - 1) * θ = (-1) * θ := by rw [h]; ring
      exact mul_right_cancel₀ h0 h'
    · intro h
      have h0 : θ ≠ 0 := by
        rintro rfl
        rw [zero_pow hQpos] at h
        exact one_ne_zero (neg_eq_zero.mp h.symm)
      exact ⟨by rw [H3_pow_pred θ _ hQ1, h]; ring, h0⟩
  · -- q ≡ 1 mod 4
    rw [hq, show 1 + 2 ^ (k + 3) * (2 * m + 1) = 1 + 4 * (2 ^ (k + 1) * (2 * m + 1)) by ring,
      Nat.add_mul_mod_self_left]
  · -- ι^q = ι
    rw [hq]
    exact H3_pow_one_add _ 4 _ hι4 ⟨2 ^ (k + 1) * (2 * m + 1), by ring⟩
  · -- q ≡ 1 + n/2 mod n
    rw [hq, hn2, hne]
    exact H3_mod k m
  · -- ν facts
    intro θ hθ
    have hexp : (1 + qq n) * (qq n - 1) = QQ n - 1 := by
      rw [hQq]
      obtain ⟨r, hr⟩ : ∃ r, qq n = r + 1 := ⟨qq n - 1, by omega⟩
      rw [hr, Nat.add_sub_cancel, show (r + 1) ^ 2 = (1 + (r + 1)) * r + 1 by ring, Nat.add_sub_cancel]
    have hν1 : (θ ^ (1 + qq n)) ^ (qq n - 1) = -1 := by rw [← pow_mul, hexp, hθ]
    have hev : Even (1 + qq n) := ⟨1 + 2 ^ (k + 2) * (2 * m + 1), by rw [hq]; ring⟩
    refine ⟨hν1, ?_, ?_⟩
    · rw [H3_pow_pred _ _ hq1, hν1]; ring
    · rw [H3_pow_pred _ _ hQ1, ← hexp, mul_comm (1 + qq n) (qq n - 1), pow_mul, hν1, hev.neg_one_pow,
        one_mul]
  · -- N(x) = (x^+)^2 - (x^-)^2
    intro x
    have h2 := H3_two_ne_zero (n / 2)
    simp only [Nm, yPlus, yMinus, bar]
    rw [pow_add, pow_one]
    field_simp
    ring

/-- Row 13 — Remark 3.6(a),(b) (s3_pow2.tex:217-220). -/
theorem rem_3_6_proved :
    (∀ (n e : ℕ) [NeZero n], n = 2 ^ e → 4 ≤ e → ∀ ξ0 : GaloisField 3 (n / 2), IsPrimitiveRoot ξ0 n →
      (∀ θ ∈ Vsp n, Tmap n ξ0 (ξ0⁻¹ * θ) = -(ξ0⁻¹ * Tmap n ξ0 θ)) ∧
      Set.BijOn (fun θ => ξ0⁻¹ * θ) (Vminus n ξ0) (Vplus n ξ0)) ∧
    (qq 8 = 3 ∧ qq 8 % 8 ≠ 5 ∧ ∀ ξ0 : GaloisField 3 (8 / 2), IsPrimitiveRoot ξ0 8 →
      ∀ x ∈ Vsp 8, Tmap 8 ξ0 (Tmap 8 ξ0 x) = -x) := by
  refine ⟨fun n e _ hne he ξ0 hξ0 => ?_, by norm_num [qq], by norm_num [qq], ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, e = k + 4 := ⟨e - 4, by omega⟩
    have hdivs := H3_divs (k + 1) n hne
    have hn2 : n / 2 = 2 ^ (k + 3) := hdivs.1
    have hn8 : n / 8 = 2 ^ (k + 1) := hdivs.2.2
    have hn' : n = 2 ^ (k + 3) * 2 := by rw [hne]; ring
    obtain ⟨m, hm⟩ := H3_three_pow k
    have hq : qq n = 1 + 2 ^ (k + 3) * (2 * m + 1) := by rw [qq, hn8, hm]
    have hnpos : 0 < n := by rw [hne]; positivity
    have hξ0' : ξ0 ≠ 0 := hξ0.ne_zero hnpos.ne'
    have hhalf : ξ0 ^ (n / 2) = -1 :=
      (hξ0.pow hnpos (show n = n / 2 * 2 by omega)).eq_neg_one_of_two_right
    have hξq : ξ0 ^ qq n = -ξ0 := by
      rw [hq, show 1 + 2 ^ (k + 3) * (2 * m + 1) = 1 + n / 2 + n * m by rw [hn2, hne]; ring,
        pow_add, pow_add, pow_one, hhalf, pow_mul, hξ0.pow_eq_one, one_pow]
      ring
    have hξQ : ξ0 ^ QQ n = ξ0 := H3_root_fixed (k + 1) n hne ξ0 hξ0.pow_eq_one
    have key : ∀ θ : GaloisField 3 (n / 2), Tmap n ξ0 (ξ0⁻¹ * θ) = -(ξ0⁻¹ * Tmap n ξ0 θ) := by
      intro θ
      simp only [Tmap]
      rw [mul_pow, inv_pow, hξq, inv_neg]
      ring
    have key2 : ∀ θ : GaloisField 3 (n / 2), Tmap n ξ0 (ξ0 * θ) = -(ξ0 * Tmap n ξ0 θ) := by
      intro θ
      simp only [Tmap]
      rw [mul_pow, hξq]
      ring
    have hV : ∀ c θ : GaloisField 3 (n / 2), c ^ QQ n = c → θ ∈ Vsp n → c * θ ∈ Vsp n := by
      intro c θ hc hθ
      simp only [Vsp, Set.mem_ofPred_eq] at hθ ⊢
      rw [mul_pow, hc, hθ]
      ring
    refine ⟨fun θ _ => key θ, ?_, ?_, ?_⟩
    · intro θ hθ
      simp only [Vminus, Vplus, Set.mem_ofPred_eq] at hθ ⊢
      refine ⟨hV _ _ (by rw [inv_pow, hξQ]) hθ.1, ?_⟩
      rw [key, hθ.2]
      ring
    · intro a _ b _ hab
      exact mul_left_cancel₀ (inv_ne_zero hξ0') hab
    · intro φ hφ
      simp only [Vplus, Set.mem_ofPred_eq] at hφ
      rw [Set.mem_image]
      refine ⟨ξ0 * φ, ?_, ?_⟩
      · simp only [Vminus, Set.mem_ofPred_eq]
        exact ⟨hV _ _ hξQ hφ.1, by rw [key2, hφ.2]⟩
      · simp only [inv_mul_cancel_left₀ hξ0']
  · intro ξ0 hξ0 x hx
    simp only [Vsp, Set.mem_ofPred_eq] at hx
    have hQ8 : QQ 8 = 9 := by norm_num [QQ]
    rw [hQ8] at hx
    have h8 : ξ0 ^ 8 = 1 := hξ0.pow_eq_one
    have hq8 : qq 8 = 3 := by norm_num [qq]
    have hi8 : iota 8 ξ0 = ξ0 ^ 2 := by norm_num [iota]
    simp only [Tmap, hq8, hi8]
    calc ξ0 ^ 2 * (ξ0 ^ 2 * x ^ 3) ^ 3 = ξ0 ^ 8 * x ^ 9 := by ring
      _ = -x := by rw [h8, hx, one_mul]

/-- Coverage — s4_normfree.tex:24: for `n = 2^e` there is one pair, `L_1 = n/4`. -/
theorem thm_4_1_pow2_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) :
    (topPairs n 3).card = 1 ∧ ∀ P ∈ topPairs n 3, pairLen P = n / 4 := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 3 := ⟨e - 3, by omega⟩
  subst hne
  have hP : topPairs (2 ^ (k + 3)) 3 = {{orbit 3 1, inv (orbit 3 1)}} := by
    rw [topPairs, H3_topOrbits k, Finset.image_insert, Finset.image_singleton, H3_inv_inv,
      Finset.pair_comm (inv (orbit 3 1)) (orbit 3 1),
      Finset.insert_eq_of_mem (Finset.mem_singleton_self _)]
  rw [hP]
  refine ⟨Finset.card_singleton _, ?_⟩
  intro P hPm
  rw [Finset.mem_singleton] at hPm
  subst hPm
  simp only [pairLen, Finset.biUnion_insert, Finset.singleton_biUnion, id_eq]
  rw [Finset.card_union_of_disjoint (H3_disjoint k), H3_inv_card, H3_orbit_one_card k,
    (H3_divs k _ rfl).2.1]
  omega

end Xia.Proofs

#print axioms Xia.Proofs.thm_3_1_xi0_proved
#print axioms Xia.Proofs.thm_3_1_theta_set_proved
#print axioms Xia.Proofs.thm_3_1_step1_proved
#print axioms Xia.Proofs.sec_3_2_setup_proved
#print axioms Xia.Proofs.thm_4_1_pow2_proved
#print axioms Xia.Proofs.rem_3_6_proved
