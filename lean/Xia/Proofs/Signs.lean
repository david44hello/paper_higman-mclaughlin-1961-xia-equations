/- Xia/Proofs/Signs.lean — proofs of the rows prop_4_3_odd, thm_6_4_i, prop_6_6_i, cor_6_5_sign, sec_6_1_R_kappa, sec_4_1_homog_of of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry

namespace Xia.Proofs

open Xia Finset

set_option linter.unusedSectionVars false

/-! ## Signs `sgn t = (-1)^{t.val}` on `ℤ/n`, `n` even -/

section Sgn

variable {K : Type*} [CommRing K] {n : ℕ} [NeZero n]

theorem H5_neg_one_pow_mod (hn : Even n) (m : ℕ) : (-1 : K) ^ (m % n) = (-1) ^ m := by
  rw [neg_one_pow_eq_pow_mod_two (m % n), neg_one_pow_eq_pow_mod_two m,
    Nat.mod_mod_of_dvd m (even_iff_two_dvd.mp hn)]

theorem H5_sgn_add (hn : Even n) (a b : ZMod n) : (sgn (a + b) : K) = sgn a * sgn b := by
  unfold sgn
  rw [ZMod.val_add, H5_neg_one_pow_mod hn, pow_add]

theorem H5_sgn_sq (a : ZMod n) : (sgn a : K) ^ 2 = 1 := by
  unfold sgn
  rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]

theorem H5_sgn_zero : (sgn (0 : ZMod n) : K) = 1 := by
  simp [sgn]

theorem H5_sgn_neg (hn : Even n) (a : ZMod n) : (sgn (-a) : K) = sgn a := by
  have h1 : (sgn (-a) : K) * sgn a = 1 := by
    rw [← H5_sgn_add hn, neg_add_cancel, H5_sgn_zero]
  have h2 := H5_sgn_sq (K := K) a
  linear_combination (sgn a : K) * h1 - (sgn (-a) : K) * h2

theorem H5_sgn_natCast (hn : Even n) (m : ℕ) : (sgn ((m : ℕ) : ZMod n) : K) = (-1) ^ m := by
  unfold sgn
  rw [ZMod.val_natCast, H5_neg_one_pow_mod hn]

theorem H5_sgn_intCast (hn : Even n) (z : ℤ) : (sgn ((z : ℤ) : ZMod n) : K) = (-1) ^ z.natAbs := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · rw [Int.cast_natCast, Int.natAbs_natCast, H5_sgn_natCast hn]
  · rw [Int.cast_neg, Int.cast_natCast, Int.natAbs_neg, Int.natAbs_natCast, H5_sgn_neg hn, H5_sgn_natCast hn]

theorem H5_sgn_one (hn : Even n) : (sgn (1 : ZMod n) : K) = -1 := by
  have h : (1 : ZMod n) = ((1 : ℕ) : ZMod n) := by rw [Nat.cast_one]
  rw [h, H5_sgn_natCast hn, pow_one]

theorem H5_val_half : (half n).val = n / 2 := by
  unfold half
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.div_lt_self (Nat.pos_of_ne_zero (NeZero.ne n)) (by norm_num))]

theorem H5_sgn_half (hn4 : 4 ∣ n) : (sgn (half n) : K) = 1 := by
  have hn : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) hn4)
  have he : Even (n / 2) := ⟨n / 4, by omega⟩
  unfold half
  rw [H5_sgn_natCast hn, he.neg_one_pow]

/-- `2 ∑_t sgn t = 0` for even `n` (shift the index by `1`). -/
theorem H5_sum_sgn_two (hn : Even n) : 2 * ∑ t : ZMod n, (sgn t : K) = 0 := by
  have h := Equiv.sum_comp (Equiv.addRight (1 : ZMod n)) (fun t => (sgn t : K))
  simp only [Equiv.coe_addRight, H5_sgn_add hn, H5_sgn_one hn, ← Finset.sum_mul] at h
  linear_combination -h

end Sgn

/-! ## Autocorrelation `R` and the square of `S` -/

section RS

variable {K : Type*} [CommRing K] {n : ℕ} [NeZero n]

theorem H5_S_sq_eq (hn : Even n) (y : ZMod n → K) : S y ^ 2 = ∑ s, sgn s * R y s := by
  unfold S R
  rw [sq, Finset.sum_mul_sum]
  have hinner : ∀ t : ZMod n,
      ∑ u, (sgn t : K) * y t * (sgn u * y u) = ∑ s, sgn s * (y t * y (t + s)) := by
    intro t
    calc ∑ u, (sgn t : K) * y t * (sgn u * y u)
        = ∑ s, (sgn t : K) * y t * (sgn (t + s) * y (t + s)) :=
          (Equiv.sum_comp (Equiv.addLeft t) (fun u => (sgn t : K) * y t * (sgn u * y u))).symm
      _ = ∑ s, sgn s * (y t * y (t + s)) := Finset.sum_congr rfl fun s _ => by
          rw [H5_sgn_add hn]
          have h2 := H5_sgn_sq (K := K) t
          linear_combination (sgn s * y t * y (t + s) : K) * h2
  rw [Finset.sum_congr rfl fun t _ => hinner t, Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => (Finset.mul_sum _ _ _).symm

theorem H5_R_neg (y : ZMod n → K) (s : ZMod n) : R y (-s) = R y s := by
  unfold R
  calc ∑ t, y t * y (t + -s) = ∑ u, y (u + s) * y (u + s + -s) :=
        (Equiv.sum_comp (Equiv.addRight s) (fun t => y t * y (t + -s))).symm
    _ = ∑ u, y u * y (u + s) := Finset.sum_congr rfl fun u _ => by
        rw [add_neg_cancel_right, mul_comm]

/-- (L3) with constant `c` gives `R(s) = c` for every `s ≠ n/2`. -/
theorem H5_R_of_L3 (hn : Even n) (c : K) (y : ZMod n → K) (hL3 : L3 c y) :
    ∀ s, s ≠ half n → R y s = c := by
  intro s hs
  have hval : s.val ≠ n / 2 := fun h => hs (ZMod.val_injective n (h.trans H5_val_half.symm))
  have hR : ∀ s' : ZMod n, s'.val < n / 2 → R y s' = c := by
    intro s' h'
    rw [← hL3 s' h']
    unfold R
    exact Finset.sum_congr rfl fun t _ => by rw [add_comm]
  obtain ⟨k, hk⟩ := hn
  have hlt := ZMod.val_lt s
  rcases lt_or_gt_of_ne hval with h | h
  · exact hR s h
  · rw [← H5_R_neg]
    apply hR
    rw [ZMod.neg_val', Nat.mod_eq_of_lt (by omega)]
    omega

/-- (L2) with constant `c` gives `R(n/2) = n c` (every `t` pairs with `t + n/2`). -/
theorem H5_R_half_of_L2 (hn : Even n) (c : K) (y : ZMod n → K) (hL2 : L2 c y) :
    R y (half n) = n * c := by
  obtain ⟨k, hk⟩ := hn
  have hhh : half n + half n = (0 : ZMod n) := by
    unfold half
    rw [← Nat.cast_add, show n / 2 + n / 2 = n by omega, ZMod.natCast_self]
  have hall : ∀ t : ZMod n, y t * y (t + half n) = c := by
    intro t
    by_cases ht : t.val < n / 2
    · exact hL2 t ht
    · have hlt := ZMod.val_lt t
      have h' : (t + half n).val < n / 2 := by
        rw [ZMod.val_add, H5_val_half, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      have := hL2 _ h'
      rw [add_assoc, hhh, add_zero] at this
      rw [mul_comm]
      exact this
  unfold R
  rw [Finset.sum_congr rfl fun t _ => hall t, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]

/-- For `4 ∣ n`, (L3) with constant `c` gives `S^2 = R(n/2) - c` (any field with `2 ≠ 0`). -/
theorem H5_S_sq_L3 {F : Type*} [Field F] (hn4 : 4 ∣ n) (h2 : (2 : F) ≠ 0) (c : F) (y : ZMod n → F)
    (hL3 : L3 c y) : S y ^ 2 = R y (half n) - c := by
  have hn : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) hn4)
  rw [H5_S_sq_eq hn, ← Finset.add_sum_erase _ _ (Finset.mem_univ (half n))]
  have hrest : ∑ s ∈ univ.erase (half n), (sgn s : F) * R y s = ∑ s ∈ univ.erase (half n), sgn s * c :=
    Finset.sum_congr rfl fun s hs => by rw [H5_R_of_L3 hn c y hL3 s (Finset.ne_of_mem_erase hs)]
  have hsum : ∑ s ∈ univ.erase (half n), (sgn s : F) = -1 := by
    have h0 : ∑ t : ZMod n, (sgn t : F) = 0 := (mul_eq_zero.mp (H5_sum_sgn_two hn)).resolve_left h2
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (half n)), H5_sgn_half hn4] at h0
    linear_combination h0
  rw [hrest, ← Finset.sum_mul, hsum, H5_sgn_half hn4]
  ring

/-- Frobenius in characteristic `r` (odd prime): (L1) gives `S^r = (-1)^σ S`. -/
theorem H5_S_pow_char {F : Type*} [CommRing F] (r : ℕ) [Fact r.Prime] [CharP F r] (hr : Odd r) (hn : Even n)
    (σ : ℤ) (y : ZMod n → F) (hL1 : L1 r σ y) : S y ^ r = (-1) ^ σ.natAbs * S y := by
  unfold S
  rw [sum_pow_char]
  have hterm : ∀ t : ZMod n, ((sgn t : F) * y t) ^ r = sgn t * y (t + σ) := by
    intro t
    rw [mul_pow, ← hL1 t]
    congr 1
    unfold sgn
    rw [← pow_mul, mul_comm t.val r, pow_mul, hr.neg_one_pow]
  rw [Finset.sum_congr rfl fun t _ => hterm t]
  calc ∑ t, (sgn t : F) * y (t + (σ : ZMod n))
        = ∑ t, sgn (t + (σ : ZMod n) - (σ : ZMod n)) * y (t + (σ : ZMod n)) := by
        simp only [add_sub_cancel_right]
    _ = ∑ u, sgn (u - (σ : ZMod n)) * y u :=
        Equiv.sum_comp (Equiv.addRight (σ : ZMod n)) (fun u => (sgn (u - (σ : ZMod n)) : F) * y u)
    _ = ∑ u, (-1) ^ σ.natAbs * (sgn u * y u) := Finset.sum_congr rfl fun u _ => by
        rw [sub_eq_add_neg, H5_sgn_add hn, H5_sgn_neg hn, H5_sgn_intCast hn]
        ring
    _ = _ := by rw [Finset.mul_sum]

end RS

/-! ## Arithmetic helpers -/

theorem H5_four_dvd {n a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) : 4 ∣ n := by
  rw [hn, show (4 : ℕ) = 2 ^ 2 by norm_num]
  exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _

theorem H5_two_ne_zero {F : Type*} [Field F] (r : ℕ) [CharP F r] (hr : ¬ r ∣ 2) : (2 : F) ≠ 0 := by
  intro h
  apply hr
  have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  exact (CharP.cast_eq_zero_iff F r 2).mp h'

/-! ## Row 16b — Proposition 4.3, odd part -/

theorem prop_4_3_odd_proved (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (_hodd : Odd nodd)
    (_h3 : ¬ 3 ∣ n) (σ : ℕ) (_hσ : σ ∣ n) (hσo : Odd σ) : NFSet n σ = ∅ := by
  have hn4 : 4 ∣ n := H5_four_dvd hn ha
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) hn4)
  rw [Set.eq_empty_iff_forall_notMem]
  rintro y ⟨hL1, hL3, hRm, -⟩
  have h2 : (2 : GaloisField 3 (n / σ)) ≠ 0 := H5_two_ne_zero 3 (by decide)
  have hS2 : S y ^ 2 = 1 := by rw [H5_S_sq_L3 hn4 h2 0 y hL3, hRm, sub_zero]
  have hS3 : S y ^ 3 = -S y := by
    rw [H5_S_pow_char 3 (by decide) hev _ y hL1, Int.natAbs_natCast, hσo.neg_one_pow, neg_one_mul]
  have h2S : 2 * S y = 0 := by linear_combination hS3 - S y * hS2
  have hS0 : S y = 0 := (mul_eq_zero.mp h2S).resolve_left h2
  rw [hS0] at hS2
  norm_num at hS2

/-! ## Rows 24(i), 26(i) — the sign obstruction in characteristic `r` -/

/-- Core: for `4 ∣ n`, `r ∤ pn` and `(-1)^{σ_r} ≠ (p/r)`, the norm-free `r`-system has no solution in any field of
characteristic `r`. -/
theorem H5_core (n r : ℕ) [NeZero n] [Fact r.Prime] (hn4 : 4 ∣ n) (hr : ¬ r ∣ pp n * n) (σr : ℤ)
    (hsign : (-1 : ℤ) ^ σr.natAbs ≠ legendreSym r (pp n : ℤ)) {F : Type*} [Field F] [CharP F r]
    (y : ZMod n → F) (hy : NFrEqs r σr y) : False := by
  obtain ⟨hL1, hL3, hRm, -⟩ := hy
  have hp : r.Prime := Fact.out
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) hn4)
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact hr (dvd_mul_of_dvd_right (even_iff_two_dvd.mp hev) _)
  have hrodd : Odd r := hp.odd_of_ne_two hr2
  have h2 : (2 : F) ≠ 0 :=
    H5_two_ne_zero r fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  -- S^2 = κ
  have hS2 : S y ^ 2 = kappa n F := by
    rw [H5_S_sq_L3 hn4 h2 _ y hL3, hRm]
    unfold kappa pp
    push_cast
    ring
  -- κ ≠ 0
  have hκ : kappa n F ≠ 0 := by
    have hc : ((n ^ 2 * pp n : ℕ) : F) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff F r]
      intro hd
      rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
      · exact hr (dvd_mul_of_dvd_right (hp.dvd_of_dvd_pow h) _)
      · exact hr (dvd_mul_of_dvd_left h _)
    unfold kappa
    exact_mod_cast hc
  have hS0 : S y ≠ 0 := by
    intro h
    apply hκ
    rw [← hS2, h]
    ring
  -- Frobenius: S^(r-1) = (-1)^σ
  have hSr := H5_S_pow_char r hrodd hev σr y hL1
  obtain ⟨k, hk⟩ := hrodd
  have hε : (S y ^ 2) ^ k = (-1) ^ σr.natAbs := by
    have h' : S y ^ (2 * k) * S y = (-1) ^ σr.natAbs * S y := by
      rw [← pow_succ, ← hk]
      exact hSr
    rw [← pow_mul]
    exact mul_right_cancel₀ hS0 h'
  -- Euler: κ^k = (κ/r) = (p/r)
  have hnr : ((n : ℤ) : ZMod r) ≠ 0 := by
    rw [Int.cast_natCast, Ne, CharP.cast_eq_zero_iff (ZMod r) r]
    exact fun h => hr (dvd_mul_of_dvd_right h _)
  have hpr : ((pp n : ℤ) : ZMod r) ≠ 0 := by
    rw [Int.cast_natCast, Ne, CharP.cast_eq_zero_iff (ZMod r) r]
    exact fun h => hr (dvd_mul_of_dvd_left h _)
  have hleg : (kappa n F) ^ k = ((legendreSym r (pp n : ℤ) : ℤ) : F) := by
    have e1 := legendreSym.eq_pow r ((n : ℤ) ^ 2 * (pp n : ℤ))
    rw [show r / 2 = k by omega, legendreSym.mul, legendreSym.sq_one' r hnr, one_mul] at e1
    have e2 := congrArg (ZMod.castHom (dvd_refl r) F) e1
    simp only [map_pow, map_intCast] at e2
    rw [e2]
    unfold kappa
    push_cast
    ring
  have hfin : ((((-1 : ℤ) ^ σr.natAbs : ℤ)) : F) = ((legendreSym r (pp n : ℤ) : ℤ) : F) := by
    rw [← hleg, ← hS2, hε]
    push_cast
    ring
  rcases neg_one_pow_eq_or ℤ σr.natAbs with h1 | h1 <;>
    rcases legendreSym.eq_one_or_neg_one r hpr with h2' | h2' <;>
    rw [h1, h2'] at hsign hfin
  · exact hsign rfl
  · push_cast at hfin
    exact h2 (by linear_combination hfin)
  · push_cast at hfin
    exact h2 (by linear_combination -hfin)
  · exact hsign rfl

theorem thm_6_4_i_proved (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a)
    (_hodd : Odd nodd) (hr : ¬ r ∣ pp n * n) (_hr1 : r % 2 ^ a ≠ 2 ^ a - 1) (σr : ℤ)
    (hsign : (-1 : ℤ) ^ σr.natAbs ≠ legendreSym r (pp n : ℤ)) : NFrSet n r σr = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro y hy
  exact H5_core n r (H5_four_dvd hn ha) hr σr hsign y hy

theorem prop_6_6_i_proved (n a r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a) (ha : 3 ≤ a)
    (hr : ¬ r ∣ pp n) (hr1 : r % 2 ^ a = 2 ^ a - 1) (σr : ℤ)
    (hsign : (-1 : ℤ) ^ σr.natAbs ≠ legendreSym r (pp n : ℤ)) : NFrSet n r σr = ∅ := by
  have hp : r.Prime := Fact.out
  have hN : 8 ≤ 2 ^ a :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hrn : ¬ r ∣ pp n * n := by
    intro hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
    · exact hr h
    · rw [hn] at h
      have h2 : r = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
      subst h2
      rw [Nat.mod_eq_of_lt (by omega)] at hr1
      omega
  rw [Set.eq_empty_iff_forall_notMem]
  intro y hy
  exact H5_core n r (H5_four_dvd (nodd := 1) (by rw [hn, mul_one]) ha) hrn σr hsign y hy

/-! ## Row 25a — Corollary 6.5, sign part -/

theorem cor_6_5_sign_proved (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a)
    (_hodd : Odd nodd) (_hp : (pp n).Prime) (_hr : ¬ r ∣ pp n * n) (σr : ℤ)
    (hXia35 : (-1 : ℤ) ^ σr.natAbs = legendreSym r ((-1) ^ (n / 2) * (pp n : ℤ))) :
    (-1 : ℤ) ^ σr.natAbs = legendreSym r (pp n : ℤ) := by
  have hn4 : 4 ∣ n := H5_four_dvd hn ha
  have he : Even (n / 2) := ⟨n / 4, by omega⟩
  rw [he.neg_one_pow, one_mul] at hXia35
  exact hXia35

/-! ## Coverage — s6_primes.tex:44-49 -/

theorem sec_6_1_R_kappa_proved (n : ℕ) [NeZero n] (hn : Even n) {K : Type*} [CommRing K] (y : ZMod n → K) :
    (L3 ((n : K) * (1 - (pp n : K))) y → ∀ s, s ≠ half n → R y s = (n : K) * (1 - (pp n : K))) ∧
      (L2 ((n : K) ^ 3) y → R y (half n) = (n : K) ^ 4) ∧
      ∀ e : ℕ, n = 2 ^ e → 3 ≤ e → Odd e →
        kappa n (ZMod 5) = -(pp n : ZMod 5) ∧ ¬ IsSquare (kappa n (ZMod 5)) ∧ kappa n (ZMod 5) ^ 2 = -1 := by
  refine ⟨fun h => H5_R_of_L3 hn _ y h, fun h => by rw [H5_R_half_of_L2 hn _ y h]; ring, ?_⟩
  intro e hne _ heo
  obtain ⟨k, rfl⟩ := heo
  have hx : ((n : ℕ) : ZMod 5) = 2 * (-1) ^ k := by
    rw [hne]
    push_cast
    rw [pow_succ, pow_mul, show (2 : ZMod 5) ^ 2 = -1 by decide, mul_comm]
  have hpp : ((pp n : ℕ) : ZMod 5) = (n : ZMod 5) ^ 2 + n + 1 := by
    unfold pp
    push_cast
    ring
  have hns2 : ∀ x : ZMod 5, (2 : ZMod 5) ≠ x * x := by decide
  have hns3 : ∀ x : ZMod 5, (3 : ZMod 5) ≠ x * x := by decide
  unfold kappa
  rw [hpp]
  rcases neg_one_pow_eq_or (ZMod 5) k with h | h <;> rw [h] at hx <;> rw [hx]
  · refine ⟨by decide, ?_, by decide⟩
    rintro ⟨x, hx'⟩
    exact hns3 x (by rw [← hx']; decide)
  · refine ⟨by decide, ?_, by decide⟩
    rintro ⟨x, hx'⟩
    exact hns2 x (by rw [← hx']; decide)

/-! ## Row 14c — Section 4.1, homogeneous laws (given Prop 2.4's bijection) -/

section Homog

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

/-- The homogeneous laws (h1), (h3), (h4) (the `H` of `sec_4_1_homog`). -/
def H5_H (lam : ZMod n → L) : Prop :=
  (∀ k, lam (3 * k) = lam k ^ 3) ∧ (∀ k, lam k * lam (-k) = 1) ∧
    (∀ k, lam k * lam (k + half n) = lam (half n) * lam (2 * k))

theorem H5_F3_ne {ω : L} (hω0 : ω ≠ 0) (h : ZMod n → L) (hF3 : F3 ω h) (k : ZMod n) : h k ≠ 0 := by
  intro hk
  have e := hF3 k
  rw [hk, zero_mul] at e
  exact pow_ne_zero _ (pow_ne_zero _ hω0) e.symm

theorem H5_H_ne (lam : ZMod n → L) (hl : H5_H lam) (k : ZMod n) : lam k ≠ 0 := by
  intro hk
  have e := hl.2.1 k
  rw [hk, zero_mul] at e
  exact zero_ne_one e

theorem H5_part1 {ω : L} (hω0 : ω ≠ 0) (h h' : ZMod n → L) (hh : F1 3 2 ω h ∧ F3 ω h ∧ F4 h)
    (hh' : F1 3 2 ω h' ∧ F3 ω h' ∧ F4 h') : H5_H (fun k => h' k / h k) := by
  obtain ⟨hF1, hF3, hF4⟩ := hh
  obtain ⟨hF1', hF3', hF4'⟩ := hh'
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_⟩
  · have e1 := hF1 k
    have e1' := hF1' k
    simp only [Nat.cast_ofNat] at e1 e1'
    show h' (3 * k) / h (3 * k) = (h' k / h k) ^ 3
    rw [e1, e1', mul_div_mul_left _ _ (zpow_ne_zero _ (pow_ne_zero _ hω0)), div_pow]
  · show h' k / h k * (h' (-k) / h (-k)) = 1
    rw [div_mul_div_comm, hF3 k, hF3' k]
    exact div_self (pow_ne_zero _ (pow_ne_zero _ hω0))
  · show h' k / h k * (h' (k + half n) / h (k + half n)) = h' (half n) / h (half n) * (h' (2 * k) / h (2 * k))
    rw [div_mul_div_comm, div_mul_div_comm, hF4 k, hF4' k]

theorem H5_part2 {ω : L} (h lam : ZMod n → L) (hh : F1 3 2 ω h ∧ F3 ω h ∧ F4 h) (hl : H5_H lam) :
    F1 3 2 ω (fun k => lam k * h k) ∧ F3 ω (fun k => lam k * h k) ∧ F4 (fun k => lam k * h k) := by
  obtain ⟨hF1, hF3, hF4⟩ := hh
  obtain ⟨hl1, hl3, hl4⟩ := hl
  refine ⟨?_, ?_, ?_⟩
  · intro k
    have e1 := hF1 k
    simp only [Nat.cast_ofNat] at e1 ⊢
    rw [e1, hl1 k]
    ring
  · intro k
    show lam k * h k * (lam (-k) * h (-k)) = _
    calc lam k * h k * (lam (-k) * h (-k)) = (lam k * lam (-k)) * (h k * h (-k)) := by ring
      _ = _ := by rw [hl3 k, hF3 k, one_mul]
  · intro k
    show lam k * h k * (lam (k + half n) * h (k + half n)) = lam (half n) * h (half n) * (lam (2 * k) * h (2 * k))
    calc lam k * h k * (lam (k + half n) * h (k + half n))
        = (lam k * lam (k + half n)) * (h k * h (k + half n)) := by ring
      _ = _ := by rw [hl4 k, hF4 k]; ring

theorem H5_part4 (lam : ZMod n → L) (hl : H5_H lam) (k : ZMod n) :
    lam k ^ (3 ^ orderOf (3 : ZMod n) - 1) = 1 := by
  have hiter : ∀ j : ℕ, lam ((3 : ZMod n) ^ j * k) = lam k ^ (3 ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', mul_assoc, hl.1, ih, ← pow_mul, ← pow_succ]
  have h1 := hiter (orderOf (3 : ZMod n))
  rw [pow_orderOf_eq_one, one_mul] at h1
  have hne := H5_H_ne lam hl k
  have hpos : 1 ≤ 3 ^ orderOf (3 : ZMod n) := Nat.one_le_pow _ _ (by norm_num)
  calc lam k ^ (3 ^ orderOf (3 : ZMod n) - 1)
      = lam k ^ (3 ^ orderOf (3 : ZMod n) - 1) * lam k / lam k := by rw [mul_div_cancel_right₀ _ hne]
    _ = lam k ^ (3 ^ orderOf (3 : ZMod n)) / lam k := by rw [← pow_succ, Nat.sub_add_cancel hpos]
    _ = 1 := by rw [← h1, div_self hne]

theorem H5_orderOf_pos (h3 : ¬ 3 ∣ n) : 0 < orderOf (3 : ZMod n) := by
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have hu : ((ZMod.unitOfCoprime 3 hcop : (ZMod n)ˣ) : ZMod n) = 3 := by
    rw [ZMod.coe_unitOfCoprime, Nat.cast_ofNat]
  rw [← hu, orderOf_units]
  exact orderOf_pos _

theorem H5_part5 (h3 : ¬ 3 ∣ n) : {lam : ZMod n → L | H5_H lam}.Finite := by
  have hM : 0 < 3 ^ orderOf (3 : ZMod n) - 1 := by
    have h1 := H5_orderOf_pos (n := n) h3
    have h2 : 3 ≤ 3 ^ orderOf (3 : ZMod n) := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ orderOf (3 : ZMod n) := Nat.pow_le_pow_right (by norm_num) h1
    omega
  have hfin : {x : L | x ^ (3 ^ orderOf (3 : ZMod n) - 1) = 1}.Finite := by
    apply (Polynomial.nthRootsFinset (3 ^ orderOf (3 : ZMod n) - 1) (1 : L)).finite_toSet.subset
    intro x hx
    rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset hM]
    exact hx
  apply (Set.Finite.pi (t := fun _ : ZMod n => {x : L | x ^ (3 ^ orderOf (3 : ZMod n) - 1) = 1})
    (fun _ => hfin)).subset
  intro lam hl k _
  exact H5_part4 lam hl k

theorem H5_part3 [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω0 : ω ≠ 0)
    (hP24 : Set.BijOn (dftA ω) (NFSet n 2) {h | F1 3 2 ω h ∧ F3 ω h ∧ F4 h}) (hne : (NFSet n 2).Nonempty) :
    Nat.card (NFSet n 2) = Nat.card {lam : ZMod n → L // H5_H lam} := by
  obtain ⟨y0, hy0⟩ := hne
  have hh0 : F1 3 2 ω (dftA ω y0) ∧ F3 ω (dftA ω y0) ∧ F4 (dftA ω y0) := hP24.mapsTo hy0
  have hne0 := H5_F3_ne hω0 _ hh0.2.1
  rw [Nat.card_congr (hP24.equiv _)]
  apply Nat.card_congr
  exact
    { toFun := fun h => ⟨fun k => h.1 k / dftA ω y0 k, H5_part1 hω0 _ _ hh0 h.2⟩
      invFun := fun lam => ⟨fun k => lam.1 k * dftA ω y0 k, H5_part2 _ _ hh0 lam.2⟩
      left_inv := fun h => Subtype.ext (funext fun k => div_mul_cancel₀ _ (hne0 k))
      right_inv := fun lam => Subtype.ext (funext fun k => mul_div_cancel_right₀ _ (hne0 k)) }

end Homog

theorem sec_4_1_homog_of_proved (n : ℕ) [NeZero n] (_hn : Even n) (h3 : ¬ 3 ∣ n) {L : Type*} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (hP24 : Set.BijOn (dftA ω) (NFSet n 2) {h | F1 3 2 ω h ∧ F3 ω h ∧ F4 h}) :
    let H : (ZMod n → L) → Prop := fun lam => (∀ k, lam (3 * k) = lam k ^ 3) ∧ (∀ k, lam k * lam (-k) = 1) ∧
      (∀ k, lam k * lam (k + half n) = lam (half n) * lam (2 * k))
    (∀ h h' : ZMod n → L, (F1 3 2 ω h ∧ F3 ω h ∧ F4 h) → (F1 3 2 ω h' ∧ F3 ω h' ∧ F4 h') →
      H (fun k => h' k / h k)) ∧
    (∀ h lam : ZMod n → L, (F1 3 2 ω h ∧ F3 ω h ∧ F4 h) → H lam →
      F1 3 2 ω (fun k => lam k * h k) ∧ F3 ω (fun k => lam k * h k) ∧ F4 (fun k => lam k * h k)) ∧
    ((NFSet n 2).Nonempty → Nat.card (NFSet n 2) = Nat.card {lam : ZMod n → L // H lam}) ∧
    (∀ lam : ZMod n → L, H lam → ∀ k, lam k ^ (3 ^ orderOf (3 : ZMod n) - 1) = 1) ∧
    {lam : ZMod n → L | H lam}.Finite := by
  intro H
  have hω0 : ω ≠ 0 := hω.ne_zero (NeZero.ne n)
  exact ⟨fun h h' hh hh' => H5_part1 hω0 h h' hh hh', fun h lam hh hl => H5_part2 h lam hh hl,
    fun hne => H5_part3 ω hω0 hP24 hne, fun lam hl k => H5_part4 lam hl k, H5_part5 h3⟩

end Xia.Proofs

#print axioms Xia.Proofs.prop_4_3_odd_proved
#print axioms Xia.Proofs.thm_6_4_i_proved
#print axioms Xia.Proofs.prop_6_6_i_proved
#print axioms Xia.Proofs.cor_6_5_sign_proved
#print axioms Xia.Proofs.sec_6_1_R_kappa_proved
#print axioms Xia.Proofs.sec_4_1_homog_of_proved
