/- Xia/Proofs/Decoupling34.lean — proofs of the rows thm_3_4_a, thm_3_4_d, intro_conic_not_product of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry

namespace Xia.Proofs

open Xia Finset

/-! ## 1. Powers of 3 modulo powers of 2 (as in Pow2Arith.lean) -/

theorem H8_three_pow (k : ℕ) : ∃ m : ℕ, 3 ^ (2 ^ (k + 1)) = 1 + 2 ^ (k + 3) * (2 * m + 1) := by
  induction k with
  | zero => exact ⟨0, by norm_num⟩
  | succ k ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨m + 2 ^ (k + 1) * (2 * m + 1) ^ 2, ?_⟩
    rw [pow_succ 2 (k + 1), pow_mul, hm]
    ring

theorem H8_mod (k m : ℕ) : (1 + 2 ^ (k + 3) * (2 * m + 1)) % 2 ^ (k + 4) = 1 + 2 ^ (k + 3) := by
  have h : 1 + 2 ^ (k + 3) * (2 * m + 1) = (1 + 2 ^ (k + 3)) + 2 ^ (k + 4) * m := by ring
  rw [h, Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  have h3 : 2 ^ (k + 4) = 2 * 2 ^ (k + 3) := by ring
  have h4 : 0 < 2 ^ (k + 3) := pow_pos two_pos _
  have h5 : 2 ^ (k + 3) = 8 * 2 ^ k := by ring
  have h6 : 0 < 2 ^ k := pow_pos two_pos _
  omega

theorem H8_divs (k n : ℕ) (hn : n = 2 ^ (k + 3)) : n / 2 = 2 ^ (k + 2) ∧ n / 4 = 2 ^ (k + 1) ∧
    n / 8 = 2 ^ k := by
  subst hn
  refine ⟨?_, ?_, ?_⟩
  · rw [show 2 ^ (k + 3) = 2 ^ (k + 2) * 2 by ring, Nat.mul_div_cancel _ (by norm_num)]
  · rw [show 2 ^ (k + 3) = 2 ^ (k + 1) * 4 by ring, Nat.mul_div_cancel _ (by norm_num)]
  · rw [show 2 ^ (k + 3) = 2 ^ k * 8 by ring, Nat.mul_div_cancel _ (by norm_num)]

theorem H8_pow_one_add {M : Type*} [Monoid M] (x : M) (d a : ℕ) (hx : x ^ d = 1) (ha : d ∣ a) :
    x ^ (1 + a) = x := by
  obtain ⟨c, rfl⟩ := ha
  rw [pow_add, pow_one, pow_mul, hx, one_pow, mul_one]

theorem H8_pow_pred {M : Type*} [Monoid M] (x : M) (a : ℕ) (ha : 1 ≤ a) : x ^ a = x ^ (a - 1) * x := by
  rw [← pow_succ, Nat.sub_add_cancel ha]

/-- For `n = 2^(k+3)`: `Q = 3^(n/4) = 1 + n·(2m+1)`. -/
theorem H8_QQ (k n : ℕ) (hn : n = 2 ^ (k + 3)) : ∃ m : ℕ, QQ n = 1 + n * (2 * m + 1) := by
  obtain ⟨m, hm⟩ := H8_three_pow k
  refine ⟨m, ?_⟩
  rw [QQ, (H8_divs k n hn).2.1, hm, hn]

theorem H8_root_fixed {M : Type*} [Monoid M] (k n : ℕ) (hn : n = 2 ^ (k + 3)) (ξ : M) (hξ : ξ ^ n = 1) :
    ξ ^ QQ n = ξ := by
  obtain ⟨m, hm⟩ := H8_QQ k n hn
  rw [hm]
  exact H8_pow_one_add ξ n _ hξ (Dvd.intro _ rfl)

section ZModPow2

variable (k : ℕ)

theorem H8_three_pow_eq_one : (3 : ZMod (2 ^ (k + 3))) ^ (2 ^ (k + 1)) = 1 := by
  obtain ⟨m, hm⟩ := H8_three_pow k
  have h : (3 : ZMod (2 ^ (k + 3))) ^ (2 ^ (k + 1)) = ((3 ^ (2 ^ (k + 1)) : ℕ) : ZMod (2 ^ (k + 3))) := by
    simp
  rw [h, hm, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero, Nat.cast_one]

theorem H8_three_pow_ne_one : (3 : ZMod (2 ^ (k + 3))) ^ (2 ^ k) ≠ 1 := by
  have h : (3 : ZMod (2 ^ (k + 3))) ^ (2 ^ k) = ((3 ^ (2 ^ k) : ℕ) : ZMod (2 ^ (k + 3))) := by simp
  have h1 : (1 : ZMod (2 ^ (k + 3))) = ((1 : ℕ) : ZMod (2 ^ (k + 3))) := Nat.cast_one.symm
  rw [h, h1, Ne, ZMod.natCast_eq_natCast_iff']
  cases k with
  | zero => norm_num
  | succ k =>
    obtain ⟨m, hm⟩ := H8_three_pow k
    rw [hm, show k + 1 + 3 = k + 4 from rfl, H8_mod]
    have h16 : 2 ^ (k + 4) = 16 * 2 ^ k := by ring
    have h8 : 2 ^ (k + 3) = 8 * 2 ^ k := by ring
    have h0 : 0 < 2 ^ k := pow_pos two_pos _
    rw [Nat.mod_eq_of_lt (by omega : 1 < 2 ^ (k + 4))]
    omega

theorem H8_orderOf_three : orderOf (3 : ZMod (2 ^ (k + 3))) = 2 ^ (k + 1) :=
  orderOf_eq_prime_pow (H8_three_pow_ne_one k) (H8_three_pow_eq_one k)

theorem H8_neg_one_ne_pow (j : ℕ) : (-1 : ZMod (2 ^ (k + 3))) ≠ 3 ^ j := by
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

end ZModPow2

/-- `ord_n(3) = n/4` and `-1 ∉ ⟨3⟩` in `ℤ/n`, `n = 2^e`, `e ≥ 3`. -/
theorem H8_ord (n e : ℕ) (hne : n = 2 ^ e) (he : 3 ≤ e) :
    orderOf (3 : ZMod n) = n / 4 ∧ ∀ j : ℕ, (-1 : ZMod n) ≠ 3 ^ j := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 3 := ⟨e - 3, by omega⟩
  subst hne
  exact ⟨by rw [H8_orderOf_three, (H8_divs k _ rfl).2.1], H8_neg_one_ne_pow k⟩

/-- A finite field contains a primitive `d`-th root of unity for every `d ∣ |K| - 1`. -/
theorem H8_exists_prim {K : Type*} [Field K] [Finite K] (d : ℕ) (hd : d ∣ Nat.card K - 1) (hd0 : d ≠ 0) :
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

/-! ## 2. Characteristic 3 -/

section Char3

variable {F : Type*} [Field F] [CharP F 3]

theorem H8_three_eq_zero : (3 : F) = 0 := by
  have h := CharP.cast_eq_zero F 3
  exact_mod_cast h

theorem H8_two_eq_neg_one : (2 : F) = -1 := by
  linear_combination (H8_three_eq_zero (F := F))

theorem H8_two_ne_zero : (2 : F) ≠ 0 := by
  rw [H8_two_eq_neg_one]; exact neg_ne_zero.mpr one_ne_zero

/-- `-(a + a) = a` in characteristic 3. -/
theorem H8_neg_add_self (a : F) : -(a + a) = a := by
  linear_combination (-a) * (H8_three_eq_zero (F := F))

theorem H8_eq_zero_of_eq_neg (a : F) (h : a = -a) : a = 0 := by
  have h2 : a + a = 0 := by linear_combination h
  calc a = -(a + a) := (H8_neg_add_self a).symm
    _ = 0 := by rw [h2, neg_zero]

theorem H8_natCast_pow_three (c : ℕ) : (c : F) ^ 3 = c := by
  have h := map_natCast (frobenius F 3) c
  rwa [frobenius_def] at h

end Char3

/-! ## 3. The set-up of Section 3.2 (`n = 2^e`, `e ≥ 4`) -/

section Setup

variable {F : Type*} [Field F] [CharP F 3]

theorem H8_setup (n e : ℕ) (hne : n = 2 ^ e) (he : 4 ≤ e) (ξ0 : F) (hξ0 : IsPrimitiveRoot ξ0 n) :
    QQ n = qq n ^ 2 ∧ Odd (qq n) ∧ Odd (QQ n) ∧ iota n ξ0 ^ 2 = -1 ∧ iota n ξ0 ^ qq n = iota n ξ0 ∧
      ξ0 ^ qq n = -ξ0 ∧ ξ0 ^ QQ n = ξ0 ∧ ξ0 ^ (n / 2) = -1 ∧ ξ0 ≠ 0 ∧ 2 * (n / 8) = n / 4 ∧
      2 * (n / 4) = n / 2 ∧ n / 4 = n / 8 + n / 8 ∧ 9 ≤ qq n ∧ (n : F) ≠ 0 ∧ 0 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 4 := ⟨e - 4, by omega⟩
  have hdivs := H8_divs (k + 1) n hne
  have hn2 : n / 2 = 2 ^ (k + 3) := hdivs.1
  have hn4 : n / 4 = 2 ^ (k + 2) := hdivs.2.1
  have hn8 : n / 8 = 2 ^ (k + 1) := hdivs.2.2
  have hnpos : 0 < n := by rw [hne]; positivity
  obtain ⟨m, hm⟩ := H8_three_pow k
  have hq : qq n = 1 + 2 ^ (k + 3) * (2 * m + 1) := by rw [qq, hn8, hm]
  have hQq : QQ n = qq n ^ 2 := by
    rw [QQ, qq, hn4, hn8, ← pow_mul]; congr 1
  have hιprim : IsPrimitiveRoot (iota n ξ0) 4 := hξ0.pow hnpos (by rw [hn4, hne]; ring)
  have hι4 : iota n ξ0 ^ 4 = 1 := hιprim.pow_eq_one
  have hhalf : ξ0 ^ (n / 2) = -1 :=
    (hξ0.pow hnpos (show n = n / 2 * 2 by rw [hn2, hne]; ring)).eq_neg_one_of_two_right
  have h8 : 8 ≤ 2 ^ (k + 3) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h8' : 2 ^ (k + 3) ≤ 2 ^ (k + 3) * (2 * m + 1) := Nat.le_mul_of_pos_right _ (by omega)
  refine ⟨hQq, Odd.pow (by decide), Odd.pow (by decide), ?_, ?_, ?_,
    H8_root_fixed (k + 1) n hne ξ0 hξ0.pow_eq_one, hhalf, hξ0.ne_zero hnpos.ne', by rw [hn8, hn4]; ring,
    by rw [hn4, hn2]; ring, by rw [hn4, hn8]; ring, by omega, ?_, hnpos⟩
  · exact (hιprim.pow (by norm_num) (show 4 = 2 * 2 by norm_num)).eq_neg_one_of_two_right
  · rw [hq]
    exact H8_pow_one_add _ 4 _ hι4 ⟨2 ^ (k + 1) * (2 * m + 1), by ring⟩
  · rw [hq, show 1 + 2 ^ (k + 3) * (2 * m + 1) = 1 + n / 2 + n * m by rw [hn2, hne]; ring,
      pow_add, pow_add, pow_one, hhalf, pow_mul, hξ0.pow_eq_one, one_pow]
    ring
  · rw [hne]; push_cast; exact pow_ne_zero _ H8_two_ne_zero

end Setup

/-! ## 4. `V`, `T`, `V_±` -/

section VT

variable {F : Type*} [Field F] [CharP F 3] (n : ℕ)

theorem H8_V_add (x y : F) (hx : x ∈ Vsp n) (hy : y ∈ Vsp n) : x + y ∈ Vsp n := by
  simp only [Vsp, Set.mem_ofPred_eq, QQ] at hx hy ⊢
  rw [add_pow_char_pow, hx, hy, neg_add]

omit [CharP F 3] in
theorem H8_V_neg (hQodd : Odd (QQ n)) (x : F) (hx : x ∈ Vsp n) : -x ∈ Vsp n := by
  simp only [Vsp, Set.mem_ofPred_eq] at hx ⊢
  rw [hQodd.neg_pow, hx]

theorem H8_V_sub (hQodd : Odd (QQ n)) (x y : F) (hx : x ∈ Vsp n) (hy : y ∈ Vsp n) : x - y ∈ Vsp n := by
  rw [sub_eq_add_neg]; exact H8_V_add n x (-y) hx (H8_V_neg n hQodd y hy)

theorem H8_T_add (ξ0 x y : F) : Tmap n ξ0 (x + y) = Tmap n ξ0 x + Tmap n ξ0 y := by
  simp only [Tmap, qq]
  rw [add_pow_char_pow]; ring

omit [CharP F 3] in
theorem H8_T_neg (hqodd : Odd (qq n)) (ξ0 x : F) : Tmap n ξ0 (-x) = -Tmap n ξ0 x := by
  simp only [Tmap]
  rw [hqodd.neg_pow]; ring

theorem H8_T_sub (hqodd : Odd (qq n)) (ξ0 x y : F) : Tmap n ξ0 (x - y) = Tmap n ξ0 x - Tmap n ξ0 y := by
  rw [sub_eq_add_neg, H8_T_add, H8_T_neg n hqodd, ← sub_eq_add_neg]

omit [CharP F 3] in
theorem H8_T_mem (hQ : QQ n = qq n ^ 2) (hqodd : Odd (qq n)) (ξ0 : F) (hιq : iota n ξ0 ^ qq n = iota n ξ0)
    (x : F) (hx : x ∈ Vsp n) : Tmap n ξ0 x ∈ Vsp n := by
  simp only [Vsp, Set.mem_ofPred_eq, Tmap] at hx ⊢
  have hιQ : iota n ξ0 ^ QQ n = iota n ξ0 := by rw [hQ, pow_two, pow_mul, hιq, hιq]
  rw [mul_pow, hιQ, ← pow_mul, mul_comm (qq n) (QQ n), pow_mul, hx, hqodd.neg_pow]
  ring

omit [CharP F 3] in
theorem H8_TT (hQ : QQ n = qq n ^ 2) (ξ0 : F) (hι2 : iota n ξ0 ^ 2 = -1) (hιq : iota n ξ0 ^ qq n = iota n ξ0)
    (x : F) (hx : x ∈ Vsp n) : Tmap n ξ0 (Tmap n ξ0 x) = x := by
  simp only [Vsp, Set.mem_ofPred_eq] at hx
  simp only [Tmap]
  rw [mul_pow, hιq, ← pow_mul, ← pow_two, ← hQ, hx]
  linear_combination (-x) * hι2

/-- For `x ∈ V`: `-(x + Tx) ∈ V_+` and `-(x - Tx) ∈ V_-` (these are `(x ± Tx)/2`, as `1/2 = -1`). -/
theorem H8_dec_mem (hQ : QQ n = qq n ^ 2) (hqodd : Odd (qq n)) (hQodd : Odd (QQ n)) (ξ0 : F)
    (hι2 : iota n ξ0 ^ 2 = -1) (hιq : iota n ξ0 ^ qq n = iota n ξ0) (x : F) (hx : x ∈ Vsp n) :
    -(x + Tmap n ξ0 x) ∈ Vplus n ξ0 ∧ -(x - Tmap n ξ0 x) ∈ Vminus n ξ0 := by
  have hT := H8_T_mem n hQ hqodd ξ0 hιq x hx
  have hTT := H8_TT n hQ ξ0 hι2 hιq x hx
  refine ⟨⟨H8_V_neg n hQodd _ (H8_V_add n _ _ hx hT), ?_⟩, ⟨H8_V_neg n hQodd _ (H8_V_sub n hQodd _ _ hx hT), ?_⟩⟩
  · rw [H8_T_neg n hqodd, H8_T_add, hTT, add_comm]
  · rw [H8_T_neg n hqodd, H8_T_sub n hqodd, hTT]; ring

theorem H8_dec_sum (ξ0 x : F) : -(x + Tmap n ξ0 x) + -(x - Tmap n ξ0 x) = x := by
  linear_combination (-x) * (H8_three_eq_zero (F := F))

/-- Unique decomposition `V = V_+ ⊕ V_-`. -/
theorem H8_dec (hQ : QQ n = qq n ^ 2) (hqodd : Odd (qq n)) (hQodd : Odd (QQ n)) (ξ0 : F)
    (hι2 : iota n ξ0 ^ 2 = -1) (hιq : iota n ξ0 ^ qq n = iota n ξ0) (x : F) (hx : x ∈ Vsp n) :
    ∃! pm : F × F, pm.1 ∈ Vplus n ξ0 ∧ pm.2 ∈ Vminus n ξ0 ∧ x = pm.1 + pm.2 := by
  obtain ⟨hp, hm⟩ := H8_dec_mem n hQ hqodd hQodd ξ0 hι2 hιq x hx
  refine ⟨(-(x + Tmap n ξ0 x), -(x - Tmap n ξ0 x)), ⟨hp, hm, (H8_dec_sum n ξ0 x).symm⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨ha, hb, hab⟩
  simp only at ha hb hab
  have hTx : Tmap n ξ0 x = a - b := by rw [hab, H8_T_add, ha.2, hb.2, sub_eq_add_neg]
  rw [hTx, hab]
  ext
  · simp only
    linear_combination a * (H8_three_eq_zero (F := F))
  · simp only
    linear_combination b * (H8_three_eq_zero (F := F))

omit [CharP F 3] in
theorem H8_smul_mem (hQ : QQ n = qq n ^ 2) (ξ0 c : F) (hc : c ^ qq n = c) (s : F) (x : F) (hx : x ∈ Vsp n ∧ Tmap n ξ0 x = s * x) :
    c * x ∈ Vsp n ∧ Tmap n ξ0 (c * x) = s * (c * x) := by
  have hcQ : c ^ QQ n = c := by rw [hQ, pow_two, pow_mul, hc, hc]
  obtain ⟨hxV, hxT⟩ := hx
  simp only [Vsp, Set.mem_ofPred_eq] at hxV ⊢
  refine ⟨by rw [mul_pow, hcQ, hxV]; ring, ?_⟩
  simp only [Tmap] at hxT ⊢
  rw [mul_pow, hc]
  linear_combination c * hxT

end VT

/-! ## 5. Counting -/

section Count

variable {F : Type*} [Field F]

/-- A set of roots of `c X^N - X` (`c ≠ 0`, `N ≥ 2`) has at most `N` elements. -/
theorem H8_card_roots_le [Finite F] (c : F) (hc : c ≠ 0) (N : ℕ) (hN : 2 ≤ N) (s : Set F)
    (hs : ∀ x ∈ s, c * x ^ N = x) : Nat.card s ≤ N := by
  classical
  have hfin : s.Finite := Set.toFinite s
  set P : Polynomial F := Polynomial.C c * Polynomial.X ^ N - Polynomial.X with hPdef
  have hlt : (Polynomial.X : Polynomial F).natDegree < (Polynomial.C c * Polynomial.X ^ N).natDegree := by
    rw [Polynomial.natDegree_X, Polynomial.natDegree_C_mul_X_pow N c hc]; omega
  have hdeg : P.natDegree = N := by
    rw [hPdef, Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_C_mul_X_pow N c hc]
  have hP0 : P ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at hdeg; omega
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card s hfin, ← hdeg]
  apply Polynomial.card_le_degree_of_subset_roots
  intro a ha
  rw [Finset.mem_val, Set.Finite.mem_toFinset] at ha
  rw [Polynomial.mem_roots hP0, Polynomial.IsRoot.def, hPdef]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  rw [hs a ha, sub_self]

theorem H8_arith (a b q : ℕ) (ha : a ≤ q) (hb : b ≤ q) (h : a * b = q ^ 2) (hq : 0 < q) : a = q ∧ b = q := by
  have h1 : a = q := by
    by_contra hne
    have hlt : a < q := lt_of_le_of_ne ha hne
    have h2 : a * b ≤ a * q := Nat.mul_le_mul_left a hb
    have h3 : a * q < q * q := Nat.mul_lt_mul_of_pos_right hlt hq
    rw [pow_two] at h
    omega
  subst h1
  refine ⟨rfl, ?_⟩
  rw [pow_two] at h
  exact Nat.eq_of_mul_eq_mul_left hq h

end Count

section GF

/-- `2(Q-1) ∣ |F| - 1` for `F = F_{3^{n/2}}`, `n = 2^e`, `e ≥ 3`, so `F` has a primitive `2(Q-1)`-th root. -/
theorem H8_prim2Q (n e : ℕ) (hne : n = 2 ^ e) (he : 3 ≤ e) :
    ∃ ζ : GaloisField 3 (n / 2), IsPrimitiveRoot ζ (2 * (QQ n - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 3 := ⟨e - 3, by omega⟩
  obtain ⟨hn2, hn4, -⟩ := H8_divs k n hne
  obtain ⟨m, hm⟩ := H8_QQ k n hne
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
  have hdvd2 : 2 * (QQ n - 1) ∣ Nat.card (GaloisField 3 (n / 2)) - 1 := by
    rw [GaloisField.card 3 (n / 2) (by rw [hn2]; positivity)]; exact hdvd
  exact H8_exists_prim (K := GaloisField 3 (n / 2)) (2 * (QQ n - 1)) hdvd2 (by omega)

/-- `|V| = Q` (as in `thm_3_1_theta_set_proved`). -/
theorem H8_card_V (n e : ℕ) (hne : n = 2 ^ e) (he : 3 ≤ e) :
    Nat.card (Vsp n : Set (GaloisField 3 (n / 2))) = QQ n := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 3 := ⟨e - 3, by omega⟩
  obtain ⟨m, hm⟩ := H8_QQ k n hne
  have hQ1 : QQ n - 1 = n * (2 * m + 1) := by rw [hm, Nat.add_sub_cancel_left]
  have hQpos : 0 < QQ n - 1 := by rw [hQ1, hne]; positivity
  have hQ1' : 1 ≤ QQ n := by omega
  obtain ⟨ζ, hζ⟩ := H8_prim2Q n (k + 3) hne (by omega)
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
  have hθcard : Nat.card {θ : GaloisField 3 (n / 2) // θ ^ (QQ n - 1) = -1} = QQ n - 1 := by
    rw [Nat.card_congr eqv, Nat.card_eq_finsetCard, hcardR]
  have hset : (Vsp n : Set (GaloisField 3 (n / 2))) = insert 0 {θ | θ ^ (QQ n - 1) = -1} := by
    ext θ
    simp only [Vsp, Set.mem_insert_iff, Set.mem_ofPred_eq]
    constructor
    · intro h
      by_cases h0 : θ = 0
      · exact Or.inl h0
      · right
        rw [H8_pow_pred θ _ hQ1'] at h
        have h' : θ ^ (QQ n - 1) * θ = (-1) * θ := by rw [h]; ring
        exact mul_right_cancel₀ h0 h'
    · rintro (rfl | h)
      · rw [zero_pow (by omega), neg_zero]
      · rw [H8_pow_pred θ _ hQ1', h]; ring
  have hnot : (0 : GaloisField 3 (n / 2)) ∉ {θ : GaloisField 3 (n / 2) | θ ^ (QQ n - 1) = -1} := by
    simp only [Set.mem_ofPred_eq]
    rw [zero_pow hQpos.ne']
    exact fun h => one_ne_zero (neg_eq_zero.mp h.symm)
  rw [hset, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem hnot, ← Nat.card_coe_set_eq]
  have : Nat.card ↥{θ : GaloisField 3 (n / 2) | θ ^ (QQ n - 1) = -1} =
      Nat.card {θ : GaloisField 3 (n / 2) // θ ^ (QQ n - 1) = -1} := rfl
  rw [this, hθcard]
  omega

end GF

/-! ## 6. Theorem 3.4(a) -/

/-- Row 11a — Theorem 3.4(a) (s3_pow2.tex:107-108): `T(x) = ι x^q` is an `F_3`-linear involution of `V`; hence
`V = V_+ ⊕ V_-`, and each of `V_+`, `V_-` is a line over `F_q` (closed under `F_q`-scalars, `q` elements). -/
theorem thm_3_4_a_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 4 ≤ e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) :
    (∀ x ∈ Vsp n, Tmap n ξ0 x ∈ Vsp n ∧ Tmap n ξ0 (Tmap n ξ0 x) = x) ∧
      (∀ x x' : GaloisField 3 (n / 2), Tmap n ξ0 (x + x') = Tmap n ξ0 x + Tmap n ξ0 x') ∧
      (∀ x ∈ Vsp n, ∃! pm : GaloisField 3 (n / 2) × GaloisField 3 (n / 2),
        pm.1 ∈ Vplus n ξ0 ∧ pm.2 ∈ Vminus n ξ0 ∧ x = pm.1 + pm.2) ∧
      (∀ c : GaloisField 3 (n / 2), c ^ qq n = c →
        (∀ x ∈ Vplus n ξ0, c * x ∈ Vplus n ξ0) ∧ ∀ x ∈ Vminus n ξ0, c * x ∈ Vminus n ξ0) ∧
      Nat.card (Vplus n ξ0) = qq n ∧ Nat.card (Vminus n ξ0) = qq n := by
  obtain ⟨hQ, hqodd, hQodd, hι2, hιq, -, -, -, -, -, -, -, hq9, -, -⟩ := H8_setup n e hne he ξ0 hξ0
  have hdec := H8_dec n hQ hqodd hQodd ξ0 hι2 hιq
  have hι0 : iota n ξ0 ≠ 0 := by
    intro h; rw [h] at hι2; norm_num at hι2
  -- the counts
  have hle_p : Nat.card (Vplus n ξ0) ≤ qq n :=
    H8_card_roots_le (iota n ξ0) hι0 (qq n) (by omega) _ (fun x hx => hx.2)
  have hle_m : Nat.card (Vminus n ξ0) ≤ qq n :=
    H8_card_roots_le (-iota n ξ0) (neg_ne_zero.mpr hι0) (qq n) (by omega) _
      (fun x hx => by have h := hx.2; simp only [Tmap] at h; rw [neg_mul, h, neg_neg])
  have hprod : Nat.card (Vplus n ξ0) * Nat.card (Vminus n ξ0) = Nat.card (Vsp n : Set (GaloisField 3 (n / 2))) := by
    rw [← Nat.card_prod]
    apply Nat.card_eq_of_bijective (fun pm : ↥(Vplus n ξ0) × ↥(Vminus n ξ0) =>
      (⟨pm.1.1 + pm.2.1, H8_V_add n _ _ pm.1.2.1 pm.2.2.1⟩ : ↥(Vsp n : Set (GaloisField 3 (n / 2)))))
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
      simp only [Subtype.mk.injEq] at h
      have hu := (hdec (a + b) (H8_V_add n _ _ ha.1 hb.1)).unique (y₁ := (a, b)) (y₂ := (a', b'))
        ⟨ha, hb, rfl⟩ ⟨ha', hb', h⟩
      simp only [Prod.mk.injEq] at hu
      obtain ⟨rfl, rfl⟩ := hu
      rfl
    · rintro ⟨x, hx⟩
      obtain ⟨pm, ⟨h1, h2, h3⟩, -⟩ := hdec x hx
      exact ⟨(⟨pm.1, h1⟩, ⟨pm.2, h2⟩), Subtype.ext h3.symm⟩
  rw [H8_card_V n e hne (by omega), hQ] at hprod
  obtain ⟨hcp, hcm⟩ := H8_arith _ _ _ hle_p hle_m hprod (by omega)
  refine ⟨fun x hx => ⟨H8_T_mem n hQ hqodd ξ0 hιq x hx, H8_TT n hQ ξ0 hι2 hιq x hx⟩, H8_T_add n ξ0, hdec,
    fun c hc => ⟨fun x hx => ?_, fun x hx => ?_⟩, hcp, hcm⟩
  · have h := H8_smul_mem n hQ ξ0 c hc 1 x ⟨hx.1, by rw [one_mul]; exact hx.2⟩
    exact ⟨h.1, by rw [h.2, one_mul]⟩
  · exact H8_smul_mem n hQ ξ0 c hc (-1) x ⟨hx.1, by rw [neg_one_mul]; exact hx.2⟩ |>.imp id
      (fun h => by rw [h, neg_one_mul])

/-! ## 7. Theorem 3.4(d): the top-layer inverse Fourier transform `y^-_t(x)` (s3_pow2.tex:187-198) -/

section Fourier

variable {F : Type*} [Field F] [CharP F 3]

/-- The `k`-th pair of terms of `n·y^-_t(x)`: the value `h_x(ξ_0^{3^k}) ξ^{-t}` on `O` and `h_x(ξ_0^{-3^k}) ξ^{t}` on
`O^{-1}`, with `h_x(ξ_0^{3^k}) = ξ_0^{2k3^k} x^{3^k}`, `h_x(ξ_0^{-3^k}) = -ξ_0^{-2k3^k} ν^{-3^k} x^{q3^k}`. -/
def H8_term (n : ℕ) (ξ0 ν x : F) (t k : ℕ) : F :=
  ξ0 ^ (2 * k * 3 ^ k) * x ^ (3 ^ k) * ((ξ0 ^ (3 ^ k)) ^ t)⁻¹ -
    (ξ0 ^ (2 * k * 3 ^ k))⁻¹ * (ν ^ (3 ^ k))⁻¹ * (x ^ qq n) ^ (3 ^ k) * (ξ0 ^ (3 ^ k)) ^ t

/-- `y^-_t(x) := n^{-1} ∑_{ξ ∈ O ∪ O^{-1}} h_x(ξ) ξ^{-t}` (the orbit `O` is `{ξ_0^{3^k} : k < n/4}`). -/
def H8_Y (n : ℕ) (ξ0 ν x : F) (t : ℕ) : F := (n : F)⁻¹ * ∑ k ∈ range (n / 4), H8_term n ξ0 ν x t k

/-- (F1) along the orbits, term by term: `term_{t+2}(k+1) = term_t(k)^3`. -/
theorem H8_term_succ (n : ℕ) (ξ0 ν x : F) (hξ : ξ0 ≠ 0) (hν : ν ≠ 0) (t k : ℕ) :
    H8_term n ξ0 ν x (t + 2) (k + 1) = H8_term n ξ0 ν x t k ^ 3 := by
  unfold H8_term
  have e1 : ξ0 ^ (2 * (k + 1) * 3 ^ (k + 1)) = (ξ0 ^ (2 * k * 3 ^ k)) ^ 3 * ((ξ0 ^ (3 ^ k)) ^ 3) ^ 2 := by
    rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
  have e2 : ∀ z : F, z ^ (3 ^ (k + 1)) = (z ^ (3 ^ k)) ^ 3 := fun z => by rw [← pow_mul, pow_succ]
  rw [e1, e2 ξ0, e2 x, e2 (x ^ qq n), e2 ν]
  have hA : ξ0 ^ (2 * k * 3 ^ k) ≠ 0 := pow_ne_zero _ hξ
  have hB : ξ0 ^ (3 ^ k) ≠ 0 := pow_ne_zero _ hξ
  have hN : ν ^ (3 ^ k) ≠ 0 := pow_ne_zero _ hν
  generalize ξ0 ^ (2 * k * 3 ^ k) = A at hA ⊢
  generalize ξ0 ^ (3 ^ k) = B at hB ⊢
  generalize ν ^ (3 ^ k) = N at hN ⊢
  generalize x ^ (3 ^ k) = X
  generalize (x ^ qq n) ^ (3 ^ k) = W
  rw [sub_pow_char]
  congr 1
  · field_simp; ring
  · field_simp; ring

omit [CharP F 3] in
/-- The wrap of the orbit: `term_t(n/4) = term_t(0)` (uses `ξ_0^Q = ξ_0`, `x^Q = -x`, `ν^Q = ν`). -/
theorem H8_term_wrap (n : ℕ) (ξ0 ν x : F) (hnd : 2 * (n / 4) = n / 2) (hhalf : ξ0 ^ (n / 2) = -1)
    (hQodd : Odd (QQ n)) (hqodd : Odd (qq n)) (hξQ : ξ0 ^ QQ n = ξ0) (hx : x ^ QQ n = -x) (hνQ : ν ^ QQ n = ν)
    (t : ℕ) : H8_term n ξ0 ν x t (n / 4) = H8_term n ξ0 ν x t 0 := by
  unfold H8_term
  have hQ : 3 ^ (n / 4) = QQ n := rfl
  rw [hQ]
  have ea : ξ0 ^ (2 * (n / 4) * QQ n) = -1 := by rw [hnd, pow_mul, hhalf, hQodd.neg_one_pow]
  have ew : (x ^ qq n) ^ QQ n = -(x ^ qq n) := by
    rw [← pow_mul, mul_comm, pow_mul, hx, hqodd.neg_pow]
  rw [ea, hξQ, hx, ew, hνQ]
  simp only [mul_zero, zero_mul, pow_zero, pow_one, inv_one, one_mul, inv_neg]
  ring

theorem H8_Y_succ_succ (n : ℕ) (ξ0 ν x : F) (hξ : ξ0 ≠ 0) (hν : ν ≠ 0) (hnd : 2 * (n / 4) = n / 2)
    (hhalf : ξ0 ^ (n / 2) = -1) (hQodd : Odd (QQ n)) (hqodd : Odd (qq n)) (hξQ : ξ0 ^ QQ n = ξ0)
    (hx : x ^ QQ n = -x) (hνQ : ν ^ QQ n = ν) (t : ℕ) :
    H8_Y n ξ0 ν x (t + 2) = H8_Y n ξ0 ν x t ^ 3 := by
  unfold H8_Y
  have hshift : ∑ k ∈ range (n / 4), H8_term n ξ0 ν x (t + 2) k =
      ∑ k ∈ range (n / 4), H8_term n ξ0 ν x (t + 2) (k + 1) := by
    have h1 := Finset.sum_range_succ (fun k => H8_term n ξ0 ν x (t + 2) k) (n / 4)
    have h2 := Finset.sum_range_succ' (fun k => H8_term n ξ0 ν x (t + 2) k) (n / 4)
    rw [H8_term_wrap n ξ0 ν x hnd hhalf hQodd hqodd hξQ hx hνQ] at h1
    linear_combination h2 - h1
  rw [hshift, Finset.sum_congr rfl (fun k _ => H8_term_succ n ξ0 ν x hξ hν t k), mul_pow, inv_pow,
    H8_natCast_pow_three, sum_pow_char]

theorem H8_Y_all_zero (n : ℕ) (ξ0 ν x : F) (hξ : ξ0 ≠ 0) (hν : ν ≠ 0) (hnd : 2 * (n / 4) = n / 2)
    (hhalf : ξ0 ^ (n / 2) = -1) (hQodd : Odd (QQ n)) (hqodd : Odd (qq n)) (hξQ : ξ0 ^ QQ n = ξ0)
    (hx : x ^ QQ n = -x) (hνQ : ν ^ QQ n = ν) (h0 : H8_Y n ξ0 ν x 0 = 0) (h1 : H8_Y n ξ0 ν x 1 = 0) :
    ∀ t, H8_Y n ξ0 ν x t = 0 := by
  have key : ∀ t, H8_Y n ξ0 ν x t = 0 ∧ H8_Y n ξ0 ν x (t + 1) = 0 := by
    intro t
    induction t with
    | zero => exact ⟨h0, h1⟩
    | succ t ih =>
      refine ⟨ih.2, ?_⟩
      rw [show t + 1 + 1 = t + 2 by ring, H8_Y_succ_succ n ξ0 ν x hξ hν hnd hhalf hQodd hqodd hξQ hx hνQ,
        ih.1]
      ring
  exact fun t => (key t).1

omit [CharP F 3] in
theorem H8_geom (n : ℕ) (z : F) (hz : z ^ n = 1) (hz1 : z ≠ 1) : ∑ t ∈ range n, z ^ t = 0 := by
  have h := geom_sum_mul z n
  rw [hz, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hz1)

omit [CharP F 3] in
/-- Fourier inversion: `∑_{t<n} y^-_t(x) ξ_0^t = x` (only the `ξ = ξ_0` term of `O ∪ O^{-1}` survives). -/
theorem H8_inversion (n : ℕ) (ξ0 ν x : F) (hξ0 : IsPrimitiveRoot ξ0 n) (hn : (n : F) ≠ 0)
    (hord : orderOf (3 : ZMod n) = n / 4) (hneg : ∀ j : ℕ, (-1 : ZMod n) ≠ 3 ^ j) (h4 : 0 < n / 4) :
    ∑ t ∈ range n, H8_Y n ξ0 ν x t * ξ0 ^ t = x := by
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at h4; simp at h4
    · exact h
  have hξ : ξ0 ≠ 0 := hξ0.ne_zero hnpos.ne'
  unfold H8_Y
  have hrw : ∀ t, (n : F)⁻¹ * (∑ k ∈ range (n / 4), H8_term n ξ0 ν x t k) * ξ0 ^ t =
      (n : F)⁻¹ * ∑ k ∈ range (n / 4), H8_term n ξ0 ν x t k * ξ0 ^ t := by
    intro t; rw [mul_assoc, Finset.sum_mul]
  simp_rw [hrw]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hsplit : ∀ k, ∑ t ∈ range n, H8_term n ξ0 ν x t k * ξ0 ^ t =
      ξ0 ^ (2 * k * 3 ^ k) * x ^ (3 ^ k) * ∑ t ∈ range n, ((ξ0 ^ (3 ^ k))⁻¹ * ξ0) ^ t -
        (ξ0 ^ (2 * k * 3 ^ k))⁻¹ * (ν ^ (3 ^ k))⁻¹ * (x ^ qq n) ^ (3 ^ k) *
          ∑ t ∈ range n, (ξ0 ^ (3 ^ k) * ξ0) ^ t := by
    intro k
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    unfold H8_term
    rw [mul_pow, mul_pow, inv_pow]
    ring
  have hzn : ∀ z : F, z ^ n = 1 → ∀ k : ℕ, ((z ^ (3 ^ k))⁻¹ * z) ^ n = 1 ∧ (z ^ (3 ^ k) * z) ^ n = 1 := by
    intro z hz k
    refine ⟨?_, ?_⟩
    · rw [mul_pow, inv_pow, pow_right_comm, hz, one_pow, inv_one, one_mul]
    · rw [mul_pow, pow_right_comm, hz, one_pow, one_mul]
  -- the `O^{-1}` sums vanish
  have hsecond : ∀ k, ∑ t ∈ range n, (ξ0 ^ (3 ^ k) * ξ0) ^ t = 0 := by
    intro k
    apply H8_geom n _ (hzn ξ0 hξ0.pow_eq_one k).2
    intro h
    rw [← pow_succ] at h
    have hd := (hξ0.pow_eq_one_iff_dvd _).mp h
    have hz : ((3 ^ k + 1 : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    push_cast at hz
    exact hneg k (eq_neg_of_add_eq_zero_left hz).symm
  -- the `O` sums vanish except at `k = 0`
  have hfirst : ∀ k, 0 < k → k < n / 4 → ∑ t ∈ range n, ((ξ0 ^ (3 ^ k))⁻¹ * ξ0) ^ t = 0 := by
    intro k hk0 hk
    apply H8_geom n _ (hzn ξ0 hξ0.pow_eq_one k).1
    intro h
    have h' : ξ0 ^ (3 ^ k) = ξ0 := (inv_mul_eq_one₀ (pow_ne_zero _ hξ)).mp h
    have h3k : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
    rw [H8_pow_pred ξ0 _ h3k] at h'
    have h'' : ξ0 ^ (3 ^ k - 1) = 1 := mul_right_cancel₀ hξ (by rw [h', one_mul])
    have hd := (hξ0.pow_eq_one_iff_dvd _).mp h''
    have hz : ((3 ^ k - 1 : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    rw [Nat.cast_sub h3k, sub_eq_zero] at hz
    push_cast at hz
    exact pow_ne_one_of_lt_orderOf hk0.ne' (by rw [hord]; exact hk) hz
  rw [Finset.sum_eq_single 0]
  · rw [hsplit 0, hsecond 0]
    simp only [mul_zero, pow_zero, pow_one, one_mul, inv_mul_cancel₀ hξ, one_pow,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, sub_zero]
    field_simp
  · intro k hk hk0
    rw [hsplit k, hsecond k, hfirst k (Nat.pos_of_ne_zero hk0) (Finset.mem_range.mp hk)]
    ring
  · intro h
    exact absurd (Finset.mem_range.mpr h4) h

/-- eq:top-all-V, first half: `y^-_0(x) = n^{-1} Λ_ν(x + Tx)` for every `x ∈ V` (pair `k` with `k + m/4`). -/
theorem H8_Y0 (n : ℕ) (ξ0 ν x : F) (h8 : n / 4 = n / 8 + n / 8) (hnd8 : 2 * (n / 8) = n / 4)
    (hξq : ξ0 ^ qq n = -ξ0) (hξ : ξ0 ≠ 0) (hν : ν ≠ 0) (hνq : ν ^ qq n = -ν) (hx : x ^ QQ n = -x)
    (hQ : QQ n = qq n ^ 2) (hι : iota n ξ0 ≠ 0) :
    H8_Y n ξ0 ν x 0 = (n : F)⁻¹ * Lam n ξ0 ν (x + Tmap n ξ0 x) := by
  unfold H8_Y Lam
  congr 1
  rw [h8, Finset.sum_range_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  unfold H8_term Tmap
  have hodd : Odd (3 ^ k) := Odd.pow (by decide)
  have e3 : 3 ^ (n / 8 + k) = qq n * 3 ^ k := by rw [pow_add]; rfl
  have ea : ξ0 ^ (2 * (n / 8 + k) * (qq n * 3 ^ k)) = ξ0 ^ (2 * k * 3 ^ k) * iota n ξ0 ^ (3 ^ k) := by
    rw [show 2 * (n / 8 + k) * (qq n * 3 ^ k) = qq n * (2 * (n / 8 + k) * 3 ^ k) by ring, pow_mul, hξq,
      Even.neg_pow ⟨(n / 8 + k) * 3 ^ k, by ring⟩, iota, ← pow_mul, ← pow_add]
    congr 1
    rw [← hnd8]; ring
  have ex : x ^ (qq n * 3 ^ k) = (x ^ qq n) ^ (3 ^ k) := pow_mul _ _ _
  have ew : (x ^ qq n) ^ (qq n * 3 ^ k) = -(x ^ (3 ^ k)) := by
    rw [← pow_mul, ← mul_assoc, ← pow_two, ← hQ, pow_mul, hx, hodd.neg_pow]
  have en : ν ^ (qq n * 3 ^ k) = -(ν ^ (3 ^ k)) := by rw [pow_mul, hνq, hodd.neg_pow]
  rw [e3, ea, ex, ew, en]
  simp only [zpow_neg, zpow_natCast, pow_zero, inv_one, mul_one]
  rw [add_pow_char_pow, mul_pow, mul_pow]
  have hA : ξ0 ^ (2 * k * 3 ^ k) ≠ 0 := pow_ne_zero _ hξ
  have hI : iota n ξ0 ^ (3 ^ k) ≠ 0 := pow_ne_zero _ hι
  have hN : ν ^ (3 ^ k) ≠ 0 := pow_ne_zero _ hν
  generalize ξ0 ^ (2 * k * 3 ^ k) = A at hA ⊢
  generalize iota n ξ0 ^ (3 ^ k) = I at hI ⊢
  generalize ν ^ (3 ^ k) = N at hN ⊢
  generalize x ^ (3 ^ k) = X
  generalize (x ^ qq n) ^ (3 ^ k) = W
  field_simp
  ring

/-- eq:top-all-V, second half: `y^-_1(x) = n^{-1} Λ'_ν(x - Tx)` for every `x ∈ V`. -/
theorem H8_Y1 (n : ℕ) (ξ0 ν x : F) (h8 : n / 4 = n / 8 + n / 8) (hnd8 : 2 * (n / 8) = n / 4)
    (hξq : ξ0 ^ qq n = -ξ0) (hξ : ξ0 ≠ 0) (hν : ν ≠ 0) (hνq : ν ^ qq n = -ν) (hx : x ^ QQ n = -x)
    (hQ : QQ n = qq n ^ 2) (hι : iota n ξ0 ≠ 0) :
    H8_Y n ξ0 ν x 1 = (n : F)⁻¹ * Lam' n ξ0 ν (x - Tmap n ξ0 x) := by
  unfold H8_Y Lam'
  congr 1
  rw [h8, Finset.sum_range_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  unfold H8_term Tmap
  have hodd : Odd (3 ^ k) := Odd.pow (by decide)
  have e3 : 3 ^ (n / 8 + k) = qq n * 3 ^ k := by rw [pow_add]; rfl
  have ea : ξ0 ^ (2 * (n / 8 + k) * (qq n * 3 ^ k)) = ξ0 ^ (2 * k * 3 ^ k) * iota n ξ0 ^ (3 ^ k) := by
    rw [show 2 * (n / 8 + k) * (qq n * 3 ^ k) = qq n * (2 * (n / 8 + k) * 3 ^ k) by ring, pow_mul, hξq,
      Even.neg_pow ⟨(n / 8 + k) * 3 ^ k, by ring⟩, iota, ← pow_mul, ← pow_add]
    congr 1
    rw [← hnd8]; ring
  have eb : ξ0 ^ (qq n * 3 ^ k) = -(ξ0 ^ (3 ^ k)) := by rw [pow_mul, hξq, hodd.neg_pow]
  have ex : x ^ (qq n * 3 ^ k) = (x ^ qq n) ^ (3 ^ k) := pow_mul _ _ _
  have ew : (x ^ qq n) ^ (qq n * 3 ^ k) = -(x ^ (3 ^ k)) := by
    rw [← pow_mul, ← mul_assoc, ← pow_two, ← hQ, pow_mul, hx, hodd.neg_pow]
  have en : ν ^ (qq n * 3 ^ k) = -(ν ^ (3 ^ k)) := by rw [pow_mul, hνq, hodd.neg_pow]
  have ez : ξ0 ^ ((2 * (k : ℤ) - 1) * 3 ^ k) = ξ0 ^ (2 * k * 3 ^ k) * (ξ0 ^ (3 ^ k))⁻¹ := by
    rw [show (2 * (k : ℤ) - 1) * 3 ^ k = ((2 * k * 3 ^ k : ℕ) : ℤ) - ((3 ^ k : ℕ) : ℤ) by push_cast; ring,
      zpow_sub₀ hξ, zpow_natCast, zpow_natCast, div_eq_mul_inv]
  rw [e3, ea, eb, ex, ew, en]
  rw [zpow_neg, ez]
  simp only [zpow_neg, zpow_natCast, pow_one]
  rw [sub_pow_char_pow, mul_pow, mul_pow]
  have hA : ξ0 ^ (2 * k * 3 ^ k) ≠ 0 := pow_ne_zero _ hξ
  have hB : ξ0 ^ (3 ^ k) ≠ 0 := pow_ne_zero _ hξ
  have hI : iota n ξ0 ^ (3 ^ k) ≠ 0 := pow_ne_zero _ hι
  have hN : ν ^ (3 ^ k) ≠ 0 := pow_ne_zero _ hν
  generalize ξ0 ^ (2 * k * 3 ^ k) = A at hA ⊢
  generalize ξ0 ^ (3 ^ k) = B at hB ⊢
  generalize iota n ξ0 ^ (3 ^ k) = I at hI ⊢
  generalize ν ^ (3 ^ k) = N at hN ⊢
  generalize x ^ (3 ^ k) = X
  generalize (x ^ qq n) ^ (3 ^ k) = W
  field_simp
  ring

theorem H8_Lam_add (n : ℕ) (ξ0 ν u v : F) : Lam n ξ0 ν (u + v) = Lam n ξ0 ν u + Lam n ξ0 ν v := by
  unfold Lam
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [add_pow_char_pow]; ring

theorem H8_Lam'_add (n : ℕ) (ξ0 ν u v : F) : Lam' n ξ0 ν (u + v) = Lam' n ξ0 ν u + Lam' n ξ0 ν v := by
  unfold Lam'
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [add_pow_char_pow]; ring

omit [CharP F 3] in
theorem H8_Lam_zero (n : ℕ) (ξ0 ν : F) : Lam n ξ0 ν 0 = 0 := by
  unfold Lam
  apply Finset.sum_eq_zero
  intro k _
  rw [zero_pow (pow_ne_zero _ (by norm_num)), mul_zero]

omit [CharP F 3] in
theorem H8_Lam'_zero (n : ℕ) (ξ0 ν : F) : Lam' n ξ0 ν 0 = 0 := by
  unfold Lam'
  apply Finset.sum_eq_zero
  intro k _
  rw [zero_pow (pow_ne_zero _ (by norm_num)), mul_zero]

theorem H8_Lam_sub (n : ℕ) (ξ0 ν u v : F) : Lam n ξ0 ν (u - v) = Lam n ξ0 ν u - Lam n ξ0 ν v := by
  have h := H8_Lam_add n ξ0 ν (u - v) v
  rw [sub_add_cancel] at h
  rw [h]; ring

theorem H8_Lam'_sub (n : ℕ) (ξ0 ν u v : F) : Lam' n ξ0 ν (u - v) = Lam' n ξ0 ν u - Lam' n ξ0 ν v := by
  have h := H8_Lam'_add n ξ0 ν (u - v) v
  rw [sub_add_cancel] at h
  rw [h]; ring

end Fourier

/-! ## 8. Theorem 3.4(d) -/

/-- Row 11d — Theorem 3.4(d) (s3_pow2.tex:117-118): for every `ν ∈ k_0` with `ν^{q-1} = -1`, `Λ_ν` is injective on
`V_+` and `Λ'_ν` on `V_-`; hence `x ↦ n^{-1}Λ_ν(x + Tx)` on `V` has kernel exactly `V_-`. -/
theorem thm_3_4_d_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 4 ≤ e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) (ν : GaloisField 3 (n / 2)) (hνk : ν ^ QQ n = ν) (hν : ν ^ (qq n - 1) = -1) :
    Set.InjOn (Lam n ξ0 ν) (Vplus n ξ0) ∧ Set.InjOn (Lam' n ξ0 ν) (Vminus n ξ0) ∧
      ∀ x ∈ Vsp n, ((n : GaloisField 3 (n / 2))⁻¹ * Lam n ξ0 ν (x + Tmap n ξ0 x) = 0 ↔ x ∈ Vminus n ξ0) := by
  obtain ⟨hQ, hqodd, hQodd, hι2, hιq, hξq, hξQ, hhalf, hξ, hnd8, hnd, h8, hq9, hn, hnpos⟩ :=
    H8_setup n e hne he ξ0 hξ0
  obtain ⟨hord, hneg⟩ := H8_ord n e hne (by omega)
  have hι0 : iota n ξ0 ≠ 0 := by
    intro h; rw [h] at hι2; norm_num at hι2
  have hν0 : ν ≠ 0 := by
    intro h; rw [h, zero_pow (by omega)] at hν; exact one_ne_zero (neg_eq_zero.mp hν.symm)
  have hνq : ν ^ qq n = -ν := by rw [H8_pow_pred ν _ (by omega), hν]; ring
  have h16 : 16 ≤ n := by
    rw [hne]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have h4 : 0 < n / 4 := by omega
  -- the key: `x ∈ V`, `Λ_ν(x + Tx) = 0`, `Λ'_ν(x - Tx) = 0` force `x = 0`
  have key : ∀ x ∈ (Vsp n : Set (GaloisField 3 (n / 2))), Lam n ξ0 ν (x + Tmap n ξ0 x) = 0 →
      Lam' n ξ0 ν (x - Tmap n ξ0 x) = 0 → x = 0 := by
    intro x hx hL hL'
    have hx' : x ^ QQ n = -x := hx
    have hY0 : H8_Y n ξ0 ν x 0 = 0 := by
      rw [H8_Y0 n ξ0 ν x h8 hnd8 hξq hξ hν0 hνq hx' hQ hι0, hL, mul_zero]
    have hY1 : H8_Y n ξ0 ν x 1 = 0 := by
      rw [H8_Y1 n ξ0 ν x h8 hnd8 hξq hξ hν0 hνq hx' hQ hι0, hL', mul_zero]
    have hall := H8_Y_all_zero n ξ0 ν x hξ hν0 hnd hhalf hQodd hqodd hξQ hx' hνk hY0 hY1
    rw [← H8_inversion n ξ0 ν x hξ0 hn hord hneg h4]
    apply Finset.sum_eq_zero
    intro t _
    rw [hall t, zero_mul]
  have hinjp : Set.InjOn (Lam n ξ0 ν) (Vplus n ξ0) := by
    intro a ha b hb hab
    have hx : a - b ∈ (Vsp n : Set (GaloisField 3 (n / 2))) := H8_V_sub n hQodd a b ha.1 hb.1
    have hT : Tmap n ξ0 (a - b) = a - b := by rw [H8_T_sub n hqodd, ha.2, hb.2]
    have hz := key (a - b) hx (by rw [hT, H8_Lam_add, H8_Lam_sub, hab, sub_self, add_zero])
      (by rw [hT, sub_self, H8_Lam'_zero])
    exact sub_eq_zero.mp hz
  have hinjm : Set.InjOn (Lam' n ξ0 ν) (Vminus n ξ0) := by
    intro a ha b hb hab
    have hx : a - b ∈ (Vsp n : Set (GaloisField 3 (n / 2))) := H8_V_sub n hQodd a b ha.1 hb.1
    have hT : Tmap n ξ0 (a - b) = -(a - b) := by rw [H8_T_sub n hqodd, ha.2, hb.2]; ring
    have hz := key (a - b) hx (by rw [hT, add_neg_cancel, H8_Lam_zero])
      (by rw [hT, sub_neg_eq_add, H8_Lam'_add, H8_Lam'_sub, hab, sub_self, add_zero])
    exact sub_eq_zero.mp hz
  refine ⟨hinjp, hinjm, fun x hx => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have hL : Lam n ξ0 ν (x + Tmap n ξ0 x) = 0 :=
      (mul_eq_zero.mp h).resolve_left (inv_ne_zero hn)
    have hT := H8_T_mem n hQ hqodd ξ0 hιq x hx
    have hTT := H8_TT n hQ ξ0 hι2 hιq x hx
    have hp : x + Tmap n ξ0 x ∈ Vplus n ξ0 :=
      ⟨H8_V_add n _ _ hx hT, by rw [H8_T_add, hTT, add_comm]⟩
    have h0 : (0 : GaloisField 3 (n / 2)) ∈ Vplus n ξ0 := by
      refine ⟨?_, ?_⟩
      · show (0 : GaloisField 3 (n / 2)) ^ QQ n = -0
        rw [zero_pow (by rw [hQ]; positivity), neg_zero]
      · simp only [Tmap]; rw [zero_pow (by omega), mul_zero]
    have hp0 : x + Tmap n ξ0 x = 0 := hinjp hp h0 (by rw [hL, H8_Lam_zero])
    exact ⟨hx, by linear_combination hp0⟩
  · have hp0 : x + Tmap n ξ0 x = 0 := by rw [h.2, add_neg_cancel]
    rw [hp0, H8_Lam_zero, mul_zero]

/-! ## 9. The conic is not a product (P10s_main.tex:196-198) -/

/-- Coverage — P10s_main.tex:196-198 (review S2(a)): for `n = 2^e`, `e ≥ 5` odd, the points of a fibre form a conic in `V`
(Thm 3.4(c)), not a product of a subset of `V_+` and a subset of `V_-`. -/
theorem intro_conic_not_product_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 5 ≤ e) (_heo : Odd e)
    (ξ0 : GaloisField 3 (n / 2)) (hξ0 : IsPrimitiveRoot ξ0 n) (ν : GaloisField 3 (n / 2)) (hν : ν ^ (qq n - 1) = -1) :
    ¬ ∃ A B : Set (GaloisField 3 (n / 2)),
      {pr : GaloisField 3 (n / 2) × GaloisField 3 (n / 2) |
        pr.1 ∈ Vplus n ξ0 ∧ pr.2 ∈ Vminus n ξ0 ∧ pr.1 ^ 2 - pr.2 ^ 2 = iota n ξ0 * ν} = A ×ˢ B := by
  classical
  rintro ⟨A, B, hAB⟩
  obtain ⟨hQ, hqodd, hQodd, hι2, hιq, -, -, -, -, -, -, -, hq9, -, -⟩ := H8_setup n e hne (by omega) ξ0 hξ0
  set q := qq n with hqdef
  have hν0 : ν ≠ 0 := by
    intro h; rw [h, zero_pow (by omega)] at hν; exact one_ne_zero (neg_eq_zero.mp hν.symm)
  -- every `x` with `x^{q+1} = ν` gives the point `(-(x+Tx), -(x-Tx))` of the conic
  have hmem : ∀ x : GaloisField 3 (n / 2), x ^ (q + 1) = ν →
      (-(x + Tmap n ξ0 x), -(x - Tmap n ξ0 x)) ∈ {pr : GaloisField 3 (n / 2) × GaloisField 3 (n / 2) |
        pr.1 ∈ Vplus n ξ0 ∧ pr.2 ∈ Vminus n ξ0 ∧ pr.1 ^ 2 - pr.2 ^ 2 = iota n ξ0 * ν} := by
    intro x hx
    have hxV : x ∈ (Vsp n : Set (GaloisField 3 (n / 2))) := by
      show x ^ QQ n = -x
      obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
      have hexp : QQ n = (q + 1) * (q - 1) + 1 := by
        rw [hQ, hr, Nat.add_sub_cancel]; ring
      rw [hexp, pow_succ, pow_mul, hx, hν, neg_one_mul]
    obtain ⟨hp, hm⟩ := H8_dec_mem n hQ hqodd hQodd ξ0 hι2 hιq x hxV
    refine ⟨hp, hm, ?_⟩
    simp only
    rw [show (-(x + Tmap n ξ0 x)) ^ 2 - (-(x - Tmap n ξ0 x)) ^ 2 =
        x * Tmap n ξ0 x + 3 * (x * Tmap n ξ0 x) by ring, H8_three_eq_zero, zero_mul, add_zero]
    simp only [Tmap]
    rw [mul_left_comm, ← pow_succ', hx]
  -- roots of unity
  obtain ⟨ζ, hζ⟩ := H8_prim2Q n e hne (by omega)
  have hsplit2 : 2 * (QQ n - 1) = (q + 1) * (2 * (q - 1)) := by
    obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    rw [hQ, hr, show (r + 1) ^ 2 = (r ^ 2 + 2 * r) + 1 by ring, Nat.add_sub_cancel, Nat.add_sub_cancel]
    ring
  have hpos : 0 < 2 * (QQ n - 1) := by rw [hsplit2]; exact Nat.mul_pos (by omega) (by omega)
  have hζ1 : IsPrimitiveRoot (ζ ^ (q + 1)) (2 * (q - 1)) := hζ.pow hpos hsplit2
  have hζ2 : IsPrimitiveRoot (ζ ^ (2 * (q - 1))) (q + 1) := hζ.pow hpos (by rw [hsplit2, mul_comm])
  have hν2 : ν ^ (2 * (q - 1)) = 1 := by rw [mul_comm, pow_mul, hν]; norm_num
  have : NeZero (2 * (q - 1)) := ⟨by omega⟩
  obtain ⟨i, -, hi⟩ := hζ1.eq_pow_of_pow_eq_one hν2
  set x0 := ζ ^ i with hx0
  have hx0ν : x0 ^ (q + 1) = ν := by rw [hx0, ← pow_mul, mul_comm, pow_mul, hi]
  have hx00 : x0 ≠ 0 := by
    intro h; rw [h, zero_pow (by omega)] at hx0ν; exact hν0 hx0ν.symm
  set ω := ζ ^ (2 * (q - 1)) with hω
  let pt : ℕ → GaloisField 3 (n / 2) × GaloisField 3 (n / 2) := fun j =>
    (-(x0 * ω ^ j + Tmap n ξ0 (x0 * ω ^ j)), -(x0 * ω ^ j - Tmap n ξ0 (x0 * ω ^ j)))
  have hptmem : ∀ j, pt j ∈ A ×ˢ B := by
    intro j
    rw [← hAB]
    apply hmem
    rw [mul_pow, hx0ν, pow_right_comm, hζ2.pow_eq_one, one_pow, mul_one]
  have hptinj : Set.InjOn pt (range (q + 1) : Set ℕ) := by
    intro j hj j' hj' h
    have hsum := congrArg (fun pr : GaloisField 3 (n / 2) × GaloisField 3 (n / 2) => pr.1 + pr.2) h
    simp only [pt, H8_dec_sum] at hsum
    have hω : ω ^ j = ω ^ j' := mul_left_cancel₀ hx00 hsum
    exact hζ2.pow_inj (Finset.mem_range.mp hj) (Finset.mem_range.mp hj') hω
  -- a product inside the conic has at most 4 points
  set a0 := (pt 0).1 with ha0
  set b0 := (pt 0).2 with hb0
  have hpt0 : pt 0 ∈ {pr : GaloisField 3 (n / 2) × GaloisField 3 (n / 2) |
      pr.1 ∈ Vplus n ξ0 ∧ pr.2 ∈ Vminus n ξ0 ∧ pr.1 ^ 2 - pr.2 ^ 2 = iota n ξ0 * ν} := by
    rw [hAB]; exact hptmem 0
  have hsub : ∀ j, pt j ∈ ({(a0, b0), (a0, -b0), (-a0, b0), (-a0, -b0)} :
      Finset (GaloisField 3 (n / 2) × GaloisField 3 (n / 2))) := by
    intro j
    have hj := hptmem j
    have h0 := hptmem 0
    rw [Set.mem_prod] at hj h0
    have h1 : ((pt j).1, b0) ∈ {pr : GaloisField 3 (n / 2) × GaloisField 3 (n / 2) |
        pr.1 ∈ Vplus n ξ0 ∧ pr.2 ∈ Vminus n ξ0 ∧ pr.1 ^ 2 - pr.2 ^ 2 = iota n ξ0 * ν} := by
      rw [hAB, Set.mem_prod]; exact ⟨hj.1, h0.2⟩
    have h2 : (a0, (pt j).2) ∈ {pr : GaloisField 3 (n / 2) × GaloisField 3 (n / 2) |
        pr.1 ∈ Vplus n ξ0 ∧ pr.2 ∈ Vminus n ξ0 ∧ pr.1 ^ 2 - pr.2 ^ 2 = iota n ξ0 * ν} := by
      rw [hAB, Set.mem_prod]; exact ⟨h0.1, hj.2⟩
    have e0 := hpt0.2.2
    have e1 := h1.2.2
    have e2 := h2.2.2
    simp only at e0 e1 e2
    have hsq1 : (pt j).1 ^ 2 = a0 ^ 2 := by linear_combination e1 - e0
    have hsq2 : (pt j).2 ^ 2 = b0 ^ 2 := by linear_combination e0 - e2
    have hpj : pt j = ((pt j).1, (pt j).2) := rfl
    rw [hpj]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq1 with h | h <;>
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq2 with h' | h' <;>
      · rw [h, h']; simp
  have hcard : (range (q + 1)).card ≤ ({(a0, b0), (a0, -b0), (-a0, b0), (-a0, -b0)} :
      Finset (GaloisField 3 (n / 2) × GaloisField 3 (n / 2))).card := by
    rw [← Finset.card_image_of_injOn hptinj]
    apply Finset.card_le_card
    intro pr hpr
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hpr
    exact hsub j
  have h4 := Finset.card_le_four (a := (a0, b0)) (b := (a0, -b0)) (c := (-a0, b0)) (d := (-a0, -b0))
  rw [Finset.card_range] at hcard
  omega

end Xia.Proofs

#print axioms Xia.Proofs.thm_3_4_a_proved
#print axioms Xia.Proofs.thm_3_4_d_proved
#print axioms Xia.Proofs.intro_conic_not_product_proved
