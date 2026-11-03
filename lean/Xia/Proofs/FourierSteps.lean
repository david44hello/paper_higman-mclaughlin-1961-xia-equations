/- Xia/Proofs/FourierSteps.lean — proofs of the rows rem_2_6, thm_4_1_descent, thm_4_1_step4 of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry
import Xia.Defs.Layer0

namespace Xia.Proofs

open Xia Finset

/-! ## 1. Generic helpers on `ZMod n` (adapted from Xia/Proofs/Sec22.lean) -/

/-- Powers of an `x` with `x^n = 1` along `ZMod n` are additive in the exponent. -/
theorem H9_pow_val_add {n : ℕ} [NeZero n] {M : Type*} [Monoid M] (x : M) (hx : x ^ n = 1)
    (a b : ZMod n) : x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hx, pow_add]

/-- `(n/2 : ZMod n).val = n/2`. -/
theorem H9_half_val {n : ℕ} [NeZero n] : (half n : ZMod n).val = n / 2 := by
  unfold half
  rw [ZMod.val_natCast]
  have := NeZero.pos n
  exact Nat.mod_eq_of_lt (by omega)

/-- For even `n`: `m + m = 0` in `ZMod n`. -/
theorem H9_two_half {n : ℕ} [NeZero n] (hn : Even n) : half n + half n = (0 : ZMod n) := by
  unfold half
  rw [← Nat.cast_add]
  have h2 : n % 2 = 0 := Nat.even_iff.mp hn
  have : n / 2 + n / 2 = n := by omega
  rw [this, ZMod.natCast_self]

/-- For even `n`: `-m = m` in `ZMod n`. -/
theorem H9_neg_half {n : ℕ} [NeZero n] (hn : Even n) : -(half n : ZMod n) = half n := by
  rw [neg_eq_iff_add_eq_zero, H9_two_half hn]

/-- For even `n`: `m ≠ 0` in `ZMod n`. -/
theorem H9_half_ne_zero {n : ℕ} [NeZero n] (hn : Even n) : (half n : ZMod n) ≠ 0 := by
  intro h
  have h1 := H9_half_val (n := n)
  rw [h, ZMod.val_zero] at h1
  have := NeZero.pos n
  have h2 : n % 2 = 0 := Nat.even_iff.mp hn
  omega

/-- For even `n`: if `t.val ≥ m` then `(t + m).val < m`. -/
theorem H9_add_half_val_lt {n : ℕ} [NeZero n] (hn : Even n) (t : ZMod n) (ht : ¬ t.val < n / 2) :
    (t + half n).val < n / 2 := by
  rw [ZMod.val_add, H9_half_val]
  have hlt := ZMod.val_lt t
  have h2 : n % 2 = 0 := Nat.even_iff.mp hn
  rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- For even `n`, `(a + b).val` has the parity of `a.val + b.val`. -/
theorem H9_even_val_add {n : ℕ} [NeZero n] (hn : Even n) (a b : ZMod n) :
    Even (a + b).val ↔ Even (a.val + b.val) := by
  rw [ZMod.val_add, Nat.even_iff, Nat.even_iff, Nat.mod_mod_of_dvd _ (even_iff_two_dvd.mp hn)]

/-- For even `n`, the parity of `(N : ZMod n).val` is that of `N`. -/
theorem H9_even_natCast_val {n : ℕ} [NeZero n] (hn : Even n) (N : ℕ) :
    Even ((N : ZMod n)).val ↔ Even N := by
  rw [ZMod.val_natCast, Nat.even_iff, Nat.even_iff, Nat.mod_mod_of_dvd _ (even_iff_two_dvd.mp hn)]

/-- If `n` and `n/2` are even, `k + n/2` has the parity of `k`. -/
theorem H9_even_add_half {n : ℕ} [NeZero n] (hn : Even n) (hm : Even (n / 2)) (k : ZMod n) :
    Even (k + half n).val ↔ Even k.val := by
  rw [H9_even_val_add hn, H9_half_val, Nat.even_add]
  exact ⟨fun h => h.2 hm, fun h => ⟨fun _ => hm, fun _ => h⟩⟩

theorem H9_odd_add_half {n : ℕ} [NeZero n] (hn : Even n) (hm : Even (n / 2)) (k : ZMod n) :
    Odd (k + half n).val ↔ Odd k.val := by
  rw [← Nat.not_even_iff_odd, ← Nat.not_even_iff_odd, H9_even_add_half hn hm]

/-- For even `n`, `2k` is even. -/
theorem H9_even_two_mul {n : ℕ} [NeZero n] (hn : Even n) (k : ZMod n) : Even (2 * k).val := by
  rw [two_mul, H9_even_val_add hn]
  exact ⟨k.val, rfl⟩

/-- For even `n`: `2z = 0` iff `z ∈ {0, m}`. -/
theorem H9_two_mul_eq_zero_iff {n : ℕ} [NeZero n] (hn : Even n) (z : ZMod n) :
    2 * z = 0 ↔ z = 0 ∨ z = half n := by
  have key : 2 * z = 0 ↔ -z = z := by rw [neg_eq_iff_add_eq_zero, two_mul]
  rw [key, ZMod.neg_eq_self_iff]
  have h2 : n % 2 = 0 := Nat.even_iff.mp hn
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      rw [← ZMod.natCast_zmod_val z]
      unfold half
      congr 1
      omega
  · rintro (h | h)
    · exact Or.inl h
    · right
      rw [h, H9_half_val]
      omega

/-- For even `n`: `2x = 2w` iff `x = w` or `x = w + m` (the two square roots). -/
theorem H9_two_mul_eq_iff {n : ℕ} [NeZero n] (hn : Even n) (x w : ZMod n) :
    2 * x = 2 * w ↔ x = w ∨ x = w + half n := by
  rw [← sub_eq_zero, ← mul_sub, H9_two_mul_eq_zero_iff hn, sub_eq_zero, sub_eq_iff_eq_add']

/-- Splitting a product over `{ρ : 2 g(ρ) = 2 w}` into the two square-root classes. -/
theorem H9_prod_split {n : ℕ} [NeZero n] (hn : Even n) {M : Type*} [CommMonoid M] (T : Finset (ZMod n))
    (g : ZMod n → ZMod n) (f : ZMod n → M) (w : ZMod n) :
    ∏ ρ ∈ T.filter (fun ρ => 2 * g ρ = 2 * w), f ρ =
      (∏ ρ ∈ T.filter (fun ρ => g ρ = w), f ρ) * ∏ ρ ∈ T.filter (fun ρ => g ρ = w + half n), f ρ := by
  have hdisj : Disjoint (T.filter (fun ρ => g ρ = w)) (T.filter (fun ρ => g ρ = w + half n)) := by
    rw [Finset.disjoint_filter]
    intro ρ _ h1 h2
    apply H9_half_ne_zero hn
    linear_combination h1 - h2
  rw [← Finset.prod_union hdisj, ← Finset.filter_or]
  exact Finset.prod_congr (Finset.filter_congr (fun ρ _ => H9_two_mul_eq_iff hn _ _)) (fun _ _ => rfl)

/-- A sum of a function that changes sign under a shift vanishes (when `2 ≠ 0`). -/
theorem H9_sum_antiperiodic {n : ℕ} [NeZero n] {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (f : ZMod n → K)
    (c : ZMod n) (hf : ∀ t, f (t + c) = -f t) : ∑ t, f t = 0 := by
  have hX : ∑ t, f t = -∑ t, f t := by
    rw [← Finset.sum_neg_distrib]
    exact Fintype.sum_equiv (Equiv.addRight c) _ _ (fun t => by
      simp only [Equiv.coe_addRight]
      rw [hf, neg_neg])
  have h2X : (2 : K) * ∑ t, f t = 0 := by linear_combination hX
  exact (mul_eq_zero.mp h2X).resolve_left h2

theorem H9_eq_zero_of_eq_neg {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {x : K} (hx : x = -x) : x = 0 := by
  have h2x : (2 : K) * x = 0 := by linear_combination hx
  exact (mul_eq_zero.mp h2x).resolve_left h2

/-- `(-1)^{(t + m).val} = (-1)^{t.val}` when `n` and `n/2` are even. -/
theorem H9_sgn_add_half {n : ℕ} [NeZero n] (hn : Even n) (hm : Even (n / 2)) {K : Type*} [CommRing K]
    (t : ZMod n) : (sgn (t + half n) : K) = sgn t := by
  unfold sgn
  rw [H9_pow_val_add (-1 : K) hn.neg_one_pow, H9_half_val, hm.neg_one_pow, mul_one]

/-- `n = 2^a n_odd` with `a ≥ 2`: `n` and `n/2` are even. -/
theorem H9_even_halves {n a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 2 ≤ a) : Even n ∧ Even (n / 2) := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
  have e : n = 4 * (2 ^ b * nodd) := by rw [hn]; ring
  exact ⟨⟨2 * (2 ^ b * nodd), by omega⟩, ⟨2 ^ b * nodd, by omega⟩⟩

/-! ## 2. Roots of unity and the transform -/

theorem H9_omega_half {n : ℕ} [NeZero n] (hn : Even n) {L : Type*} [Field L] {ω : L}
    (hω : IsPrimitiveRoot ω n) : ω ^ (n / 2) = -1 := by
  have h2 : n % 2 = 0 := Nat.even_iff.mp hn
  exact (hω.pow (NeZero.pos n) (show n = n / 2 * 2 by omega)).eq_neg_one_of_two_right

theorem H9_pow_n {n : ℕ} [NeZero n] {L : Type*} [CommRing L] {ω : L} (hω : IsPrimitiveRoot ω n)
    (k : ZMod n) : (ω ^ k.val) ^ n = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]

theorem H9_pow_half {n : ℕ} [NeZero n] (hn : Even n) {L : Type*} [Field L] {ω : L}
    (hω : IsPrimitiveRoot ω n) (k : ZMod n) : (ω ^ k.val) ^ (half n).val = (-1) ^ k.val := by
  rw [H9_half_val, ← pow_mul, mul_comm, pow_mul, H9_omega_half hn hω]

/-- `ω^{(k+m).val} = -ω^{k.val}` (exponent model of `-ξ`). -/
theorem H9_omega_add_half {n : ℕ} [NeZero n] (hn : Even n) {L : Type*} [Field L] {ω : L}
    (hω : IsPrimitiveRoot ω n) (k : ZMod n) : ω ^ (k + half n).val = -ω ^ k.val := by
  rw [H9_pow_val_add ω hω.pow_eq_one, H9_half_val, H9_omega_half hn hω, mul_neg_one]

/-- Shifting the sequence by `m` multiplies `ŷ(ω^k)` by `(-1)^k`. -/
theorem H9_dft_shift {n : ℕ} [NeZero n] (hn : Even n) {L : Type*} [Field L] {ω : L}
    (hω : IsPrimitiveRoot ω n) (z : ZMod n → L) (k : ZMod n) :
    dft ω z k = (-1) ^ k.val * dft ω (fun t => z (t + half n)) k := by
  unfold dft
  rw [Finset.mul_sum]
  refine (Fintype.sum_equiv (Equiv.addRight (half n)) _ _ (fun t => ?_)).symm
  simp only [Equiv.coe_addRight]
  rw [H9_pow_val_add _ (H9_pow_n hω k) t (half n), H9_pow_half hn hω k]
  ring

theorem H9_dft_neg {n : ℕ} [NeZero n] {L : Type*} [CommRing L] (ω : L) (z : ZMod n → L) (k : ZMod n) :
    dft ω (fun t => -z t) k = -dft ω z k := by
  unfold dft
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun t _ => by ring)

theorem H9_dftA_add {n : ℕ} [NeZero n] {F L : Type*} [CommRing F] [CommRing L] [Algebra F L] (ω : L)
    (u v : ZMod n → F) (k : ZMod n) : dftA ω (fun t => u t + v t) k = dftA ω u k + dftA ω v k := by
  simp only [dftA, dft]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun t _ => by rw [map_add]; ring)

/-- `ŷ(-1) = S` (exponent model: `-1 ↔ m`). -/
theorem H9_dftA_half {n : ℕ} [NeZero n] (hn : Even n) {F L : Type*} [Field F] [Field L] [Algebra F L] {ω : L}
    (hω : IsPrimitiveRoot ω n) (y : ZMod n → F) : dftA ω y (half n) = algebraMap F L (S y) := by
  simp only [dftA, dft, S, sgn]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [H9_half_val, H9_omega_half hn hω, map_mul, map_pow, map_neg, map_one]
  ring

/-- (F3) at `ξ = -1` gives `S^2 = 1` when `n/2` is even. -/
theorem H9_S_sq {n : ℕ} [NeZero n] (hn : Even n) (hm : Even (n / 2)) {F L : Type*} [Field F] [Field L]
    [Algebra F L] {ω : L} (hω : IsPrimitiveRoot ω n) (y : ZMod n → F) (hF3 : F3 ω (dftA ω y)) :
    algebraMap F L (S y) * algebraMap F L (S y) = 1 := by
  have e := hF3 (half n)
  rw [H9_neg_half hn, H9_dftA_half hn hω y, H9_half_val, H9_omega_half hn hω, hm.neg_one_pow] at e
  exact e

/-- `s^{2^b} = 1` from `s^2 = 1`, `b ≥ 1`. -/
theorem H9_pow_two_pow {M : Type*} [Monoid M] {s : M} (hs2 : s * s = 1) {b : ℕ} (hb : 1 ≤ b) :
    s ^ (2 ^ b) = 1 := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  rw [pow_succ', pow_mul, pow_two, hs2, one_pow]

/-! ## 3. Characteristic 3: `x̄`, `x^±` -/

theorem H9_two_ne_zero_GF (m : ℕ) : (2 : GaloisField 3 m) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : GaloisField 3 m) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff (GaloisField 3 m) 3] at h'
  norm_num at h'

theorem H9_two_ne_zero_L {m : ℕ} {L : Type*} [Field L] [Algebra (GaloisField 3 m) L] : (2 : L) ≠ 0 := by
  have e : algebraMap (GaloisField 3 m) L 2 = 2 := map_ofNat _ 2
  rw [← e]
  exact (map_ne_zero _).mpr (H9_two_ne_zero_GF m)

theorem H9_frob_fix (m : ℕ) (hm : m ≠ 0) (x : GaloisField 3 m) : x ^ (3 ^ m) = x := by
  let _inst : Fintype (GaloisField 3 m) := Fintype.ofFinite _
  have h := FiniteField.pow_card x
  rwa [← Nat.card_eq_fintype_card, GaloisField.card 3 m hm] at h

theorem H9_bar_add {m : ℕ} (n : ℕ) (x z : GaloisField 3 m) : bar n (x + z) = bar n x + bar n z :=
  map_add (iterateFrobenius (GaloisField 3 m) 3 (n / 4)) x z

theorem H9_bar_sub {m : ℕ} (n : ℕ) (x z : GaloisField 3 m) : bar n (x - z) = bar n x - bar n z :=
  map_sub (iterateFrobenius (GaloisField 3 m) 3 (n / 4)) x z

theorem H9_bar_div_two {m : ℕ} (n : ℕ) (x : GaloisField 3 m) : bar n (x / 2) = bar n x / 2 := by
  have h := map_div₀ (iterateFrobenius (GaloisField 3 m) 3 (n / 4)) x 2
  rw [map_ofNat] at h
  exact h

theorem H9_bar_bar (n : ℕ) [NeZero n] (h4 : 4 ∣ n) (x : GaloisField 3 (n / 2)) : bar n (bar n x) = x := by
  have hn0 := NeZero.ne n
  unfold bar
  rw [← pow_mul, ← pow_add, show n / 4 + n / 4 = n / 2 by omega]
  exact H9_frob_fix (n / 2) (by omega) x

theorem H9_bar_yPlus (n : ℕ) [NeZero n] (h4 : 4 ∣ n) (x : GaloisField 3 (n / 2)) :
    bar n (yPlus n x) = yPlus n x := by
  unfold yPlus
  rw [H9_bar_div_two, H9_bar_add, H9_bar_bar n h4, add_comm]

theorem H9_bar_yMinus (n : ℕ) [NeZero n] (h4 : 4 ∣ n) (x : GaloisField 3 (n / 2)) :
    bar n (yMinus n x) = -yMinus n x := by
  unfold yMinus
  rw [H9_bar_div_two, H9_bar_sub, H9_bar_bar n h4]
  ring

theorem H9_yPlus_bar (n : ℕ) [NeZero n] (h4 : 4 ∣ n) (x : GaloisField 3 (n / 2)) :
    yPlus n (bar n x) = yPlus n x := by
  unfold yPlus
  rw [H9_bar_bar n h4, add_comm]

theorem H9_yMinus_bar (n : ℕ) [NeZero n] (h4 : 4 ∣ n) (x : GaloisField 3 (n / 2)) :
    yMinus n (bar n x) = -yMinus n x := by
  unfold yMinus
  rw [H9_bar_bar n h4]
  ring

theorem H9_split {m : ℕ} (n : ℕ) (x : GaloisField 3 m) : yPlus n x + yMinus n x = x := by
  have h2 := H9_two_ne_zero_GF m
  unfold yPlus yMinus
  field_simp
  ring

theorem H9_sq_diff {m : ℕ} (n : ℕ) (x : GaloisField 3 m) :
    yPlus n x ^ 2 - yMinus n x ^ 2 = x * bar n x := by
  have h2 := H9_two_ne_zero_GF m
  unfold yPlus yMinus
  field_simp
  ring

theorem H9_two_yPlus {m : ℕ} (n : ℕ) (x : GaloisField 3 m) : 2 * yPlus n x = x + bar n x := by
  have h2 := H9_two_ne_zero_GF m
  unfold yPlus
  field_simp

/-! ## 4. (L1)-(L4) consequences on the sequence side -/

/-- (L1) with `σ = 2` iterated: `y_{t+2j} = y_t^{3^j}`. -/
theorem H9_iter {n : ℕ} [NeZero n] {K : Type*} [CommRing K] {y : ZMod n → K} (h1 : L1 3 2 y)
    (t : ZMod n) (j : ℕ) : y (t + ((2 * j : ℕ) : ZMod n)) = y t ^ (3 ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := h1 (t + ((2 * j : ℕ) : ZMod n))
    have e : t + ((2 * (j + 1) : ℕ) : ZMod n) = t + ((2 * j : ℕ) : ZMod n) + ((2 : ℤ) : ZMod n) := by
      push_cast; ring
    rw [e, h, ih, ← pow_mul, ← pow_succ]

/-- For `4 ∣ n`: `y_{t+m} = ȳ_t`. -/
theorem H9_shift_half {n : ℕ} [NeZero n] (h4 : 4 ∣ n) {K : Type*} [CommRing K] {y : ZMod n → K}
    (h1 : L1 3 2 y) (t : ZMod n) : y (t + half n) = bar n (y t) := by
  have e : half n = ((2 * (n / 4) : ℕ) : ZMod n) := by
    unfold half; congr 1; omega
  rw [e, H9_iter h1 t]
  rfl

/-- `R(-s) = R(s)`. -/
theorem H9_R_neg {n : ℕ} [NeZero n] {K : Type*} [CommRing K] (y : ZMod n → K) (s : ZMod n) :
    R y (-s) = R y s := by
  unfold R
  exact Fintype.sum_equiv (Equiv.subRight s) _ _ (fun t => by
    simp only [Equiv.subRight_apply, sub_add_cancel, ← sub_eq_add_neg]
    ring)

/-- (L3) gives `R(s) = 0` for every `s ≠ m`. -/
theorem H9_R_zero {n : ℕ} [NeZero n] (hn : Even n) {K : Type*} [CommRing K] (y : ZMod n → K) (h3 : L3 0 y)
    (s : ZMod n) (hs : s ≠ half n) : R y s = 0 := by
  have hR : ∀ s : ZMod n, s.val < n / 2 → R y s = 0 := by
    intro s hs
    rw [← h3 s hs]
    unfold R
    simp only [add_comm s]
  by_cases h : s.val < n / 2
  · exact hR s h
  · have hne : s.val ≠ n / 2 := by
      intro he; apply hs; rw [← ZMod.natCast_zmod_val s, he]; rfl
    have hlt := ZMod.val_lt s
    have h2 : n % 2 = 0 := Nat.even_iff.mp hn
    have hneg := H9_R_neg y (-s)
    rw [neg_neg] at hneg
    rw [hneg]
    apply hR
    rw [ZMod.neg_val', Nat.mod_eq_of_lt (by omega)]
    omega

/-- Any (L2)-type identity `y_s y_{s+m} = c` (for `s < m`) holds for every `s`. -/
theorem H9_L2_all {n : ℕ} [NeZero n] (hn : Even n) {K : Type*} [CommRing K] {c : K} (y : ZMod n → K)
    (h2 : L2 c y) (t : ZMod n) : y t * y (t + half n) = c := by
  by_cases ht : t.val < n / 2
  · exact h2 t ht
  · have h := h2 (t + half n) (H9_add_half_val_lt hn t ht)
    rw [add_assoc, H9_two_half hn, add_zero] at h
    rw [mul_comm]; exact h

/-! ## 5. Row 6 — Remark 2.6 -/

/-- Row 6 — Remark 2.6, with hypothesis `hF4` = the exact instance `prop_2_4_F4 n _ h3 ω hω y`. -/
theorem rem_2_6_of (n : ℕ) [NeZero n] (h4 : 4 ∣ n) (_h3 : ¬ 3 ∣ n) {L : Type*} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2))
    (hy : y ∈ NFSet n 2) (hF4 : L4 y ↔ F4 (dftA ω y)) :
    let yp : ZMod n → GaloisField 3 (n / 2) := fun t => yPlus n (y t)
    let ym : ZMod n → GaloisField 3 (n / 2) := fun t => yMinus n (y t)
    (∀ t, yp (t + half n) = yp t ∧ bar n (yp t) = yp t ∧ bar n (ym t) = -ym t ∧ ym (t + half n) = -ym t) ∧
      (∀ s, ∑ t, yp t * ym (t + s) = 0 ∧ ∑ t, sgn t * yp t * ym (2 * s - t) = 0) ∧
      (∀ s, s ≠ 0 → s ≠ half n → R yp s = 0 ∧ R ym s = 0) ∧
      (∀ k : ZMod n, Odd k.val → dftA ω yp k = 0) ∧ (∀ k : ZMod n, Even k.val → dftA ω ym k = 0) ∧
      (∀ k : ZMod n, Even k.val → dftA ω y k = dftA ω yp k) ∧ (∀ k : ZMod n, Odd k.val → dftA ω y k = dftA ω ym k) ∧
      (∀ k : ZMod n, Even k.val →
        dftA ω yp k * dftA ω yp (k + half n) = algebraMap _ L (S y) * dftA ω yp (2 * k)) ∧
      (∀ k : ZMod n, Odd k.val →
        dftA ω ym k * dftA ω ym (k + half n) = algebraMap _ L (S y) * dftA ω yp (2 * k)) ∧
      (∀ s : ZMod n, S y * (y s + y (s + half n)) = 2 * S y * yp s) ∧
      (L2 (-1) y ↔ ∀ t, yp t ^ 2 - ym t ^ 2 = -1) := by
  intro yp ym
  obtain ⟨h1, hL3, _, hL4⟩ := hy
  have hn : Even n := by obtain ⟨c, hc⟩ := h4; exact ⟨2 * c, by omega⟩
  have hm : Even (n / 2) := by obtain ⟨c, hc⟩ := h4; exact ⟨c, by omega⟩
  have h2F := H9_two_ne_zero_GF (n / 2)
  have h2L : (2 : L) ≠ 0 := H9_two_ne_zero_L (m := n / 2)
  have hbar : ∀ t, y (t + half n) = bar n (y t) := H9_shift_half h4 h1
  have hyp : ∀ t, yp (t + half n) = yp t := fun t => by
    show yPlus n (y (t + half n)) = yPlus n (y t)
    rw [hbar, H9_yPlus_bar n h4]
  have hym : ∀ t, ym (t + half n) = -ym t := fun t => by
    show yMinus n (y (t + half n)) = -yMinus n (y t)
    rw [hbar, H9_yMinus_bar n h4]
  have hsplit : ∀ t, y t = yp t + ym t := fun t => (H9_split n (y t)).symm
  -- cross terms
  have hcross1 : ∀ s, ∑ t, yp t * ym (t + s) = 0 := fun s =>
    H9_sum_antiperiodic h2F _ (half n) (fun t => by
      show yp (t + half n) * ym (t + half n + s) = -(yp t * ym (t + s))
      rw [hyp, add_right_comm, hym]
      ring)
  have hcross2 : ∀ s, ∑ t, sgn t * yp t * ym (2 * s - t) = 0 := fun s =>
    H9_sum_antiperiodic h2F _ (half n) (fun t => by
      show sgn (t + half n) * yp (t + half n) * ym (2 * s - (t + half n)) = -(sgn t * yp t * ym (2 * s - t))
      rw [H9_sgn_add_half hn hm, hyp,
        show 2 * s - (t + half n) = 2 * s - t + half n by linear_combination (-1 : ZMod n) * H9_two_half hn, hym]
      ring)
  have hcross3 : ∀ s, ∑ t, ym t * yp (t + s) = 0 := fun s =>
    H9_sum_antiperiodic h2F _ (half n) (fun t => by
      show ym (t + half n) * yp (t + half n + s) = -(ym t * yp (t + s))
      rw [hym, add_right_comm, hyp]
      ring)
  -- autocorrelations
  have hRsplit : ∀ u, R y u = R yp u + R ym u := fun u => by
    unfold R
    have e : ∀ t, y t * y (t + u) =
        yp t * yp (t + u) + ym t * ym (t + u) + (yp t * ym (t + u) + ym t * yp (t + u)) := fun t => by
      rw [hsplit t, hsplit (t + u)]
      ring
    rw [Finset.sum_congr rfl (fun t _ => e t), Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, hcross1 u, hcross3 u]
    ring
  have hRp : ∀ s, R yp (s + half n) = R yp s := fun s => by
    unfold R
    exact Finset.sum_congr rfl (fun t _ => by rw [← add_assoc, hyp])
  have hRm : ∀ s, R ym (s + half n) = -R ym s := fun s => by
    unfold R
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun t _ => by rw [← add_assoc, hym]; ring)
  -- the transforms
  have hdp : ∀ k : ZMod n, Odd k.val → dftA ω yp k = 0 := fun k hk => by
    have e := H9_dft_shift hn hω (fun t => algebraMap _ L (yp t)) k
    simp only [hyp] at e
    rw [hk.neg_one_pow, neg_one_mul] at e
    exact H9_eq_zero_of_eq_neg h2L e
  have hdm : ∀ k : ZMod n, Even k.val → dftA ω ym k = 0 := fun k hk => by
    have e := H9_dft_shift hn hω (fun t => algebraMap _ L (ym t)) k
    simp only [hym, map_neg] at e
    rw [H9_dft_neg, hk.neg_one_pow, one_mul] at e
    exact H9_eq_zero_of_eq_neg h2L e
  have hdsplit : ∀ k, dftA ω y k = dftA ω yp k + dftA ω ym k := fun k =>
    (congrArg (fun z => dftA ω z k) (funext hsplit)).trans (H9_dftA_add ω yp ym k)
  have hdE : ∀ k : ZMod n, Even k.val → dftA ω y k = dftA ω yp k := fun k hk => by
    rw [hdsplit, hdm k hk, add_zero]
  have hdO : ∀ k : ZMod n, Odd k.val → dftA ω y k = dftA ω ym k := fun k hk => by
    rw [hdsplit, hdp k hk, zero_add]
  have hF4' := hF4.mp hL4
  have hS := H9_dftA_half hn hω y
  refine ⟨fun t => ⟨hyp t, H9_bar_yPlus n h4 (y t), H9_bar_yMinus n h4 (y t), hym t⟩,
    fun s => ⟨hcross1 s, hcross2 s⟩, fun s hs0 hsh => ?_, hdp, hdm, hdE, hdO, fun k hk => ?_, fun k hk => ?_,
    fun s => ?_, ?_⟩
  · -- (L3) splits
    have e1 : R yp s + R ym s = 0 := by rw [← hRsplit s]; exact H9_R_zero hn y hL3 s hsh
    have hsh' : s + half n ≠ half n := by
      intro h; apply hs0; linear_combination h
    have e2 : R yp s - R ym s = 0 := by
      rw [← hRp, sub_eq_add_neg, ← hRm, ← hRsplit]
      exact H9_R_zero hn y hL3 _ hsh'
    have hA : R yp s = 0 := by
      have h2A : (2 : GaloisField 3 (n / 2)) * R yp s = 0 := by linear_combination e1 + e2
      exact (mul_eq_zero.mp h2A).resolve_left h2F
    exact ⟨hA, by linear_combination e1 - hA⟩
  · -- (L4) on μ_m
    have hk2 : Even (k + half n).val := (H9_even_add_half hn hm k).mpr hk
    rw [← hdE k hk, ← hdE _ hk2, ← hdE _ (H9_even_two_mul hn k), ← hS]
    exact hF4' k
  · -- (L4) on the top layer
    have hk2 : Odd (k + half n).val := (H9_odd_add_half hn hm k).mpr hk
    rw [← hdO k hk, ← hdO _ hk2, ← hdE _ (H9_even_two_mul hn k), ← hS]
    exact hF4' k
  · -- right side of (L4)
    show S y * (y s + y (s + half n)) = 2 * S y * yPlus n (y s)
    rw [hbar]
    linear_combination (-(S y)) * H9_two_yPlus n (y s)
  · -- (L2)
    have hsq : ∀ t, yp t ^ 2 - ym t ^ 2 = y t * y (t + half n) := fun t => by
      rw [hbar]; exact H9_sq_diff n (y t)
    constructor
    · intro hL2 t
      rw [hsq]
      exact H9_L2_all hn y hL2 t
    · intro h s _
      rw [← hsq]
      exact h s

/-! ## 6. The descent (Theorem 4.1, Step 3) -/

/-- The descent along the layers, from `h(2k) = s h(k) h(k + m)` alone: for `d ≤ a - 1` and odd `η`,
`h(2^d η) = s^{2^d - 1} ∏_{ρ odd, 2^d ρ = 2^d η} h(ρ)`. -/
theorem H9_descent_core {n a nodd : ℕ} [NeZero n] (hn : n = 2 ^ a * nodd) {M : Type*}
    [CommRing M] (h : ZMod n → M) (s : M)
    (hF : ∀ k : ZMod n, h (2 * k) = s * h k * h (k + half n)) :
    ∀ d : ℕ, d + 1 ≤ a → ∀ η : ZMod n, Odd η.val →
      h ((2 : ZMod n) ^ d * η) = s ^ (2 ^ d - 1) *
        ∏ ρ ∈ (topLayer n).filter (fun ρ => (2 : ZMod n) ^ d * ρ = (2 : ZMod n) ^ d * η), h ρ := by
  intro d
  induction d with
  | zero =>
    intro _ η hη
    have hmem : η ∈ topLayer n := by
      simp only [topLayer, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hη
    simp only [pow_zero, one_mul, Nat.sub_self]
    rw [Finset.filter_eq' (topLayer n) η]
    simp only [hmem, ↓reduceIte, Finset.prod_singleton]
  | succ d ih =>
    intro hd η hη
    obtain ⟨r, hr⟩ : ∃ r, a = d + 2 + r := ⟨a - d - 2, by omega⟩
    have hev : Even n := ⟨2 ^ (d + 1 + r) * nodd, by rw [hn, hr]; ring⟩
    set c : ZMod n := ((2 ^ (r + 1) * nodd : ℕ) : ZMod n) with hc
    have hcd : (2 : ZMod n) ^ d * c = half n := by
      have e : n / 2 = 2 ^ d * (2 ^ (r + 1) * nodd) := by
        rw [hn, hr, show 2 ^ (d + 2 + r) * nodd = 2 * (2 ^ d * (2 ^ (r + 1) * nodd)) by ring]
        exact Nat.mul_div_cancel_left _ (by norm_num)
      rw [hc]
      unfold half
      rw [e]
      push_cast
      ring
    have hce : Even c.val :=
      (H9_even_natCast_val hev _).mpr ((Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_right nodd)
    have hηc : Odd (η + c).val := by
      rw [← Nat.not_even_iff_odd, H9_even_val_add hev, Nat.even_add]
      intro hh
      exact (Nat.not_even_iff_odd.mpr hη) (hh.mpr hce)
    have hsh : (2 : ZMod n) ^ d * η + half n = (2 : ZMod n) ^ d * (η + c) := by rw [mul_add, hcd]
    have hd' : d + 1 ≤ a := by omega
    have ih1 := ih hd' η hη
    have ih2 := ih hd' (η + c) hηc
    rw [← hsh] at ih2
    have hfilt : (topLayer n).filter (fun ρ => (2 : ZMod n) ^ (d + 1) * ρ = (2 : ZMod n) ^ (d + 1) * η) =
        (topLayer n).filter (fun ρ => 2 * ((2 : ZMod n) ^ d * ρ) = 2 * ((2 : ZMod n) ^ d * η)) :=
      Finset.filter_congr (fun ρ _ => by rw [pow_succ', mul_assoc, mul_assoc])
    have hprod := H9_prod_split hev (topLayer n) (fun ρ => (2 : ZMod n) ^ d * ρ) h ((2 : ZMod n) ^ d * η)
    have hstep : (2 : ZMod n) ^ (d + 1) * η = 2 * ((2 : ZMod n) ^ d * η) := by ring
    rw [hfilt, hprod, hstep, hF, ih1, ih2]
    have hexp : 2 ^ (d + 1) - 1 = 1 + (2 ^ d - 1) + (2 ^ d - 1) := by
      have := Nat.one_le_two_pow (n := d)
      rw [pow_succ]
      omega
    rw [hexp, pow_add, pow_add, pow_one]
    ring

/-- Common facts for rows 14d, 14f: `h(2k) = S h(k) h(k + m)` and `S^2 = 1`. -/
theorem H9_F4_form {n : ℕ} [NeZero n] {M : Type*} [Field M] (h : ZMod n → M) (s : M) (hs2 : s * s = 1)
    (hS : h (half n) = s) (hF4 : F4 h) : ∀ k : ZMod n, h (2 * k) = s * h k * h (k + half n) := fun k => by
  have e := hF4 k
  rw [hS] at e
  linear_combination (-s) * e - h (2 * k) * hs2

/-- Row 14d — Theorem 4.1, Step 3 (eq:descent), with hypotheses `hF3`, `hF4` = the exact instances
`prop_2_4_F3 n _ h3 ω hω y`, `prop_2_4_F4 n _ h3 ω hω y`. -/
theorem thm_4_1_descent_of (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (_hodd : Odd nodd)
    (_h3 : ¬ 3 ∣ n) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2)
    (hF3 : (L3 0 y ∧ R y (half n) = 1) ↔ F3 ω (dftA ω y)) (hF4 : L4 y ↔ F4 (dftA ω y)) :
    (∀ (j : ℕ) (k : ZMod n), 1 ≤ j → j ≤ a - 1 → k ≠ 0 → padicValNat 2 k.val = a - j →
      dftA ω y k = algebraMap _ L (S y) ^ (2 ^ (a - j) - 1) *
        ∏ ρ ∈ (topLayer n).filter (fun ρ => (2 ^ (a - j) : ZMod n) * ρ = k), dftA ω y ρ) ∧
    dftA ω y (half n) = algebraMap _ L (S y) := by
  obtain ⟨_, hL3, hR, hL4⟩ := hy
  obtain ⟨hev, hm⟩ := H9_even_halves hn (by omega)
  have hS := H9_dftA_half hev hω y
  have hs2 := H9_S_sq hev hm hω y (hF3.mp ⟨hL3, hR⟩)
  have hF := H9_F4_form (dftA ω y) _ hs2 hS (hF4.mp hL4)
  refine ⟨fun j k hj1 hja hk0 hv => ?_, hS⟩
  have hd1 : 1 ≤ a - j := by omega
  have hda : a - j + 1 ≤ a := by omega
  have hkv0 : k.val ≠ 0 := by rwa [Ne, ZMod.val_eq_zero]
  obtain ⟨u, hu⟩ : 2 ^ (a - j) ∣ k.val := by rw [← hv]; exact pow_padicValNat_dvd
  have hu_odd : Odd u := by
    rw [← Nat.not_even_iff_odd]
    rintro ⟨w, hw⟩
    apply pow_succ_padicValNat_not_dvd (p := 2) hkv0
    rw [hv, hu, hw, pow_succ]
    exact ⟨w, by ring⟩
  have hu_lt : u < n := by
    have hlt := ZMod.val_lt k
    have h1 : 1 ≤ 2 ^ (a - j) := Nat.one_le_two_pow
    calc u ≤ 2 ^ (a - j) * u := Nat.le_mul_of_pos_left u (by omega)
      _ = k.val := hu.symm
      _ < n := hlt
  have hηv : ((u : ℕ) : ZMod n).val = u := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hu_lt]
  have hk : (2 : ZMod n) ^ (a - j) * ((u : ℕ) : ZMod n) = k := by
    rw [← ZMod.natCast_zmod_val k, hu]
    push_cast
    ring
  have core := H9_descent_core hn (dftA ω y) _ hF (a - j) hda (u : ZMod n) (by rw [hηv]; exact hu_odd)
  rw [hk] at core
  exact core

/-! ## 7. Theorem 4.1, Step 4 (layer 0) -/

/-- Row 14f — Theorem 4.1, Step 4, with hypotheses `hF1`, `hF3`, `hF4` = the exact instances
`prop_2_4_F1 n _ h3 ω hω y`, `prop_2_4_F3 n _ h3 ω hω y`, `prop_2_4_F4 n _ h3 ω hω y`. -/
theorem thm_4_1_step4_of (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (_h3 : ¬ 3 ∣ n)
    {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2)
    (hF1 : L1 3 2 y ↔ F1 3 2 ω (dftA ω y)) (hF3 : (L3 0 y ∧ R y (half n) = 1) ↔ F3 ω (dftA ω y))
    (hF4 : L4 y ↔ F4 (dftA ω y)) :
    (∀ k : ZMod n, 2 ^ a ∣ k.val →
      algebraMap _ L (S y) * dftA ω y (k + half n) =
          ∏ ρ ∈ (topLayer n).filter (fun ρ => (2 ^ (a - 1) : ZMod n) * ρ = k + half n), dftA ω y ρ ∧
        dftA ω y (2 * k) = algebraMap _ L (S y) * dftA ω y (k + half n) * dftA ω y k) ∧
    algebraMap _ L (S y) * dftA ω y (half n) = 1 ∧ (dftA ω y 0 = 1 ∨ dftA ω y 0 = -1) ∧
    ∀ k ∈ layer0' n a,
      dftA ω y (3 * k) = (ω ^ k.val) ^ 6 * dftA ω y k ^ 3 ∧ dftA ω y k * dftA ω y (-k) = (ω ^ k.val) ^ (n / 2) ∧
      algebraMap _ L (S y) * dftA ω y (3 * k + half n) =
        (ω ^ k.val) ^ 6 * (algebraMap _ L (S y) * dftA ω y (k + half n)) ^ 3 ∧
      (algebraMap _ L (S y) * dftA ω y (k + half n)) * (algebraMap _ L (S y) * dftA ω y (-k + half n)) =
        (ω ^ k.val) ^ (n / 2) := by
  obtain ⟨hL1, hL3, hR, hL4⟩ := hy
  obtain ⟨hev, hm⟩ := H9_even_halves hn (by omega)
  have hS := H9_dftA_half hev hω y
  have hF3' := hF3.mp ⟨hL3, hR⟩
  have hs2 := H9_S_sq hev hm hω y hF3'
  have hF := H9_F4_form (dftA ω y) _ hs2 hS (hF4.mp hL4)
  have hF1' := hF1.mp hL1
  have hF1c : ∀ k : ZMod n, dftA ω y (3 * k) = (ω ^ k.val) ^ 6 * dftA ω y k ^ 3 := fun k => by
    have e := hF1' k
    have e6 : ((3 : ℕ) : ℤ) * 2 = ((6 : ℕ) : ℤ) := by norm_num
    rw [e6, zpow_natCast, Nat.cast_ofNat] at e
    exact e
  refine ⟨fun k hk => ⟨?_, by rw [hF k]; ring⟩, by rw [hS]; exact hs2, ?_,
    fun k _ => ⟨hF1c k, hF3' k, ?_, ?_⟩⟩
  · -- P(α) = S ŷ(-α) is the product over the top layer
    obtain ⟨w, hw⟩ := hk
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have hwlt : w < nodd := by
      have hlt := ZMod.val_lt k
      rw [hw, hn] at hlt
      exact Nat.lt_of_mul_lt_mul_left hlt
    have h8 : 8 ≤ 2 ^ (b + 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hη_lt : 2 * w + nodd < n := by
      rw [hn]
      nlinarith
    have hηv : ((2 * w + nodd : ℕ) : ZMod n).val = 2 * w + nodd := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hη_lt]
    have hηodd : Odd ((2 * w + nodd : ℕ) : ZMod n).val := by
      rw [hηv]; exact Even.add_odd (even_two_mul w) hodd
    have hkη : (2 : ZMod n) ^ b * ((2 * w + nodd : ℕ) : ZMod n) = k + half n := by
      have e : n / 2 = 2 ^ b * nodd := by
        rw [hn, show 2 ^ (b + 1) * nodd = 2 * (2 ^ b * nodd) by ring]
        exact Nat.mul_div_cancel_left _ (by norm_num)
      rw [← ZMod.natCast_zmod_val k, hw]
      unfold half
      rw [e]
      push_cast
      ring
    have core := H9_descent_core hn (dftA ω y) _ hF b (by omega) _ hηodd
    rw [hkη] at core
    rw [core, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel Nat.one_le_two_pow,
      H9_pow_two_pow hs2 (by omega : 1 ≤ b), one_mul]
  · -- f(1) = ±1
    have e := hF3' 0
    rw [neg_zero, ZMod.val_zero, pow_zero, one_pow] at e
    exact mul_self_eq_one_iff.mp e
  · -- P(α^3) = α^6 P(α)^3
    have e := hF1c (k + half n)
    rw [show 3 * (k + half n) = 3 * k + half n by linear_combination H9_two_half hev,
      H9_omega_add_half hev hω, Even.neg_pow ⟨3, rfl⟩] at e
    rw [e]
    linear_combination -((ω ^ k.val) ^ 6 * dftA ω y (k + half n) ^ 3 * algebraMap _ L (S y)) * hs2
  · -- P(α) P(α^{-1}) = α^m
    have e := hF3' (k + half n)
    rw [neg_add, H9_neg_half hev, H9_omega_add_half hev hω, Even.neg_pow hm] at e
    linear_combination (dftA ω y (k + half n) * dftA ω y (-k + half n)) * hs2 + e

/-! ## 8. Linking check: each extra hypothesis is exactly an instance of the Prop 2.4 rows' shape
(`P1`, `P3`, `P4` below copy the binders and types of prop_2_4_F1 / _F3 / _F4 verbatim). No new axioms. -/

/-- `4 ∣ n → Even n` (to feed `hn : Even n` of the Prop 2.4 rows from row 6's binders). -/
theorem H9_even_of_four_dvd {n : ℕ} (h4 : 4 ∣ n) : Even n := by
  obtain ⟨c, hc⟩ := h4
  exact ⟨2 * c, by omega⟩

universe uL

example (n : ℕ) [NeZero n] (h4 : 4 ∣ n) (h3 : ¬ 3 ∣ n) {L : Type uL} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2))
    (hy : y ∈ NFSet n 2)
    (P4 : ∀ (n : ℕ) [NeZero n] (_hn : Even n) (_h3 : ¬ 3 ∣ n) {L : Type uL} [Field L]
      [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (_hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2)),
      L4 y ↔ F4 (dftA ω y)) : True := by
  have := rem_2_6_of n h4 h3 ω hω y hy (P4 n (H9_even_of_four_dvd h4) h3 ω hω y)
  trivial

example (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n) {L : Type uL} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2)
    (P1 : ∀ (n : ℕ) [NeZero n] (_hn : Even n) (_h3 : ¬ 3 ∣ n) {L : Type uL} [Field L]
      [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (_hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2)),
      L1 3 2 y ↔ F1 3 2 ω (dftA ω y))
    (P3 : ∀ (n : ℕ) [NeZero n] (_hn : Even n) (_h3 : ¬ 3 ∣ n) {L : Type uL} [Field L]
      [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (_hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2)),
      (L3 0 y ∧ R y (half n) = 1) ↔ F3 ω (dftA ω y))
    (P4 : ∀ (n : ℕ) [NeZero n] (_hn : Even n) (_h3 : ¬ 3 ∣ n) {L : Type uL} [Field L]
      [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (_hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2)),
      L4 y ↔ F4 (dftA ω y)) : True := by
  have hev : Even n := (H9_even_halves hn (by omega)).1
  have := thm_4_1_descent_of n a nodd hn ha hodd h3 ω hω y hy (P3 n hev h3 ω hω y) (P4 n hev h3 ω hω y)
  have := thm_4_1_step4_of n a nodd hn ha hodd h3 ω hω y hy (P1 n hev h3 ω hω y) (P3 n hev h3 ω hω y)
    (P4 n hev h3 ω hω y)
  trivial

#print axioms rem_2_6_of
#print axioms thm_4_1_descent_of
#print axioms thm_4_1_step4_of

end Xia.Proofs
