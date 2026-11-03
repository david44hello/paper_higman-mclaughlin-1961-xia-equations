/- Xia/Proofs/Sec22.lean — proofs of the rows sec_2_2_frobenius, sec_2_2_L2_iff, sec_2_2_R, sec_2_2_xia_eq, xia_sub_nf, intro_zero and 1 more of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry

namespace Xia.Proofs

open Xia Finset

/-! ## Generic helpers (any `n ≠ 0`, any commutative ring) -/

/-- Powers of an `x` with `x^n = 1` along `ZMod n` are additive in the exponent. -/
theorem H2_pow_val_add {n : ℕ} [NeZero n] {M : Type*} [Monoid M] (x : M) (hx : x ^ n = 1)
    (a b : ZMod n) : x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hx, pow_add]

/-- `(n/2 : ZMod n).val = n/2`. -/
theorem H2_half_val {n : ℕ} [NeZero n] : (half n : ZMod n).val = n / 2 := by
  unfold half
  rw [ZMod.val_natCast]
  have := NeZero.pos n
  exact Nat.mod_eq_of_lt (by omega)

/-- For even `n`: `m + m = 0` in `ZMod n`. -/
theorem H2_two_half {n : ℕ} [NeZero n] (hn : Even n) : half n + half n = (0 : ZMod n) := by
  unfold half
  rw [← Nat.cast_add]
  have h2 : n % 2 = 0 := Nat.even_iff.mp hn
  have : n / 2 + n / 2 = n := by omega
  rw [this, ZMod.natCast_self]

/-- For even `n`: if `t.val ≥ m` then `(t + m).val < m`. -/
theorem H2_add_half_val_lt {n : ℕ} [NeZero n] (hn : Even n) (t : ZMod n) (ht : ¬ t.val < n / 2) :
    (t + half n).val < n / 2 := by
  rw [ZMod.val_add, H2_half_val]
  have hlt := ZMod.val_lt t
  have h2 : n % 2 = 0 := Nat.even_iff.mp hn
  rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- A shift of the summation variable. -/
theorem H2_sum_shift {n : ℕ} [NeZero n] {M : Type*} [AddCommMonoid M] (f : ZMod n → M) (c : ZMod n) :
    ∑ t, f (t + c) = ∑ t, f t :=
  Fintype.sum_equiv (Equiv.addRight c) _ _ (fun _ => rfl)

/-- For even `n` (and `1.val = 1`): `(-1)^{(t).val} = -(-1)^{(t+1).val}`. -/
theorem H2_sgn_succ {n : ℕ} [NeZero n] (hn : Even n) (h1 : (1 : ZMod n).val = 1) {K : Type*} [CommRing K]
    (t : ZMod n) : (sgn t : K) = -(sgn (t + 1) : K) := by
  have hx : (-1 : K) ^ n = 1 := hn.neg_one_pow
  have h := H2_pow_val_add (-1 : K) hx t 1
  rw [h1, pow_one] at h
  unfold sgn
  rw [h]
  ring

/-! ## Section 2.2: consequences of (L1) with `σ = 2` -/

/-- (L1) with `σ = 2` iterated: `y_{t+2j} = y_t^{3^j}`. -/
theorem H2_iter {n : ℕ} [NeZero n] {K : Type*} [CommRing K] {y : ZMod n → K} (h1 : L1 3 2 y)
    (t : ZMod n) (j : ℕ) : y (t + ((2 * j : ℕ) : ZMod n)) = y t ^ (3 ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := h1 (t + ((2 * j : ℕ) : ZMod n))
    have e : t + ((2 * (j + 1) : ℕ) : ZMod n) = t + ((2 * j : ℕ) : ZMod n) + ((2 : ℤ) : ZMod n) := by
      push_cast; ring
    rw [e, h, ih, ← pow_mul, ← pow_succ]

/-- For `n ≡ 8 (mod 24)`: `y_{t+m} = y_t^{3^{n/4}}`. -/
theorem H2_shift_half {n : ℕ} [NeZero n] (hn : n % 24 = 8) {K : Type*} [CommRing K] {y : ZMod n → K}
    (h1 : L1 3 2 y) (t : ZMod n) : y (t + half n) = y t ^ (3 ^ (n / 4)) := by
  have e : half n = ((2 * (n / 4) : ℕ) : ZMod n) := by
    unfold half; congr 1; omega
  rw [e, H2_iter h1 t]

/-- Row 3a. -/
theorem sec_2_2_frobenius_proved (n : ℕ) [NeZero n] (hn : n % 24 = 8) (y : ZMod n → GaloisField 3 (n / 2))
    (h1 : L1 3 2 y) :
    (∀ k : ℕ, y ((2 * k : ℕ) : ZMod n) = y 0 ^ (3 ^ k) ∧ y ((2 * k + 1 : ℕ) : ZMod n) = y 1 ^ (3 ^ k)) ∧
      ∀ t : ZMod n, y (t + half n) = bar n (y t) := by
  refine ⟨fun k => ⟨?_, ?_⟩, fun t => ?_⟩
  · have h := H2_iter h1 0 k
    rwa [zero_add] at h
  · have h := H2_iter h1 1 k
    have e : ((2 * k + 1 : ℕ) : ZMod n) = 1 + ((2 * k : ℕ) : ZMod n) := by push_cast; ring
    rw [e]; exact h
  · rw [H2_shift_half hn h1 t]
    rfl

/-- `N(x^{3^k}) = N(x)^{3^k}`. -/
theorem H2_nm_pow {K : Type*} [Monoid K] (n k : ℕ) (x : K) : Nm n (x ^ (3 ^ k)) = Nm n x ^ (3 ^ k) := by
  unfold Nm
  rw [← pow_mul, ← pow_mul, mul_comm]

/-- `y_s y_{s+m} = N(y_s)` under (L1) with `σ = 2`, `n ≡ 8 (mod 24)`. -/
theorem H2_nm_eq {n : ℕ} [NeZero n] (hn : n % 24 = 8) {K : Type*} [CommRing K] {y : ZMod n → K}
    (h1 : L1 3 2 y) (s : ZMod n) : y s * y (s + half n) = Nm n (y s) := by
  rw [H2_shift_half hn h1 s]
  unfold Nm
  rw [pow_add, pow_one]

/-- `N(x) = -1 → N(x^{3^k}) = -1`. -/
theorem H2_nm_pow_neg_one {K : Type*} [CommRing K] (n k : ℕ) (x : K) (hx : Nm n x = -1) :
    Nm n (x ^ (3 ^ k)) = -1 := by
  rw [H2_nm_pow, hx]
  exact Odd.neg_one_pow (Odd.pow (by decide))

/-- Row 3b. -/
theorem sec_2_2_L2_iff_proved (n : ℕ) [NeZero n] (hn : n % 24 = 8) (y : ZMod n → GaloisField 3 (n / 2))
    (h1 : L1 3 2 y) :
    L2 (-1) y ↔ Nm n (y 0) = -1 ∧ Nm n (y 1) = -1 := by
  have hnm := H2_nm_eq hn h1
  have h1v : (1 : ZMod n).val = 1 := ZMod.val_one'' (by omega)
  have hfr := (sec_2_2_frobenius_proved n hn y h1).1
  constructor
  · intro hL2
    refine ⟨?_, ?_⟩
    · rw [← hnm 0]; exact hL2 0 (by rw [ZMod.val_zero]; omega)
    · rw [← hnm 1]; exact hL2 1 (by rw [h1v]; omega)
  · rintro ⟨h0, h1'⟩ s _
    rw [hnm s]
    obtain ⟨k, hk | hk⟩ : ∃ k, s.val = 2 * k ∨ s.val = 2 * k + 1 := ⟨s.val / 2, by omega⟩
    · have hs : s = ((2 * k : ℕ) : ZMod n) := by rw [← hk, ZMod.natCast_zmod_val]
      rw [hs, (hfr k).1]
      exact H2_nm_pow_neg_one n k _ h0
    · have hs : s = ((2 * k + 1 : ℕ) : ZMod n) := by rw [← hk, ZMod.natCast_zmod_val]
      rw [hs, (hfr k).2]
      exact H2_nm_pow_neg_one n k _ h1'

/-! ## The autocorrelation `R` (any even `n`, any commutative ring) -/

/-- `R(-s) = R(s)`. -/
theorem H2_R_neg {n : ℕ} [NeZero n] {K : Type*} [CommRing K] (y : ZMod n → K) (s : ZMod n) :
    R y (-s) = R y s := by
  unfold R
  exact Fintype.sum_equiv (Equiv.subRight s) _ _ (fun t => by
    simp only [Equiv.subRight_apply, sub_add_cancel, ← sub_eq_add_neg]
    ring)

/-- (L3) gives `R(s) = 0` for every `s ≠ m`. -/
theorem H2_R_zero {n : ℕ} [NeZero n] (hn : Even n) {K : Type*} [CommRing K] (y : ZMod n → K) (h3 : L3 0 y)
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
    have hneg := H2_R_neg y (-s)
    rw [neg_neg] at hneg
    rw [hneg]
    apply hR
    rw [ZMod.neg_val', Nat.mod_eq_of_lt (by omega)]
    omega

/-- Any (L2)-type identity `y_s y_{s+m} = c` (for `s < m`) holds for every `s`. -/
theorem H2_L2_all {n : ℕ} [NeZero n] (hn : Even n) {K : Type*} [CommRing K] {c : K} (y : ZMod n → K)
    (h2 : L2 c y) (t : ZMod n) : y t * y (t + half n) = c := by
  by_cases ht : t.val < n / 2
  · exact h2 t ht
  · have h := h2 (t + half n) (H2_add_half_val_lt hn t ht)
    rw [add_assoc, H2_two_half hn, add_zero] at h
    rw [mul_comm]; exact h

/-- (L2) with constant `c` gives `R(m) = n c`. -/
theorem H2_R_half {n : ℕ} [NeZero n] (hn : Even n) {K : Type*} [CommRing K] {c : K} (y : ZMod n → K)
    (h2 : L2 c y) : R y (half n) = n * c := by
  unfold R
  rw [Finset.sum_congr rfl (fun t _ => H2_L2_all hn y h2 t)]
  simp [Finset.sum_const, Finset.card_univ, ZMod.card]

/-- Row 3c. -/
theorem sec_2_2_R_proved (n : ℕ) [NeZero n] (hn : Even n) {K : Type*} [CommRing K] (y : ZMod n → K) :
    (∀ s, R y (-s) = R y s) ∧ (L3 0 y → ∀ s, s ≠ half n → R y s = 0) ∧
      (L2 (-1) y → R y (half n) = -(n : K)) := by
  refine ⟨H2_R_neg y, fun h3 s hs => H2_R_zero hn y h3 s hs, fun h2 => ?_⟩
  rw [H2_R_half hn y h2]
  ring

/-! ## Xia's system ⊂ norm-free system (characteristic 3, `n ≡ 8 (mod 24)`) -/

/-- `-n = 1` in characteristic 3 when `n ≡ 8 (mod 24)`. -/
theorem H2_neg_n_eq_one {n : ℕ} (hn : n % 24 = 8) {K : Type*} [CommRing K] [CharP K 3] : -(n : K) = 1 := by
  have h : ((n + 1 : ℕ) : K) = 0 := (CharP.cast_eq_zero_iff K 3 _).mpr (Nat.dvd_of_mod_eq_zero (by omega))
  push_cast at h
  linear_combination -h

/-- Every solution of Xia's system with shift `σ` solves the norm-free system with shift `σ`. -/
theorem H2_xia_to_nf {n : ℕ} [NeZero n] (hn : n % 24 = 8) {K : Type*} [CommRing K] [CharP K 3] (σ : ℤ)
    (y : ZMod n → K) (h : XiaEqs σ y) : NormFreeEqs σ y := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h3, ?_, h4⟩
  have hev : Even n := Nat.even_iff.mpr (by omega)
  rw [H2_R_half hev y h2, mul_neg_one, H2_neg_n_eq_one hn]

/-- Row 3d. -/
theorem sec_2_2_xia_eq_proved (n : ℕ) [NeZero n] (hn : n % 24 = 8) :
    XiaSet n 2 ⊆ NFSet n 2 ∧ XiaSet n 2 = {y | y ∈ NFSet n 2 ∧ Nm n (y 0) = -1 ∧ Nm n (y 1) = -1} := by
  have hsub : XiaSet n 2 ⊆ NFSet n 2 := fun y hy => H2_xia_to_nf hn _ y hy
  refine ⟨hsub, ?_⟩
  ext y
  constructor
  · intro hy
    exact ⟨hsub hy, (sec_2_2_L2_iff_proved n hn y hy.1).mp hy.2.1⟩
  · rintro ⟨hy, hN⟩
    obtain ⟨h1, h3, _, h4⟩ := hy
    exact ⟨h1, (sec_2_2_L2_iff_proved n hn y h1).mpr hN, h3, h4⟩

/-- Row 27. -/
theorem xia_sub_nf_proved (n : ℕ) [NeZero n] (hn : n % 24 = 8) (σ : ℕ) (_hσ : σ ∣ n) :
    XiaSet n σ ⊆ NFSet n σ := by
  intro y hy
  exact H2_xia_to_nf hn _ y hy

/-- Coverage `intro_zero`. -/
theorem intro_zero_proved (n σ : ℕ) [NeZero n] :
    (L1 3 (σ : ℤ) (0 : ZMod n → GaloisField 3 (n / σ)) ∧ L3 0 (0 : ZMod n → GaloisField 3 (n / σ)) ∧
      L4 (0 : ZMod n → GaloisField 3 (n / σ))) ∧ R (0 : ZMod n → GaloisField 3 (n / σ)) (half n) ≠ 1 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro s; simp
  · intro s _; simp
  · intro s _; simp
  · simp [R]

/-! ## Remark 3.3 (translation `y_t ↦ y_{t+1}`) -/

/-- For even `n`, (L4) at `s < m` gives (L4) at every `s` (both sides depend on `s` only modulo `m`). -/
theorem H2_L4_all {n : ℕ} [NeZero n] (hn : Even n) {K : Type*} [CommRing K] {y : ZMod n → K} (h4 : L4 y)
    (s : ZMod n) : ∑ t, sgn t * y t * y (2 * s - t) = (y s + y (s + half n)) * S y := by
  by_cases hs : s.val < n / 2
  · exact h4 s hs
  · have h := h4 (s + half n) (H2_add_half_val_lt hn s hs)
    have e1 : 2 * (s + half n) = 2 * s := by
      rw [mul_add, two_mul (half n), H2_two_half hn, add_zero]
    have e2 : s + half n + half n = s := by rw [add_assoc, H2_two_half hn, add_zero]
    rw [e1, e2, add_comm (y (s + half n))] at h
    exact h

/-- `S` of the translate is `-S`. -/
theorem H2_S_trans {n : ℕ} [NeZero n] (hn : Even n) (h1v : (1 : ZMod n).val = 1) {K : Type*} [CommRing K]
    (y : ZMod n → K) : S (yTrans 1 y) = -S y := by
  unfold S
  rw [← Finset.sum_neg_distrib]
  exact Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun t => by
    simp only [yTrans, Equiv.coe_addRight]
    rw [H2_sgn_succ hn h1v (K := K) t]
    ring)

/-- Row 9. -/
theorem rem_3_3_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2) :
    yTrans 1 y ∈ NFSet n 2 ∧ paramMap n ξ0 (yTrans 1 y) = (ξ0⁻¹ * dft ξ0 y 1, -S y, dft ξ0 y 0) ∧
      yTrans 1 y 0 = y 1 := by
  have h8 : 8 ≤ n := by
    rw [hne]
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hev : Even n := by
    rw [hne]; exact even_two.pow_of_ne_zero (by omega)
  have h1v : (1 : ZMod n).val = 1 := ZMod.val_one'' (by omega)
  have hξne : ξ0 ≠ 0 := hξ0.ne_zero (by omega)
  obtain ⟨h1, h3, hR, h4⟩ := hy
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- (L1)
    intro s
    simp only [yTrans]
    rw [← h1 (s + 1), add_right_comm]
  · -- (L3)
    intro s hs
    refine (Fintype.sum_equiv (Equiv.addRight 1) _ (fun t => y t * y (s + t)) (fun t => ?_)).trans (h3 s hs)
    simp only [yTrans, Equiv.coe_addRight, add_assoc]
  · -- R(m) = 1
    unfold R at hR ⊢
    refine (Fintype.sum_equiv (Equiv.addRight 1) _ (fun t => y t * y (t + half n)) (fun t => ?_)).trans hR
    simp only [yTrans, Equiv.coe_addRight]
    rw [add_right_comm t (half n) 1]
  · -- (L4)
    intro s _
    rw [H2_S_trans hev h1v y]
    have hA : ∑ t, sgn t * yTrans 1 y t * yTrans 1 y (2 * s - t) =
        ∑ u, -(sgn u * y u * y (2 * (s + 1) - u)) :=
      Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun t => by
        simp only [yTrans, Equiv.coe_addRight]
        rw [H2_sgn_succ hev h1v (K := GaloisField 3 (n / 2)) t,
          show 2 * s - t + 1 = 2 * (s + 1) - (t + 1) by ring]
        ring)
    rw [hA, Finset.sum_neg_distrib, H2_L4_all hev h4 (s + 1)]
    simp only [yTrans]
    rw [add_right_comm s (half n) 1]
    ring
  · -- the parameters
    simp only [paramMap, Prod.mk.injEq]
    refine ⟨?_, H2_S_trans hev h1v y, ?_⟩
    · unfold dft
      rw [h1v, pow_one, Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun t => ?_)
      simp only [yTrans, Equiv.coe_addRight]
      rw [H2_pow_val_add ξ0 hξ0.pow_eq_one t 1, h1v, pow_one,
        show ξ0⁻¹ * (y (t + 1) * (ξ0 ^ t.val * ξ0)) = y (t + 1) * ξ0 ^ t.val * (ξ0 * ξ0⁻¹) by ring,
        mul_inv_cancel₀ hξne, mul_one]
    · unfold dft
      simp only [ZMod.val_zero, pow_zero, one_pow, mul_one]
      exact Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun t => rfl)
  · -- y_0 ↦ y_1
    simp [yTrans]

#print axioms sec_2_2_frobenius_proved
#print axioms sec_2_2_L2_iff_proved
#print axioms sec_2_2_R_proved
#print axioms sec_2_2_xia_eq_proved
#print axioms xia_sub_nf_proved
#print axioms intro_zero_proved
#print axioms rem_3_3_proved

end Xia.Proofs
