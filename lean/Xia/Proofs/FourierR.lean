/- Xia/Proofs/FourierR.lean — proofs of the rows sec_6_3_fourier of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import Xia.Defs.Symmetry
import Xia.Proofs.Thm31
import Xia.Proofs.Signs
import Xia.Proofs.Sec22
import Xia.Proofs.Coverage

namespace Xia.Proofs

open Xia Finset

set_option linter.unusedSectionVars false

/-! ## Part A — exponent model, orthogonality, DFT inversion (any field) -/

section DFTgen

variable {n : ℕ} [NeZero n] {K : Type*} [Field K]

/-- Integer powers in the exponent model: `(ω^k)^z = ω^{k z}`. -/
theorem H20_zpow_val {ω : K} (hω1 : ω ^ n = 1) (k : ZMod n) (z : ℤ) :
    (ω ^ k.val) ^ z = ω ^ ((k * (z : ZMod n)).val) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · rw [zpow_natCast, H4_pow_val_mul_nat hω1, Int.cast_natCast]
  · rw [zpow_neg, zpow_natCast, H4_pow_val_mul_nat hω1, Int.cast_neg, Int.cast_natCast, mul_neg,
      H4_pow_val_neg hω1]

/-- Orthogonality: `∑_{k ∈ ℤ/n} ω^{kj} = n` if `j = 0`, else `0`. -/
theorem H20_orth {ω : K} (hω : IsPrimitiveRoot ω n) (j : ZMod n) :
    ∑ k : ZMod n, ω ^ ((k * j).val) = if j = 0 then (n : K) else 0 := by
  have hω1 := hω.pow_eq_one
  split_ifs with hj
  · subst hj
    simp [ZMod.card]
  · have hζ : ω ^ j.val ≠ 1 := by
      intro h1
      rw [hω.pow_eq_one_iff_dvd] at h1
      exact hj ((ZMod.val_eq_zero j).mp (Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt j)))
    have hshift : ω ^ j.val * ∑ k : ZMod n, ω ^ ((k * j).val) = ∑ k : ZMod n, ω ^ ((k * j).val) := by
      rw [Finset.mul_sum]
      rw [← H2_sum_shift (fun k : ZMod n => ω ^ ((k * j).val)) 1]
      apply Finset.sum_congr rfl
      intro k _
      rw [← H4_pow_val_add hω1]
      congr 2
      ring
    have hprod : (ω ^ j.val - 1) * ∑ k : ZMod n, ω ^ ((k * j).val) = 0 := by
      linear_combination hshift
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hζ)

/-- DFT inversion: `∑_k ŷ(ω^k) ω^{-kv} = n y_v`. -/
theorem H20_dft_inv_sum {ω : K} (hω : IsPrimitiveRoot ω n) (f : ZMod n → K) (v : ZMod n) :
    ∑ k : ZMod n, dft ω f k * ω ^ ((k * (-v)).val) = (n : K) * f v := by
  have hω1 := hω.pow_eq_one
  unfold dft
  simp_rw [H4_pow_val_mul hω1, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm : ∀ t : ZMod n, ∑ k : ZMod n, f t * ω ^ ((k * t).val) * ω ^ ((k * -v).val) =
      f t * (if t - v = 0 then (n : K) else 0) := by
    intro t
    rw [← H20_orth hω (t - v), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hx : ω ^ ((k * t).val) * ω ^ ((k * -v).val) = ω ^ ((k * (t - v)).val) := by
      rw [← H4_pow_val_add hω1]; congr 2; ring
    linear_combination (f t) * hx
  rw [Finset.sum_congr rfl (fun t _ => hterm t)]
  simp_rw [sub_eq_zero, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  ring

/-- The DFT is injective when `n` is invertible. -/
theorem H20_dft_inj {ω : K} (hω : IsPrimitiveRoot ω n) (hnK : (n : K) ≠ 0) {f g : ZMod n → K}
    (h : dft ω f = dft ω g) : f = g := by
  funext v
  have h1 := H20_dft_inv_sum hω f v
  rw [h, H20_dft_inv_sum hω g v] at h1
  exact (mul_left_cancel₀ hnK h1).symm

/-- The inverse DFT `y_v = n^{-1} ∑_k h(k) ω^{-kv}`. -/
noncomputable def H20_idft (ω : K) (h : ZMod n → K) : ZMod n → K :=
  fun v => (n : K)⁻¹ * ∑ k : ZMod n, h k * ω ^ ((k * (-v)).val)

theorem H20_dft_idft {ω : K} (hω : IsPrimitiveRoot ω n) (hnK : (n : K) ≠ 0) (h : ZMod n → K) :
    dft ω (H20_idft ω h) = h := by
  have hω1 := hω.pow_eq_one
  funext j
  unfold dft H20_idft
  simp_rw [H4_pow_val_mul hω1, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm : ∀ k : ZMod n, ∑ t : ZMod n, (n : K)⁻¹ * (h k * ω ^ ((k * -t).val)) * ω ^ ((j * t).val) =
      (n : K)⁻¹ * h k * (if j - k = 0 then (n : K) else 0) := by
    intro k
    rw [← H20_orth hω (j - k), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    have hx : ω ^ ((k * -t).val) * ω ^ ((j * t).val) = ω ^ ((t * (j - k)).val) := by
      rw [← H4_pow_val_add hω1]; congr 2; ring
    linear_combination ((n : K)⁻¹ * h k) * hx
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  simp_rw [sub_eq_zero, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  field_simp

/-- `ŷ(ω^j) = ∑_s f_s ω^{-(-j) s}` (the form produced by the correlation identity). -/
theorem H20_dft_eq_negsum {ω : K} (hω1 : ω ^ n = 1) (f : ZMod n → K) (j : ZMod n) :
    dft ω f j = ∑ s : ZMod n, f s * ω ^ ((-((-j) * s)).val) := by
  unfold dft
  apply Finset.sum_congr rfl
  intro s _
  rw [H4_pow_val_mul hω1, neg_mul, neg_neg]

end DFTgen

/-! ## Part B — (L1_r) ⇔ (F1_r) (any field of characteristic `r`) -/

section F1

variable {n : ℕ} [NeZero n] {K : Type*} [Field K]

/-- Frobenius on the DFT: `ξ^{rσ} ŷ(ξ)^r` is the DFT of `u ↦ y_{u-σ}^r` at `ξ^r`. -/
theorem H20_frob_dft (r : ℕ) [Fact r.Prime] [CharP K r] {ω : K} (hω1 : ω ^ n = 1) (σ : ℤ)
    (Y : ZMod n → K) (k : ZMod n) :
    (ω ^ k.val) ^ ((r : ℤ) * σ) * dft ω Y k ^ r =
      dft ω (fun u : ZMod n => Y (u - (σ : ZMod n)) ^ r) ((r : ZMod n) * k) := by
  unfold dft
  rw [sum_pow_char, Finset.mul_sum, H20_zpow_val hω1]
  rw [← H2_sum_shift (fun u : ZMod n => Y (u - σ) ^ r * (ω ^ (((r : ZMod n) * k).val)) ^ u.val) (σ : ZMod n)]
  apply Finset.sum_congr rfl
  intro t _
  simp only [add_sub_cancel_right]
  rw [mul_pow, H4_pow_val_mul hω1, H4_pow_val_mul hω1, H4_pow_val_mul_nat hω1]
  have hx : ω ^ ((k * (((r : ℤ) * σ : ℤ) : ZMod n)).val) * ω ^ ((k * t * (r : ZMod n)).val) =
      ω ^ (((r : ZMod n) * k * (t + σ)).val) := by
    rw [← H4_pow_val_add hω1]; congr 2; push_cast; ring
  linear_combination (Y t ^ r) * hx

/-- (L1_r) ⇔ (F1_r) for any shift `σ`. -/
theorem H20_L1_iff_F1 (r : ℕ) [Fact r.Prime] [CharP K r] {ω : K} (hω : IsPrimitiveRoot ω n)
    (hnK : (n : K) ≠ 0) (hrn : IsUnit (r : ZMod n)) (σ : ℤ) (Y : ZMod n → K) :
    L1 r σ Y ↔ F1 r σ ω (dft ω Y) := by
  have key : L1 r σ Y ↔ Y = fun u => Y (u - σ) ^ r := by
    constructor
    · intro h; funext u; rw [← h (u - σ), sub_add_cancel]
    · intro h s
      have := congrFun h (s + σ)
      simp only [add_sub_cancel_right] at this
      exact this
  rw [key]
  constructor
  · intro h k
    rw [H20_frob_dft r hω.pow_eq_one σ Y k]
    exact congrFun (congrArg (dft ω) h) _
  · intro hF
    apply H20_dft_inj hω hnK
    funext j
    obtain ⟨u, hu⟩ := hrn
    have hj : j = (r : ZMod n) * ((↑u⁻¹ : ZMod n) * j) := by
      rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]
    rw [hj, hF, H20_frob_dft r hω.pow_eq_one]

end F1

/-! ## Part C — (L3 c) ∧ R(m) = d ⇔ the correlation law; (F3_r) -/

section F3

variable {n : ℕ} [NeZero n] {K : Type*} [Field K]

/-- Correlation identity: `ŷ(ξ) ŷ(ξ^{-1}) = ∑_s R(s) ξ^{-s}`. -/
theorem H20_corr {ω : K} (hω1 : ω ^ n = 1) (Y : ZMod n → K) (k : ZMod n) :
    dft ω Y k * dft ω Y (-k) = ∑ s : ZMod n, R Y s * ω ^ ((-(k * s)).val) := by
  unfold dft
  simp_rw [H4_pow_val_mul hω1]
  rw [Finset.sum_mul_sum]
  have step : ∀ t : ZMod n, ∑ u, (Y t * ω ^ ((k * t).val)) * (Y u * ω ^ ((-k * u).val)) =
      ∑ s, Y t * Y (t + s) * ω ^ ((-(k * s)).val) := by
    intro t
    rw [← Equiv.sum_comp (Equiv.addLeft t)]
    apply Finset.sum_congr rfl
    intro s _
    simp only [Equiv.coe_addLeft]
    have hx : ω ^ ((k * t).val) * ω ^ ((-k * (t + s)).val) = ω ^ ((-(k * s)).val) := by
      rw [← H4_pow_val_add hω1]; congr 2; ring
    linear_combination (Y t * Y (t + s)) * hx
  rw [Finset.sum_congr rfl (fun t _ => step t), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [R, Finset.sum_mul]

/-- `R(-s) = R(s)`. -/
theorem H20_R_neg (Y : ZMod n → K) (s : ZMod n) : R Y (-s) = R Y s := by
  unfold R
  rw [← Equiv.sum_comp (Equiv.addRight s) (fun t => Y t * Y (t + -s))]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Equiv.coe_addRight, add_neg_cancel_right]
  ring

/-- (L3 c) and `R(m) = d` say exactly `R = c + (d - c) δ_m`. -/
theorem H20_R_iff (hn : Even n) (Y : ZMod n → K) (c d : K) :
    (L3 c Y ∧ R Y (half n) = d) ↔ ∀ s : ZMod n, R Y s = c + if s = half n then d - c else 0 := by
  have hRL : ∀ s : ZMod n, R Y s = ∑ t, Y t * Y (s + t) := by
    intro s; unfold R; apply Finset.sum_congr rfl; intro t _; rw [add_comm t s]
  constructor
  · rintro ⟨hL3, hRm⟩ s
    split_ifs with hs
    · rw [hs, hRm]; ring
    · rw [add_zero]
      rcases lt_trichotomy s.val (n / 2) with hlt | heq | hgt
      · rw [hRL]; exact hL3 s hlt
      · exfalso; apply hs; rw [← ZMod.natCast_zmod_val s, heq]; rfl
      · rw [← H20_R_neg, hRL]
        apply hL3
        have hs0 : s ≠ 0 := by intro h0; rw [h0, ZMod.val_zero] at hgt; omega
        rw [ZMod.neg_val, ite_eq_right hs0]
        have := ZMod.val_lt s
        obtain ⟨q, hq⟩ := hn; omega
  · intro hR
    refine ⟨fun s hs => ?_, ?_⟩
    · have hne : s ≠ half n := by
        intro h; rw [h, H4_half_val] at hs; omega
      rw [← hRL, hR s, ite_eq_right hne, add_zero]
    · rw [hR, ite_eq_left rfl]; ring

/-- The DFT side of `R = c + (d - c) δ_m`. -/
theorem H20_dft_Rstar {ω : K} (hω : IsPrimitiveRoot ω n) (hn : Even n) (c d : K) (k : ZMod n) :
    ∑ s : ZMod n, (c + if s = half n then d - c else 0) * ω ^ ((-(k * s)).val) =
      (if k = 0 then c * n else 0) + (d - c) * (ω ^ k.val) ^ (n / 2) := by
  simp_rw [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  have horth : ∑ s : ZMod n, c * ω ^ ((-(k * s)).val) = if k = 0 then c * n else 0 := by
    rw [← Finset.mul_sum]
    have : ∑ s : ZMod n, ω ^ ((-(k * s)).val) = ∑ s : ZMod n, ω ^ ((s * (-k)).val) := by
      apply Finset.sum_congr rfl; intro s _; rw [mul_neg, mul_comm]
    rw [this, H20_orth hω]
    by_cases hk : k = 0 <;> simp [hk]
  rw [horth]
  congr 1
  rw [H4_pow_val_mul_nat hω.pow_eq_one, ← mul_neg]
  have : -half n = ((n / 2 : ℕ) : ZMod n) := H4_neg_half hn
  rw [this]

/-- (L3 c) ∧ `R(m) = d` ⇔ `ŷ(ξ) ŷ(ξ^{-1}) = c n [ξ = 1] + (d - c) ξ^m` for every `ξ ∈ μ_n`. -/
theorem H20_L3R_iff {ω : K} (hω : IsPrimitiveRoot ω n) (hnK : (n : K) ≠ 0) (hn : Even n) (Y : ZMod n → K)
    (c d : K) :
    (L3 c Y ∧ R Y (half n) = d) ↔
      ∀ k : ZMod n, dft ω Y k * dft ω Y (-k) = (if k = 0 then c * n else 0) + (d - c) * (ω ^ k.val) ^ (n / 2) := by
  have hω1 := hω.pow_eq_one
  rw [H20_R_iff hn]
  simp_rw [H20_corr hω1, ← H20_dft_Rstar hω hn c d]
  constructor
  · intro h k
    apply Finset.sum_congr rfl; intro s _; rw [h s]
  · intro h
    have hfun : R Y = fun s => c + if s = half n then d - c else 0 := by
      apply H20_dft_inj hω hnK
      funext j
      rw [H20_dft_eq_negsum hω1, H20_dft_eq_negsum hω1]
      exact h (-j)
    intro s
    exact congrFun hfun s

/-- The law of the previous lemma is (F3_r) with `κ = d - c` once `c n + (d - c) = n^2`. -/
theorem H20_F3r_iff {ω : K} (h : ZMod n → K) (c d κ : K) (hκ : d - c = κ) (h0 : c * n + (d - c) = (n : K) ^ 2) :
    (∀ k : ZMod n, h k * h (-k) = (if k = 0 then c * n else 0) + (d - c) * (ω ^ k.val) ^ (n / 2)) ↔
      F3r κ ω h := by
  constructor
  · intro H
    refine ⟨fun k hk => ?_, ?_⟩
    · rw [H k, ite_eq_right hk, zero_add, hκ]
    · have := H 0
      rw [neg_zero, ite_eq_left rfl, ZMod.val_zero, pow_zero, one_pow, mul_one, h0] at this
      rw [sq, this]
  · rintro ⟨H1, H0⟩ k
    by_cases hk : k = 0
    · subst hk
      rw [neg_zero, ite_eq_left rfl, ZMod.val_zero, pow_zero, one_pow, mul_one, h0, ← sq, H0]
    · rw [ite_eq_right hk, H1 k hk, hκ, zero_add]

/-- The constants of the norm-free `r`-system: `n^4 - n(1-p) = n^2 p = κ` and `n(1-p) n + n^2 p = n^2`. -/
theorem H20_consts (n : ℕ) :
    (n : K) ^ 4 - (n : K) * (1 - (pp n : K)) = kappa n K ∧
      (n : K) * (1 - (pp n : K)) * n + ((n : K) ^ 4 - (n : K) * (1 - (pp n : K))) = (n : K) ^ 2 := by
  unfold kappa pp
  push_cast
  constructor <;> ring

/-- (L3_r) ∧ `R(m) = n^4` ⇔ (F3_r) with `κ = n^2 p`. -/
theorem H20_L3_iff_F3r {ω : K} (hω : IsPrimitiveRoot ω n) (hnK : (n : K) ≠ 0) (hn : Even n) (Y : ZMod n → K) :
    (L3 ((n : K) * (1 - (pp n : K))) Y ∧ R Y (half n) = (n : K) ^ 4) ↔ F3r (kappa n K) ω (dft ω Y) := by
  rw [H20_L3R_iff hω hnK hn Y]
  exact H20_F3r_iff _ _ _ _ (H20_consts n).1 (H20_consts n).2

end F3

/-! ## Part D — (L4) ⇔ (F4) (any field with `2 ≠ 0`) -/

section F4

variable {n : ℕ} [NeZero n] {K : Type*} [Field K]

/-- `C(v) = ∑_u (-1)^u y_u y_{v-u}`: `ŷ(ξ) ŷ(-ξ)` is its DFT. -/
def H20_C (Y : ZMod n → K) (v : ZMod n) : K := ∑ u, sgn u * Y u * Y (v - u)

/-- `D(v) = S ∑_{2t = v} y_t`: `ŷ(-1) ŷ(ξ^2)` is its DFT. -/
def H20_D (Y : ZMod n → K) (v : ZMod n) : K := S Y * ∑ t, if 2 * t = v then Y t else 0

theorem H20_F4_lhs {ω : K} (hω : IsPrimitiveRoot ω n) (hn : Even n) (h2 : 2 ≤ n) (Y : ZMod n → K) (k : ZMod n) :
    dft ω Y k * dft ω Y (k + half n) = dft ω (H20_C Y) k := by
  have hω1 := hω.pow_eq_one
  have hsg : ∀ u : ZMod n, (ω ^ (k + half n).val) ^ u.val = sgn u * ω ^ ((k * u).val) := by
    intro u
    rw [H4_pow_val_mul hω1, add_mul, H4_pow_val_add hω1, ← H4_pow_val_mul hω1 (half n),
      H4_pow_val_half hω hn h2, sgn]
    ring
  unfold dft H20_C
  simp_rw [hsg]
  simp_rw [H4_pow_val_mul hω1, Finset.sum_mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [← (Equiv.subRight u).sum_comp]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Equiv.subRight_apply]
  have hx : ω ^ ((k * (v - u)).val) * ω ^ ((k * u).val) = ω ^ ((k * v).val) := by
    rw [← H4_pow_val_add hω1]; congr 2; ring
  linear_combination (Y (v - u) * Y u * sgn u) * hx

theorem H20_F4_rhs {ω : K} (hω : IsPrimitiveRoot ω n) (hn : Even n) (h2 : 2 ≤ n) (Y : ZMod n → K) (k : ZMod n) :
    dft ω Y (half n) * dft ω Y (2 * k) = dft ω (H20_D Y) k := by
  have hω1 := hω.pow_eq_one
  rw [H4_S_eq_dft hn h2 hω]
  unfold dft H20_D
  simp_rw [H4_pow_val_mul hω1, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  have hite : ∀ v : ZMod n, S Y * (if 2 * t = v then Y t else 0) * ω ^ ((k * v).val) =
      if 2 * t = v then S Y * (Y t * ω ^ ((2 * k * t).val)) else 0 := by
    intro v
    split_ifs with hv
    · subst hv; rw [show 2 * k * t = k * (2 * t) by ring]; ring
    · ring
  rw [Finset.sum_congr rfl (fun v _ => hite v), Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]

/-- For even `n`, `(2t).val` is even. -/
theorem H20_not_odd_two_mul (hn : Even n) (t : ZMod n) : ¬ Odd (2 * t).val := by
  intro h
  rw [H7_val_odd_iff (even_iff_two_dvd.mp hn), map_mul, map_ofNat] at h
  have h20 : (2 : ZMod 2) = 0 := rfl
  rw [h20, zero_mul] at h
  exact absurd h (by decide)

theorem H20_C_odd (hn : Even n) (h2K : (2 : K) ≠ 0) (Y : ZMod n → K) (v : ZMod n) (hv : Odd v.val) :
    H20_C Y v = 0 := by
  have hsv : (sgn v : K) = -1 := by unfold sgn; exact hv.neg_one_pow
  have hflip : H20_C Y v = -H20_C Y v := by
    unfold H20_C
    conv_lhs => rw [← (Equiv.subLeft v).sum_comp]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro u _
    simp only [Equiv.subLeft_apply, sub_sub_cancel]
    rw [sub_eq_add_neg, H5_sgn_add hn, H5_sgn_neg hn, hsv]
    ring
  have h2C : (2 : K) * H20_C Y v = 0 := by linear_combination hflip
  exact (mul_eq_zero.mp h2C).resolve_left h2K

theorem H20_D_odd (hn : Even n) (Y : ZMod n → K) (v : ZMod n) (hv : Odd v.val) : H20_D Y v = 0 := by
  unfold H20_D
  rw [Finset.sum_eq_zero, mul_zero]
  intro t _
  rw [ite_eq_right]
  intro h
  rw [← h] at hv
  exact H20_not_odd_two_mul hn t hv

theorem H20_sum_two_mul (hn : Even n) (h3 : 3 ≤ n) (Y : ZMod n → K) (s : ZMod n) :
    ∑ t, (if 2 * t = 2 * s then Y t else 0) = Y s + Y (s + half n) := by
  have hiff : ∀ t : ZMod n, 2 * t = 2 * s ↔ t = s ∨ t = s + half n := by
    intro t
    constructor
    · intro h
      have h0 : 2 * (t - s) = 0 := by rw [mul_sub, h, sub_self]
      rcases H4_two_mul_eq_zero hn h3 _ h0 with h1 | h1
      · left; exact sub_eq_zero.mp h1
      · right; rw [← h1]; ring
    · rintro (rfl | rfl)
      · rfl
      · rw [mul_add, H4_two_mul_half hn, add_zero]
  simp_rw [hiff]
  rw [← Finset.sum_filter]
  have hfilt : Finset.univ.filter (fun t : ZMod n => t = s ∨ t = s + half n) = {s, s + half n} := by
    ext t; simp
  rw [hfilt, Finset.sum_pair]
  intro h
  apply H4_half_ne_zero (n := n) (by omega)
  linear_combination -h

theorem H20_D_two_mul (hn : Even n) (h3 : 3 ≤ n) (Y : ZMod n → K) (s : ZMod n) :
    H20_D Y (2 * s) = (Y s + Y (s + half n)) * S Y := by
  unfold H20_D
  rw [H20_sum_two_mul hn h3, mul_comm]

/-- (L4) ⇔ `C = D`. -/
theorem H20_L4_iff_CD (hn : Even n) (h3 : 3 ≤ n) (h2K : (2 : K) ≠ 0) (Y : ZMod n → K) :
    L4 Y ↔ H20_C Y = H20_D Y := by
  constructor
  · intro h4
    have hall : ∀ s : ZMod n, H20_C Y (2 * s) = H20_D Y (2 * s) := by
      intro s
      by_cases hs : s.val < n / 2
      · rw [H20_D_two_mul hn h3]; exact h4 s hs
      · have hs' := H2_add_half_val_lt hn s hs
        have h22 : 2 * (s + half n) = 2 * s := by rw [mul_add, H4_two_mul_half hn, add_zero]
        rw [← h22, H20_D_two_mul hn h3]
        exact h4 _ hs'
    funext v
    by_cases hv : Odd v.val
    · rw [H20_C_odd hn h2K Y v hv, H20_D_odd hn Y v hv]
    · rw [← H4_two_mul_hf v hv]; exact hall _
  · intro hCD s _
    have := congrFun hCD (2 * s)
    rw [H20_D_two_mul hn h3] at this
    exact this

/-- (L4) ⇔ (F4). -/
theorem H20_L4_iff_F4 {ω : K} (hω : IsPrimitiveRoot ω n) (hnK : (n : K) ≠ 0) (hn : Even n) (h3 : 3 ≤ n)
    (h2K : (2 : K) ≠ 0) (Y : ZMod n → K) : L4 Y ↔ F4 (dft ω Y) := by
  rw [H20_L4_iff_CD hn h3 h2K]
  unfold F4
  simp_rw [H20_F4_lhs hω hn (by omega), H20_F4_rhs hω hn (by omega)]
  constructor
  · intro h k; rw [h]
  · intro h; exact H20_dft_inj hω hnK (funext h)

end F4

/-! ## Part E — the whole system, `S^2 = κ`, transport along an injective ring map -/

section Whole

variable {n : ℕ} [NeZero n] {K : Type*} [Field K]

/-- The norm-free `r`-system ⇔ (F1_r) ∧ (F3_r) ∧ (F4), for `Y` in any field of characteristic `r` (GENERAL FORM). -/
theorem H20_NFr_iff (r : ℕ) [Fact r.Prime] [CharP K r] {ω : K} (hω : IsPrimitiveRoot ω n) (hn : Even n)
    (h3 : 3 ≤ n) (hnK : (n : K) ≠ 0) (h2K : (2 : K) ≠ 0) (hrn : IsUnit (r : ZMod n)) (σ : ℤ) (Y : ZMod n → K) :
    NFrEqs r σ Y ↔ F1 r σ ω (dft ω Y) ∧ F3r (kappa n K) ω (dft ω Y) ∧ F4 (dft ω Y) := by
  unfold NFrEqs
  rw [H20_L1_iff_F1 r hω hnK hrn σ Y, ← H20_L3_iff_F3r hω hnK hn Y, H20_L4_iff_F4 hω hnK hn h3 h2K Y]
  tauto

/-- (F3_r) at `ξ = -1` gives `S^2 = κ` (`4 ∣ n`). -/
theorem H20_S_sq_of_F3r {ω : K} (hω : IsPrimitiveRoot ω n) (h4 : 4 ∣ n) (κ : K) (Y : ZMod n → K)
    (hF3 : F3r κ ω (dft ω Y)) : S Y ^ 2 = κ := by
  have hn : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h4)
  have h2 : 2 ≤ n := Nat.le_of_dvd (NeZero.pos n) (dvd_trans (by norm_num) h4)
  have hm := hF3.1 (half n) (H4_half_ne_zero h2)
  rw [H4_neg_half hn, H4_S_eq_dft hn h2 hω, H4_pow_val_half hω hn h2] at hm
  have he : Even (n / 2) := ⟨n / 4, by omega⟩
  rw [he.neg_one_pow, mul_one, ← sq] at hm
  exact hm

/-- `S` commutes with ring maps. -/
theorem H20_S_map {F : Type*} [CommRing F] (f : F →+* K) (y : ZMod n → F) :
    S (fun t => f (y t)) = f (S y) := by
  simp [S, sgn, map_sum, map_mul]

/-- `κ` commutes with ring maps. -/
theorem H20_kappa_map {F : Type*} [CommRing F] (f : F →+* K) : f (kappa n F) = kappa n K := by
  simp [kappa]

/-- Transport of the norm-free `r`-system along an injective ring map. -/
theorem H20_NFr_map {F : Type*} [CommRing F] (f : F →+* K) (hf : Function.Injective f) (r : ℕ) (σ : ℤ)
    (y : ZMod n → F) : NFrEqs r σ y ↔ NFrEqs r σ (fun t => f (y t)) := by
  have hsgn : ∀ t : ZMod n, f (sgn t) = sgn t := by intro t; simp [sgn]
  have eS : S (fun t => f (y t)) = f (S y) := by simp [S, map_sum, map_mul, hsgn]
  have eR : R (fun t => f (y t)) (half n) = f (R y (half n)) := by simp [R, map_sum, map_mul]
  have e1 : ∀ s : ZMod n, f (y (s + σ)) = f (y s) ^ r ↔ y (s + σ) = y s ^ r := by
    intro s; rw [← map_pow, hf.eq_iff]
  have e3 : ∀ s : ZMod n, (∑ t, f (y t) * f (y (s + t)) = (n : K) * (1 - (pp n : K))) ↔
      ∑ t, y t * y (s + t) = (n : F) * (1 - (pp n : F)) := by
    intro s
    rw [← hf.eq_iff]; simp [map_sum, map_mul]
  have eRm : R (fun t => f (y t)) (half n) = (n : K) ^ 4 ↔ R y (half n) = (n : F) ^ 4 := by
    rw [eR, ← hf.eq_iff]; simp
  have e4 : ∀ s : ZMod n, (∑ t, sgn t * f (y t) * f (y (2 * s - t)) =
      (f (y s) + f (y (s + half n))) * S (fun t => f (y t))) ↔
      ∑ t, sgn t * y t * y (2 * s - t) = (y s + y (s + half n)) * S y := by
    intro s
    rw [eS, ← hf.eq_iff]; simp [map_sum, map_mul, hsgn]
  unfold NFrEqs L1 L3 L4
  simp only [e1, e3, eRm, e4]

end Whole

/-! ## Part F — values in the subfield: `x^{|F|} = x` ⇒ `x ∈ F` -/

theorem H20_mem_range {F L : Type*} [Field F] [Finite F] [Field L] [Algebra F L] (x : L)
    (hx : x ^ Nat.card F = x) : ∃ a : F, algebraMap F L a = x := by
  classical
  have := Fintype.ofFinite F
  by_contra hne
  push Not at hne
  have hq : 1 < Nat.card F := by rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  have hP0 : (Polynomial.X ^ Nat.card F - Polynomial.X : Polynomial L) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero L hq
  have hdeg : (Polynomial.X ^ Nat.card F - Polynomial.X : Polynomial L).natDegree = Nat.card F :=
    FiniteField.X_pow_card_sub_X_natDegree_eq L hq
  have hZ : (insert x (Finset.univ.image (algebraMap F L))).val ⊆
      (Polynomial.X ^ Nat.card F - Polynomial.X : Polynomial L).roots := by
    intro z hz
    rw [Polynomial.mem_roots hP0, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, sub_eq_zero]
    rcases Finset.mem_insert.mp (Finset.mem_val.mp hz) with rfl | hz'
    · exact hx
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hz'
      rw [← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hcard := Polynomial.card_le_degree_of_subset_roots hZ
  have hnot : x ∉ Finset.univ.image (algebraMap F L) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]; exact hne
  rw [hdeg, Finset.card_insert_of_notMem hnot,
    Finset.card_image_of_injective _ (algebraMap F L).injective, Finset.card_univ,
    ← Nat.card_eq_fintype_card] at hcard
  omega

/-- Iterating (L1): `y_{s + Nσ} = y_s^{r^N}`. -/
theorem H20_L1_iter {n : ℕ} [NeZero n] {K : Type*} [CommRing K] (r : ℕ) (σ : ℤ) (Y : ZMod n → K)
    (h1 : L1 r σ Y) (N : ℕ) (s : ZMod n) : Y (s + (N : ZMod n) * (σ : ZMod n)) = Y s ^ (r ^ N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show s + ((N + 1 : ℕ) : ZMod n) * (σ : ZMod n) = (s + (N : ZMod n) * (σ : ZMod n)) + σ by push_cast; ring,
      h1, ih, ← pow_mul, pow_succ]

/-- `(n/g) σ ≡ 0 (mod n)` for `g = gcd(σ, n)`. -/
theorem H20_shift_period (n : ℕ) [NeZero n] (σ : ℤ) :
    ((n / Int.gcd σ n : ℕ) : ZMod n) * (σ : ZMod n) = 0 := by
  obtain ⟨q, hq⟩ := Int.gcd_dvd_left σ n
  have hgn : Int.gcd σ n ∣ n := by
    have := Int.gcd_dvd_right σ (n : ℤ)
    exact Int.natCast_dvd_natCast.mp this
  have hσ : (σ : ZMod n) = ((Int.gcd σ n : ℕ) : ZMod n) * (q : ZMod n) := by
    conv_lhs => rw [hq]
    push_cast; ring
  rw [hσ, ← mul_assoc, ← Nat.cast_mul, Nat.div_mul_cancel hgn, ZMod.natCast_self, zero_mul]

/-- Iterating (F1) with a natural shift: `ŷ(ξ^{r^j}) = ξ^{σ j r^j} ŷ(ξ)^{r^j}`. -/
theorem H20_F1_iter {n : ℕ} [NeZero n] {K : Type*} [Field K] {ω : K} (hω1 : ω ^ n = 1) (r σ : ℕ)
    {h : ZMod n → K} (hF1 : F1 r (σ : ℤ) ω h) :
    ∀ (j : ℕ) (k : ZMod n), h ((r : ZMod n) ^ j * k) = (ω ^ k.val) ^ (σ * j * r ^ j) * h k ^ (r ^ j) := by
  intro j
  induction j with
  | zero => intro k; simp
  | succ j ih =>
    intro k
    have hx : ω ^ ((r : ZMod n) ^ j * k).val = (ω ^ k.val) ^ (r ^ j) := by
      rw [H4_pow_val_mul_nat hω1 k (r ^ j)]; congr 2; push_cast; ring
    have hF := hF1 ((r : ZMod n) ^ j * k)
    rw [show ((r : ℤ) * (σ : ℤ)) = ((r * σ : ℕ) : ℤ) by push_cast; ring, zpow_natCast] at hF
    rw [show (r : ZMod n) ^ (j + 1) * k = r * (r ^ j * k) by ring, hF, ih, hx]
    have e1 : σ * (j + 1) * r ^ (j + 1) = r ^ j * (r * σ) + σ * j * r ^ j * r := by ring
    have e2 : r ^ (j + 1) = r ^ j * r := by ring
    rw [e1, e2, pow_add, pow_mul (ω ^ k.val) (r ^ j) (r * σ), pow_mul (ω ^ k.val) (σ * j * r ^ j) r,
      pow_mul (h k) (r ^ j) r]
    ring

/-! ## The general theorem: any finite field `F` of characteristic `r` whose Frobenius period kills the shift -/

/-- GENERAL FORM (reusable for every `r`, every shift): `F` a finite field of characteristic `r` with `|F| = r^N`
and `N σ ≡ 0 (mod n)`, `4 ∣ n`, `r ∤ n`, `L ⊇ F` with a primitive `n`-th root `ω`: `y ↦ ŷ` is a bijection from the
norm-free `r`-system over `F` onto (F1_r) ∧ (F3_r) ∧ (F4), and every solution has `S^2 = κ`. -/
theorem H20_fourier_general {n : ℕ} [NeZero n] {F : Type*} [Field F] [Finite F] (r : ℕ) [Fact r.Prime]
    [CharP F r] (N : ℕ) (hcard : Nat.card F = r ^ N) (σ : ℤ) (hper : (N : ZMod n) * (σ : ZMod n) = 0)
    (h4 : 4 ∣ n) (hrn : ¬ r ∣ n) {L : Type*} [Field L] [Algebra F L] (ω : L) (hω : IsPrimitiveRoot ω n) :
    Set.BijOn (dftA ω) {y : ZMod n → F | NFrEqs r σ y} {h | F1 r σ ω h ∧ F3r (kappa n L) ω h ∧ F4 h} ∧
      ∀ y : ZMod n → F, NFrEqs r σ y → S y ^ 2 = kappa n F := by
  have hn2 : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h4)
  have h3 : 3 ≤ n := le_trans (by norm_num) (Nat.le_of_dvd (NeZero.pos n) h4)
  have hr2 : r ≠ 2 := by rintro rfl; exact hrn (even_iff_two_dvd.mp hn2)
  have hinj : Function.Injective (algebraMap F L) := (algebraMap F L).injective
  have : CharP L r := charP_of_injective_algebraMap hinj r
  have hnL : (n : L) ≠ 0 := by rw [Ne, CharP.cast_eq_zero_iff L r]; exact hrn
  have h2L : (2 : L) ≠ 0 := by
    have h2' : ((2 : ℕ) : L) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff L r]
      intro h; exact hr2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h)
    exact_mod_cast h2'
  have hunit : IsUnit (r : ZMod n) := (ZMod.isUnit_prime_iff_not_dvd Fact.out).mpr hrn
  have hcore := fun (Y : ZMod n → L) => H20_NFr_iff r hω hn2 h3 hnL h2L hunit σ Y
  have hmap := fun (y : ZMod n → F) => H20_NFr_map (algebraMap F L) hinj r σ y
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · -- MapsTo
    intro y hy
    exact (hcore _).mp ((hmap y).mp hy)
  · -- InjOn
    intro y1 _ y2 _ h12
    have h12' : dft ω (fun t => algebraMap F L (y1 t)) = dft ω (fun t => algebraMap F L (y2 t)) := h12
    have hY := H20_dft_inj hω hnL h12'
    funext t
    exact hinj (congrFun hY t)
  · -- SurjOn: the inverse DFT solves the system in `L`; its values are fixed by `x ↦ x^{r^N}`, so lie in `F`
    intro h hh
    have hdY : dft ω (H20_idft ω h) = h := H20_dft_idft hω hnL h
    have hNY : NFrEqs r σ (H20_idft ω h) := (hcore _).mpr (by rw [hdY]; exact hh)
    have hfix : ∀ s : ZMod n, H20_idft ω h s ^ Nat.card F = H20_idft ω h s := by
      intro s
      rw [hcard, ← H20_L1_iter r σ _ hNY.1 N s, hper, add_zero]
    choose y hy using fun s => H20_mem_range (H20_idft ω h s) (hfix s)
    have hYy : (fun t => algebraMap F L (y t)) = H20_idft ω h := funext hy
    refine ⟨y, ?_, ?_⟩
    · show NFrEqs r σ y
      rw [hmap y, hYy]; exact hNY
    · show dft ω (fun t => algebraMap F L (y t)) = h
      rw [hYy, hdY]
  · -- `S^2 = κ` from (F3_r) at `-1`
    intro y hy
    have hF3 := ((hcore _).mp ((hmap y).mp hy)).2.1
    have hS := H20_S_sq_of_F3r hω h4 _ _ hF3
    apply hinj
    rw [map_pow, ← H20_S_map, hS, H20_kappa_map]

/-! ## The target (row: Coverage — s6_primes.tex:132-136) -/

/-- Coverage — s6_primes.tex:132-136 (Fourier form, every `r`): `n = 2^a n_odd`, `a ≥ 3`, `r` prime, `r ∤ pn`, any
integer `σ_r`: `y ↦ ŷ` is a bijection from the norm-free `r`-system onto the functions with (F1_r), (F3_r), (F4_r), and
(F3_r) at `-1` gives `S^2 = κ`. -/
theorem sec_6_3_fourier_proved (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a)
    (_hodd : Odd nodd) (hr : ¬ r ∣ pp n * n) (σr : ℤ) {L : Type*} [Field L]
    [Algebra (GaloisField r (n / Int.gcd σr n)) L] (ω : L) (hω : IsPrimitiveRoot ω n) :
    Set.BijOn (dftA ω) (NFrSet n r σr) {h | F1 r σr ω h ∧ F3r (kappa n L) ω h ∧ F4 h} ∧
      ∀ y ∈ NFrSet n r σr, S y ^ 2 = kappa n _ := by
  have h8 : 2 ^ 3 ∣ n := by
    rw [hn]; exact Dvd.dvd.mul_right (pow_dvd_pow 2 ha) _
  have h4 : 4 ∣ n := dvd_trans (by norm_num) h8
  have hrn : ¬ r ∣ n := fun h => hr (dvd_mul_of_dvd_right h _)
  have hgn : Int.gcd σr n ∣ n := Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right σr n)
  have hN : n / Int.gcd σr n ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (NeZero.pos n) hgn) (Nat.pos_of_dvd_of_pos hgn (NeZero.pos n))).ne'
  obtain ⟨hB, hS⟩ := H20_fourier_general r (n / Int.gcd σr n) (GaloisField.card r _ hN) σr
    (H20_shift_period n σr) h4 hrn ω hω
  exact ⟨hB, fun y hy => hS y hy⟩

/-! ## BONUS: the `r = 5` row (s6_primes.tex:51-62) as an instance of the general theorem -/

/-- Exact copy of `Xia.Paper.sec_6_2_fourier` (Coverage — Fourier form for `r = 5`), derived from
`H20_fourier_general` with `F = F_{5^n}`, `N = n`, `σ = 1`. Named `H20_…` to avoid name clashes. -/
theorem H20_sec_6_2_fourier (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (_heo : Odd e) {L : Type*} [Field L]
    [Algebra (GaloisField 5 n) L] (ω : L) (hω : IsPrimitiveRoot ω n) :
    Set.BijOn (dftA ω) (NF5Set n) {h | F1 5 1 ω h ∧ F3r (kappa n L) ω h ∧ F4 h} ∧
      ∀ y ∈ NF5Set n, (∀ (j : ℕ) (k : ZMod n),
        dftA ω y ((5 : ZMod n) ^ j * k) = (ω ^ k.val) ^ (j * 5 ^ j) * dftA ω y k ^ (5 ^ j)) ∧
        dftA ω y (half n) = algebraMap _ L (S y) := by
  have h4 : 4 ∣ n := by
    rw [hne]; exact pow_dvd_pow 2 (by omega : 2 ≤ e)
  have hn2 : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h4)
  have h2 : 2 ≤ n := Nat.le_of_dvd (NeZero.pos n) (dvd_trans (by norm_num) h4)
  have h5n : ¬ 5 ∣ n := by
    rw [hne]; intro h
    have := (Nat.Prime.dvd_of_dvd_pow (by norm_num) h : 5 ∣ 2)
    omega
  have hper : ((n : ℕ) : ZMod n) * ((1 : ℤ) : ZMod n) = 0 := by rw [ZMod.natCast_self, zero_mul]
  obtain ⟨hB, -⟩ := H20_fourier_general 5 n (GaloisField.card 5 n (NeZero.ne n)) 1 hper h4 h5n ω hω
  refine ⟨hB, fun y hy => ⟨?_, ?_⟩⟩
  · intro j k
    have hF1 : F1 5 ((1 : ℕ) : ℤ) ω (dftA ω y) := (hB.1 hy).1
    have hit := H20_F1_iter hω.pow_eq_one 5 1 hF1 j k
    rw [Nat.cast_ofNat, one_mul] at hit
    exact hit
  · show dft ω (fun t => algebraMap _ L (y t)) (half n) = _
    rw [H4_S_eq_dft hn2 h2 hω, H20_S_map]

/-! ## Axiom audit -/

#print axioms sec_6_3_fourier_proved
#print axioms H20_sec_6_2_fourier
#print axioms H20_fourier_general
#print axioms H20_NFr_iff

end Xia.Proofs
