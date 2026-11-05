/- Xia/Proofs/NormLayers.lean — proofs of the rows intro_norm_layers of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import Xia.Defs.Symmetry
import Xia.Defs.BlockSpace
import Xia.Defs.Decoupling
import Xia.Proofs.Prop24
import Xia.Proofs.FourierSteps
import Xia.Proofs.Sec5
import Xia.Proofs.Thm34bc

namespace Xia.Proofs

open Xia Finset

section H42

variable {n : ℕ} [NeZero n] {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L]

/-- The lower-layer part: `z_t^+ = n^{-1} ∑_{k even} ẑ(k) ω^{-kt}` (in `L`), for any `z` with (L1). -/
theorem H42_plus (h4 : 4 ∣ n) (h3 : ¬ 3 ∣ n) {ω : L} (hω : IsPrimitiveRoot ω n)
    {z : ZMod n → GaloisField 3 (n / 2)} (hz : L1 3 ((2 : ℕ) : ℤ) z) (t : ZMod n) :
    algebraMap _ L (yPlus n (z t)) =
      (n : L)⁻¹ * ∑ k ∈ univ.filter (fun k : ZMod n => Even k.val), dftA ω z k * ((ω ^ k.val)⁻¹) ^ t.val := by
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h4)
  have hnL : (n : L) ≠ 0 := H19_natCast_ne_zero n h3
  have h2L : (2 : L) ≠ 0 := H19_two_ne_zero n
  have hinv := (fourier_inversion_proved n hev ω hω hnL (fun s => algebraMap _ L (z s))).1
  have e := H13_plus_sum h2L hω.pow_eq_one (H9_omega_half hev hω) _ hinv t
  simp only [Nat.not_odd_iff_even] at e
  unfold yPlus
  rw [H19_bar_shift h4 hz t, map_div₀, map_add, map_ofNat, e]
  rfl

/-- The top-layer part: `z_t^- = n^{-1} ∑_{k odd} ẑ(k) ω^{-kt}` (in `L`), for any `z` with (L1). -/
theorem H42_minus (h4 : 4 ∣ n) (h3 : ¬ 3 ∣ n) {ω : L} (hω : IsPrimitiveRoot ω n)
    {z : ZMod n → GaloisField 3 (n / 2)} (hz : L1 3 ((2 : ℕ) : ℤ) z) (t : ZMod n) :
    algebraMap _ L (yMinus n (z t)) =
      (n : L)⁻¹ * ∑ k ∈ univ.filter (fun k : ZMod n => Odd k.val), dftA ω z k * ((ω ^ k.val)⁻¹) ^ t.val := by
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h4)
  have hnL : (n : L) ≠ 0 := H19_natCast_ne_zero n h3
  have h2L : (2 : L) ≠ 0 := H19_two_ne_zero n
  have hinv := (fourier_inversion_proved n hev ω hω hnL (fun s => algebraMap _ L (z s))).1
  have e := H13_minus_sum h2L hω.pow_eq_one (H9_omega_half hev hω) _ hinv t
  unfold yMinus
  rw [H19_bar_shift h4 hz t, map_div₀, map_sub, map_ofNat, e]
  rfl

/-- `𝒴_t(top y)` is the odd-`k` sum. -/
theorem H42_Ycoef_top (ω : L) (z : ZMod n → GaloisField 3 (n / 2)) (s : ℕ) :
    Ycoef ω s (topOf ω z) =
      (n : L)⁻¹ * ∑ k ∈ univ.filter (fun k : ZMod n => Odd k.val), dftA ω z k * ((ω ^ k.val)⁻¹) ^ s := by
  unfold Ycoef topOf
  congr 1
  rw [Finset.sum_filter]
  refine sum_congr rfl (fun k _ => ?_)
  split_ifs <;> simp

end H42

theorem intro_norm_layers_proved (n : ℕ) [NeZero n] (hn : n % 24 = 8) {L : Type*} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2))
    (hy : y ∈ NFSet n 2) :
    (∀ t : ZMod n, algebraMap _ L (yPlus n (y t)) =
        (n : L)⁻¹ * ∑ k ∈ univ.filter (fun k : ZMod n => Even k.val), dftA ω y k * ((ω ^ k.val)⁻¹) ^ t.val) ∧
    (∀ t : ZMod n, algebraMap _ L (yMinus n (y t)) = Ycoef ω t.val (topOf ω y)) ∧
    (∀ t : ZMod n, algebraMap _ L (Nm n (y t)) =
        ((n : L)⁻¹ * ∑ k ∈ univ.filter (fun k : ZMod n => Even k.val), dftA ω y k * ((ω ^ k.val)⁻¹) ^ t.val) ^ 2 -
          Ycoef ω t.val (topOf ω y) ^ 2) ∧
    (∀ y' ∈ fibre ω y, ∀ t : ZMod n, yPlus n (y' t) = yPlus n (y t)) := by
  have h4 : 4 ∣ n := by omega
  have h3 : ¬ 3 ∣ n := by omega
  have hev : Even n := H19_even_of24 hn
  have hL1 : L1 3 ((2 : ℕ) : ℤ) y := hy.1
  have c1 := fun t => H42_plus (L := L) h4 h3 hω hL1 t
  have c2 : ∀ t : ZMod n, algebraMap _ L (yMinus n (y t)) = Ycoef ω t.val (topOf ω y) := fun t => by
    rw [H42_minus h4 h3 hω hL1 t, H42_Ycoef_top]
  refine ⟨c1, c2, fun t => ?_, fun y' hy' t => ?_⟩
  · rw [H19_norm_split n h4 (y t), map_sub, map_pow, map_pow, c1 t, c2 t]
  · exact (H19_yMinus_diff h4 h3 (fun ω' hω' hnL' z => fourier_inversion_proved n hev ω' hω' hnL' z) hω
      hy'.1.1 hL1 hy'.2 t).2

end Xia.Proofs

#print axioms Xia.Proofs.intro_norm_layers_proved
