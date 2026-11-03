/- Xia/Proofs/VdV.lean — proofs of the rows thm_5_1_d_V of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry
import Xia.Defs.BlockSpace
import Xia.Proofs.Sec5
import Xia.Proofs.Prop24

namespace Xia.Proofs

open Xia Finset

set_option linter.unusedSectionVars false

section H28

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

/-! ## (a) the space `V`, the shift `T`, and `1/2 = -1` -/

theorem H28_three_eq_zero [CharP L 3] : (3 : L) = 0 := by
  exact_mod_cast CharP.cast_eq_zero L 3

/-- In characteristic 3, `f / 2 = -f` for functions. -/
theorem H28_div_two [CharP L 3] (f : ZMod n → L) : f / 2 = -f := by
  funext k
  have h2 : (2 : L) = -1 := by linear_combination (H28_three_eq_zero : (3 : L) = 0)
  simp only [Pi.div_apply, Pi.neg_apply, Pi.ofNat_apply, h2, div_neg, div_one]

theorem H28_Vfib_add [CharP L 3] {ω : L} {ν : ZMod n → L} {h h' : ZMod n → L} (hh : h ∈ Vfib ω ν)
    (hh' : h' ∈ Vfib ω ν) : h + h' ∈ Vfib ω ν := by
  obtain ⟨he, hf, hl⟩ := hh
  obtain ⟨he', hf', hl'⟩ := hh'
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · simp only [Pi.add_apply, he k hk, he' k hk, add_zero]
  · simp only [Pi.add_apply]
    rw [hf k hk, hf' k hk, add_pow_char]
    ring
  · simp only [Pi.add_apply]
    linear_combination hl k hk + hl' k hk

theorem H28_Vfib_neg {ω : L} {ν : ZMod n → L} {h : ZMod n → L} (hh : h ∈ Vfib ω ν) : -h ∈ Vfib ω ν := by
  obtain ⟨he, hf, hl⟩ := hh
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · simp only [Pi.neg_apply, he k hk, neg_zero]
  · simp only [Pi.neg_apply]
    rw [hf k hk]
    ring
  · simp only [Pi.neg_apply]
    linear_combination -(hl k hk)

theorem H28_Vfib_sub [CharP L 3] {ω : L} {ν : ZMod n → L} {h h' : ZMod n → L} (hh : h ∈ Vfib ω ν)
    (hh' : h' ∈ Vfib ω ν) : h - h' ∈ Vfib ω ν := by
  rw [sub_eq_add_neg]
  exact H28_Vfib_add hh (H28_Vfib_neg hh')

/-- The ν-data `k ↦ g(k) g(k+m)` are `m`-periodic. -/
theorem H28_nuData_shift (hev : Even n) (g : ZMod n → L) (k : ZMod n) : nuData g (k + half n) = nuData g k := by
  unfold nuData
  rw [add_assoc, H6_half_add_half (even_iff_two_dvd.mp hev), add_zero, mul_comm]

theorem H28_Tsh_Tsh (hev : Even n) (h : ZMod n → L) : Tsh (Tsh h) = h := by
  funext k
  show h (k + half n + half n) = h k
  rw [add_assoc, H6_half_add_half (even_iff_two_dvd.mp hev), add_zero]

/-- `T` maps `V` to `V` (for `m`-periodic ν-data). -/
theorem H28_Tsh_mem (hev : Even n) (h4 : 4 ∣ n) {ω : L} (hω : IsPrimitiveRoot ω n) {ν : ZMod n → L}
    (hν : ∀ k : ZMod n, ν (k + half n) = ν k) {h : ZMod n → L} (hh : h ∈ Vfib ω ν) : Tsh h ∈ Vfib ω ν := by
  have h2 : 2 ∣ n := even_iff_two_dvd.mp hev
  have hhh : half n + half n = (0 : ZMod n) := H6_half_add_half h2
  have hneg : -half n = (half n : ZMod n) := neg_eq_of_add_eq_zero_left hhh
  obtain ⟨he, hf, hl⟩ := hh
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · exact he _ (H19_even_add_half h2 h4 hk)
  · show h (3 * k + half n) = (ω ^ k.val) ^ 6 * h (k + half n) ^ 3
    have e := hf (k + half n) (H19_odd_add_half h2 h4 hk)
    have hidx : (3 : ZMod n) * (k + half n) = 3 * k + half n := by
      rw [mul_add, show (3 : ZMod n) * half n = half n + (half n + half n) by ring, hhh, add_zero]
    have hpow : (ω ^ (k + half n).val) ^ 6 = (ω ^ k.val) ^ 6 := by
      rw [H7_pow_val_add ω hω.pow_eq_one, H6_half_val, H7_pow_half_eq_neg_one hev hω, mul_pow]
      norm_num
    rw [hidx, hpow] at e
    exact e
  · show h (-k + half n) * ν k = -h (k + half n + half n)
    have e := hl (k + half n) (H19_odd_add_half h2 h4 hk)
    rw [hν k, neg_add, hneg, add_assoc, hhh, add_zero] at e
    rw [add_assoc, hhh, add_zero]
    exact e

/-! ## `𝒴_s`: additivity, (P1) Frobenius, periodicity, separation -/

theorem H28_Ycoef_add (ω : L) (s : ℕ) (h h' : ZMod n → L) :
    Ycoef ω s (h + h') = Ycoef ω s h + Ycoef ω s h' := by
  unfold Ycoef
  rw [← mul_add, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl (fun k _ => ?_)
  simp only [Pi.add_apply]
  ring

theorem H28_Ycoef_neg (ω : L) (s : ℕ) (h : ZMod n → L) : Ycoef ω s (-h) = -Ycoef ω s h := by
  unfold Ycoef
  rw [← mul_neg, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl (fun k _ => ?_)
  simp only [Pi.neg_apply]
  ring

theorem H28_Ycoef_sub (ω : L) (s : ℕ) (h h' : ZMod n → L) :
    Ycoef ω s (h - h') = Ycoef ω s h - Ycoef ω s h' := by
  rw [sub_eq_add_neg, H28_Ycoef_add, H28_Ycoef_neg, ← sub_eq_add_neg]

/-- (P1): the Frobenius maps `𝒴_s(h)` to `𝒴_{s+2}(h)` on `V` ((F1) and `k ↦ 3k` a bijection of `ℤ/n`). -/
theorem H28_Ycoef_frob [CharP L 3] (h3 : ¬ 3 ∣ n) (hev : Even n) {ω : L} (hω : IsPrimitiveRoot ω n)
    {ν : ZMod n → L} {h : ZMod n → L} (hh : h ∈ Vfib ω ν) (s : ℕ) :
    Ycoef ω s h ^ 3 = Ycoef ω (s + 2) h := by
  obtain ⟨he, hf, -⟩ := hh
  have h2 : 2 ∣ n := even_iff_two_dvd.mp hev
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have hω0 : ω ≠ 0 := hω.ne_zero (NeZero.ne n)
  have hpt : ∀ k : ZMod n, (h k * ((ω ^ k.val)⁻¹) ^ s) ^ 3 =
      h (3 * k) * ((ω ^ (3 * k).val)⁻¹) ^ (s + 2) := by
    intro k
    have hv : ω ^ ((3 : ZMod n) * k).val = (ω ^ k.val) ^ 3 := by
      rw [show (3 : ZMod n) * k = k + k + k by ring, H7_pow_val_add ω hω.pow_eq_one,
        H7_pow_val_add ω hω.pow_eq_one]
      ring
    rcases Nat.even_or_odd k.val with hk | hk
    · have hk3 : Even ((3 : ZMod n) * k).val := by
        have := H19_even_three_mul h2 hk
        rwa [Nat.cast_ofNat] at this
      rw [he k hk, he _ hk3]
      ring
    · rw [hf k hk, hv, ← inv_pow]
      have hx : ω ^ k.val ≠ 0 := pow_ne_zero _ hω0
      have hx6 : (ω ^ k.val) ^ 6 * ((ω ^ k.val)⁻¹) ^ 6 = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hx, one_pow]
      linear_combination (-(h k ^ 3 * ((ω ^ k.val)⁻¹) ^ (3 * s))) * hx6
  have hn3 : ((n : L)⁻¹) ^ 3 = (n : L)⁻¹ := by
    rw [inv_pow]
    congr 1
    have e := map_natCast (frobenius L 3) n
    rwa [frobenius_def] at e
  unfold Ycoef
  rw [mul_pow, hn3, sum_pow_char]
  congr 1
  refine Fintype.sum_equiv (Units.mulLeft (ZMod.unitOfCoprime 3 hcop)) _ _ (fun k => ?_)
  simp only [Units.mulLeft_apply, ZMod.coe_unitOfCoprime, Nat.cast_ofNat]
  exact hpt k

theorem H28_Ycoef_frob_iter [CharP L 3] (h3 : ¬ 3 ∣ n) (hev : Even n) {ω : L} (hω : IsPrimitiveRoot ω n)
    {ν : ZMod n → L} {h : ZMod n → L} (hh : h ∈ Vfib ω ν) (s j : ℕ) :
    Ycoef ω s h ^ (3 ^ j) = Ycoef ω (s + 2 * j) h := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_mul, ih, H28_Ycoef_frob h3 hev hω hh, show s + 2 * j + 2 = s + 2 * (j + 1) by ring]

theorem H28_Ycoef_period {ω : L} (hω : IsPrimitiveRoot ω n) (s : ℕ) (h : ZMod n → L) :
    Ycoef ω (s + n) h = Ycoef ω s h := by
  unfold Ycoef
  congr 1
  refine sum_congr rfl (fun k _ => ?_)
  have hw : ((ω ^ k.val)⁻¹) ^ n = 1 := by
    rw [inv_pow, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, inv_one]
  rw [pow_add, hw, mul_one]

/-- `𝒴_s(h)` is fixed by `x ↦ x^{3^{n/2}}` on `V`. -/
theorem H28_Ycoef_fix [CharP L 3] (h3 : ¬ 3 ∣ n) (hev : Even n) {ω : L} (hω : IsPrimitiveRoot ω n)
    {ν : ZMod n → L} {h : ZMod n → L} (hh : h ∈ Vfib ω ν) (s : ℕ) :
    Ycoef ω s h ^ (3 ^ (n / 2)) = Ycoef ω s h := by
  have he : n % 2 = 0 := Nat.even_iff.mp hev
  rw [H28_Ycoef_frob_iter h3 hev hω hh, show s + 2 * (n / 2) = s + n by omega, H28_Ycoef_period hω]

/-- Separation: `𝒴_s(Th) = (-1)^s 𝒴_s(h)`. -/
theorem H28_Ycoef_Tsh (hev : Even n) {ω : L} (hω : IsPrimitiveRoot ω n) (s : ℕ) (h : ZMod n → L) :
    Ycoef ω s (Tsh h) = (-1) ^ s * Ycoef ω s h := by
  have hw : ∀ k : ZMod n, (ω ^ (k + half n).val)⁻¹ = -(ω ^ k.val)⁻¹ := by
    intro k
    rw [H7_pow_val_add ω hω.pow_eq_one, H6_half_val, H7_pow_half_eq_neg_one hev hω, mul_neg_one, inv_neg]
  have hsq : ((-1 : L) ^ s) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hre : ∑ k, h k * ((ω ^ k.val)⁻¹) ^ s = ∑ k, h (k + half n) * ((ω ^ (k + half n).val)⁻¹) ^ s :=
    (Equiv.sum_comp (Equiv.addRight (half n)) (fun k => h k * ((ω ^ k.val)⁻¹) ^ s)).symm
  have hsum : ∑ k, Tsh h k * ((ω ^ k.val)⁻¹) ^ s = (-1) ^ s * ∑ k, h k * ((ω ^ k.val)⁻¹) ^ s := by
    rw [hre, mul_sum]
    refine sum_congr rfl (fun k _ => ?_)
    rw [hw, neg_pow]
    show h (k + half n) * _ = _
    linear_combination (-(h (k + half n) * ((ω ^ k.val)⁻¹) ^ s)) * hsq
  unfold Ycoef
  rw [hsum]
  ring

theorem H28_Y_plus_odd [CharP L 3] (hev : Even n) {ω : L} (hω : IsPrimitiveRoot ω n) {ν : ZMod n → L}
    {h : ZMod n → L} (hh : h ∈ VfibPlus ω ν) {s : ℕ} (hs : Odd s) : Ycoef ω s h = 0 := by
  have e := H28_Ycoef_Tsh hev hω s h
  rw [hh.2, hs.neg_one_pow] at e
  have h3L : (3 : L) = 0 := H28_three_eq_zero
  have h2 : (2 : L) * Ycoef ω s h = 0 := by linear_combination e
  have h2L : (2 : L) ≠ 0 := by
    intro h20
    have : (1 : L) = 0 := by linear_combination h3L - h20
    exact one_ne_zero this
  exact (mul_eq_zero.mp h2).resolve_left h2L

theorem H28_Y_minus_even [CharP L 3] (hev : Even n) {ω : L} (hω : IsPrimitiveRoot ω n) {ν : ZMod n → L}
    {h : ZMod n → L} (hh : h ∈ VfibMinus ω ν) {s : ℕ} (hs : Even s) : Ycoef ω s h = 0 := by
  have e := H28_Ycoef_Tsh hev hω s h
  rw [hh.2, hs.neg_one_pow, H28_Ycoef_neg] at e
  have h3L : (3 : L) = 0 := H28_three_eq_zero
  have h2 : (2 : L) * Ycoef ω s h = 0 := by linear_combination -e
  have h2L : (2 : L) ≠ 0 := by
    intro h20
    have : (1 : L) = 0 := by linear_combination h3L - h20
    exact one_ne_zero this
  exact (mul_eq_zero.mp h2).resolve_left h2L

theorem H28_plus_sub [CharP L 3] {ω : L} {ν : ZMod n → L} {h h' : ZMod n → L}
    (hh : h ∈ VfibPlus ω ν) (hh' : h' ∈ VfibPlus ω ν) : h - h' ∈ VfibPlus ω ν := by
  refine ⟨H28_Vfib_sub hh.1 hh'.1, ?_⟩
  show Tsh h - Tsh h' = h - h'
  rw [hh.2, hh'.2]

theorem H28_minus_sub [CharP L 3] {ω : L} {ν : ZMod n → L} {h h' : ZMod n → L}
    (hh : h ∈ VfibMinus ω ν) (hh' : h' ∈ VfibMinus ω ν) : h - h' ∈ VfibMinus ω ν := by
  refine ⟨H28_Vfib_sub hh.1 hh'.1, ?_⟩
  show Tsh h - Tsh h' = -(h - h')
  rw [hh.2, hh'.2, neg_sub, sub_neg_eq_add, neg_add_eq_sub]

end H28

/-! ## `F`-valuedness, Fourier uniqueness, fibre points (need the algebra `F → L`) -/

section H28F

variable {n : ℕ} [NeZero n] {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L]

/-- An element `z ∈ L` with `z^{3^{n/2}} = z` lies in `F = GaloisField 3 (n/2)` (root count of `X^q - X`). -/
theorem H28_mem_range (hn2 : n / 2 ≠ 0) (z : L) (hz : z ^ (3 ^ (n / 2)) = z) :
    ∃ x : GaloisField 3 (n / 2), algebraMap _ L x = z := by
  classical
  let _ : Fintype (GaloisField 3 (n / 2)) := Fintype.ofFinite _
  have hcardF : Fintype.card (GaloisField 3 (n / 2)) = 3 ^ (n / 2) := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 3 (n / 2) hn2]
  have h1q : 1 < Fintype.card (GaloisField 3 (n / 2)) := by
    rw [hcardF]; exact Nat.one_lt_pow hn2 (by norm_num)
  have hinj := (algebraMap (GaloisField 3 (n / 2)) L).injective
  have hq : z ^ (Fintype.card (GaloisField 3 (n / 2))) = z := by rw [hcardF]; exact hz
  set P : Polynomial L := Polynomial.X ^ (Fintype.card (GaloisField 3 (n / 2))) - Polynomial.X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero L h1q
  have hdegP : P.natDegree = Fintype.card (GaloisField 3 (n / 2)) :=
    FiniteField.X_pow_card_sub_X_natDegree_eq L h1q
  have hroot : ∀ s : L, s ^ (Fintype.card (GaloisField 3 (n / 2))) = s → s ∈ P.roots.toFinset := by
    intro s hs
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def, hP]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hs, sub_self]
  by_contra hnot
  set A : Finset L := univ.image (algebraMap (GaloisField 3 (n / 2)) L) with hA
  have hAcard : A.card = Fintype.card (GaloisField 3 (n / 2)) := by
    rw [hA, card_image_of_injective _ hinj, card_univ]
  have hzA : z ∉ A := by
    intro hzA
    obtain ⟨x, -, hx⟩ := mem_image.mp hzA
    exact hnot ⟨x, hx⟩
  have hsub : insert z A ⊆ P.roots.toFinset := by
    intro s hs
    rcases mem_insert.mp hs with hs | hs
    · rw [hs]; exact hroot _ hq
    · obtain ⟨x, -, rfl⟩ := mem_image.mp hs
      apply hroot
      rw [← map_pow, FiniteField.pow_card]
  have h1 := card_le_card hsub
  rw [card_insert_of_notMem hzA, hAcard] at h1
  have h2 := (Multiset.toFinset_card_le P.roots).trans (Polynomial.card_roots' P)
  omega

/-- Fourier uniqueness: if every `𝒴_s(h)` vanishes, `h = 0`. -/
theorem H28_zero_of_Y (hev : Even n) (h3 : ¬ 3 ∣ n) {ω : L} (hω : IsPrimitiveRoot ω n) {h : ZMod n → L}
    (hY : ∀ s : ℕ, Ycoef ω s h = 0) : h = 0 := by
  have hnL := H19_natCast_ne_zero n (L := L) h3
  have hFI : ∀ (ω' : L), IsPrimitiveRoot ω' n → (n : L) ≠ 0 → ∀ y : ZMod n → L,
      (∀ t : ZMod n, y t = (n : L)⁻¹ * ∑ k : ZMod n, dft ω' y k * ((ω' ^ k.val)⁻¹) ^ t.val) ∧
        dft ω' y (half n) = S y := fun ω' hω' hnL' z => fourier_inversion_proved n hev ω' hω' hnL' z
  funext k
  show h k = 0
  refine H19_inv_zero hFI hω hnL h (fun t => ?_) k
  have e := hY t.val
  unfold Ycoef at e
  exact (mul_eq_zero.mp e).resolve_left (inv_ne_zero hnL)

/-- Fibre points: `y^-_t = 𝒴_t(top)` (`ȳ_t = y_{t+m}` by (L1); Fourier inversion; `ω^{-(k+m)t}` vs `ω^{-kt}`). -/
theorem H28_yMinus_top (hev : Even n) (h4 : 4 ∣ n) (h3 : ¬ 3 ∣ n) {ω : L} (hω : IsPrimitiveRoot ω n)
    {y' : ZMod n → GaloisField 3 (n / 2)} (hL1 : L1 3 ((2 : ℕ) : ℤ) y') (t : ZMod n) :
    algebraMap _ L (yMinus n (y' t)) = Ycoef ω t.val (topOf ω y') := by
  have hnL := H19_natCast_ne_zero n (L := L) h3
  have h2L := H19_two_ne_zero n (L := L)
  have hFI := fourier_inversion_proved n hev ω hω hnL (fun s => algebraMap _ L (y' s))
  have e1 : algebraMap _ L (y' t) = (n : L)⁻¹ * ∑ k, dftA ω y' k * ((ω ^ k.val)⁻¹) ^ t.val := hFI.1 t
  have e2 : algebraMap _ L (y' (t + half n)) =
      (n : L)⁻¹ * ∑ k, dftA ω y' k * ((ω ^ k.val)⁻¹) ^ (t + half n).val := hFI.1 (t + half n)
  have hdiff : ∑ k, dftA ω y' k * ((ω ^ k.val)⁻¹) ^ t.val -
      ∑ k, dftA ω y' k * ((ω ^ k.val)⁻¹) ^ (t + half n).val =
      2 * ∑ k, topOf ω y' k * ((ω ^ k.val)⁻¹) ^ t.val := by
    rw [← sum_sub_distrib, mul_sum]
    refine sum_congr rfl (fun k _ => ?_)
    have hw : ((ω ^ k.val)⁻¹) ^ n = 1 := by
      rw [inv_pow, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, inv_one]
    rw [H7_pow_val_add _ hw, H6_half_val]
    unfold topOf
    rcases Nat.even_or_odd k.val with hk | hk
    · have hh : ((ω ^ k.val)⁻¹) ^ (n / 2) = 1 := by
        rw [inv_pow, H19_pow_half_even hev hω hk, inv_one]
      have hko : ¬ Odd k.val := Nat.not_odd_iff_even.mpr hk
      simp only [hko, ↓reduceIte, hh]
      ring
    · have hh : ((ω ^ k.val)⁻¹) ^ (n / 2) = -1 := by
        rw [inv_pow, H19_pow_half_odd hev hω hk, inv_neg, inv_one]
      simp only [hk, ↓reduceIte, hh]
      ring
  unfold yMinus Ycoef
  rw [H19_bar_shift h4 hL1, map_div₀, map_sub, e1, e2, map_ofNat, ← mul_sub, hdiff]
  field_simp

end H28F

/-! ## Row 18V(d) — Theorem 5.1(d), V-form -/

theorem thm_5_1_d_V_proved (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (_hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (y : ZMod n → GaloisField 3 (n / 2)) (_hy : y ∈ NFSet n 2) :
    let ν := nuData (topOf ω y)
    (∀ h ∈ Vfib ω ν, (h + Tsh h) / 2 ∈ VfibPlus ω ν ∧ (h - Tsh h) / 2 ∈ VfibMinus ω ν ∧
      h = (h + Tsh h) / 2 + (h - Tsh h) / 2) ∧
    (∀ hp ∈ VfibPlus ω ν, ∀ hm ∈ VfibMinus ω ν, hp + hm = 0 → hp = 0 ∧ hm = 0) ∧
    (∀ (s : ℕ) (h h' : ZMod n → L), Ycoef ω s (h + h') = Ycoef ω s h + Ycoef ω s h') ∧
    (∀ h ∈ Vfib ω ν, (∃ x : GaloisField 3 (n / 2), algebraMap _ L x = Ycoef ω 0 h) ∧
      ∃ x : GaloisField 3 (n / 2), algebraMap _ L x = Ycoef ω 1 h) ∧
    Set.InjOn (Ycoef ω 0) (VfibPlus ω ν) ∧ Set.InjOn (Ycoef ω 1) (VfibMinus ω ν) ∧
    (∀ h ∈ VfibMinus ω ν, Ycoef ω 0 h = 0) ∧ (∀ h ∈ VfibPlus ω ν, Ycoef ω 1 h = 0) ∧
    ∀ y' ∈ fibre ω y,
      algebraMap _ L (yMinus n (y' 0)) = Ycoef ω 0 ((topOf ω y' + Tsh (topOf ω y')) / 2) ∧
      algebraMap _ L (yMinus n (y' 1)) = Ycoef ω 1 ((topOf ω y' - Tsh (topOf ω y')) / 2) := by
  intro ν
  have : CharP L 3 := H19_charP n
  have hev : Even n := H19_even_of hn ha
  have h4 : 4 ∣ n := H19_four_dvd hn ha
  have hn4 : 4 ≤ n := Nat.le_of_dvd (NeZero.pos n) h4
  have hn2 : n / 2 ≠ 0 := by omega
  have h3L : (3 : L) = 0 := H28_three_eq_zero
  have h2L := H19_two_ne_zero n (L := L)
  have hν : ∀ k : ZMod n, ν (k + half n) = ν k := H28_nuData_shift hev _
  have hT : ∀ h ∈ Vfib ω ν, Tsh h ∈ Vfib ω ν := fun h hh => H28_Tsh_mem hev h4 hω hν hh
  refine ⟨?_, ?_, H28_Ycoef_add ω, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `V = V_+ ⊕ V_-`: the two projections and the decomposition
    intro h hh
    rw [H28_div_two, H28_div_two]
    refine ⟨⟨H28_Vfib_neg (H28_Vfib_add hh (hT h hh)), ?_⟩, ⟨H28_Vfib_neg (H28_Vfib_sub hh (hT h hh)), ?_⟩, ?_⟩
    · show -(Tsh h + Tsh (Tsh h)) = -(h + Tsh h)
      rw [H28_Tsh_Tsh hev, add_comm]
    · show -(Tsh h - Tsh (Tsh h)) = -(-(h - Tsh h))
      rw [H28_Tsh_Tsh hev, neg_neg, neg_sub]
    · funext k
      simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply]
      linear_combination (h k) * h3L
  · -- `V_+ ∩ V_- = 0`
    intro hp hhp hm hhm hsum
    have hmeq : hm = -hp := eq_neg_of_add_eq_zero_right hsum
    have hp0 : hp = 0 := by
      funext k
      have e1 := congrFun hhm.2 k
      have e2 := congrFun hhp.2 k
      rw [hmeq] at e1
      simp only [Tsh, Pi.neg_apply, neg_neg] at e1 e2
      have h2 : (2 : L) * hp k = 0 := by linear_combination -e1 - e2
      exact (mul_eq_zero.mp h2).resolve_left h2L
    exact ⟨hp0, by rw [hmeq, hp0, neg_zero]⟩
  · -- `𝒴_0`, `𝒴_1` take values in `F`
    intro h hh
    exact ⟨H28_mem_range hn2 _ (H28_Ycoef_fix h3 hev hω hh 0),
      H28_mem_range hn2 _ (H28_Ycoef_fix h3 hev hω hh 1)⟩
  · -- `𝒴_0` injective on `V_+`
    intro h1 hh1 h2 hh2 heq
    have hd := H28_plus_sub hh1 hh2
    have hY0 : Ycoef ω 0 (h1 - h2) = 0 := by rw [H28_Ycoef_sub, heq, sub_self]
    have hall : ∀ s : ℕ, Ycoef ω s (h1 - h2) = 0 := by
      intro s
      rcases Nat.even_or_odd s with ⟨j, hj⟩ | hs
      · rw [hj, ← two_mul, ← zero_add (2 * j), ← H28_Ycoef_frob_iter h3 hev hω hd.1, hY0,
          zero_pow (pow_ne_zero _ (by norm_num))]
      · exact H28_Y_plus_odd hev hω hd hs
    exact sub_eq_zero.mp (H28_zero_of_Y hev h3 hω hall)
  · -- `𝒴_1` injective on `V_-`
    intro h1 hh1 h2 hh2 heq
    have hd := H28_minus_sub hh1 hh2
    have hY1 : Ycoef ω 1 (h1 - h2) = 0 := by rw [H28_Ycoef_sub, heq, sub_self]
    have hall : ∀ s : ℕ, Ycoef ω s (h1 - h2) = 0 := by
      intro s
      rcases Nat.even_or_odd s with hs | ⟨j, hj⟩
      · exact H28_Y_minus_even hev hω hd hs
      · rw [hj, add_comm, ← H28_Ycoef_frob_iter h3 hev hω hd.1, hY1, zero_pow (pow_ne_zero _ (by norm_num))]
    exact sub_eq_zero.mp (H28_zero_of_Y hev h3 hω hall)
  · -- `𝒴_0 = 0` on `V_-`
    intro h hh
    exact H28_Y_minus_even hev hω hh ⟨0, rfl⟩
  · -- `𝒴_1 = 0` on `V_+`
    intro h hh
    exact H28_Y_plus_odd hev hω hh odd_one
  · -- fibre points: `y_0^- = 𝒴_0(v_+)`, `y_1^- = 𝒴_1(v_-)`
    intro y' hy'
    have hL1 : L1 3 ((2 : ℕ) : ℤ) y' := hy'.1.1
    have hT0 := H28_Ycoef_Tsh hev hω 0 (topOf ω y')
    have hT1 := H28_Ycoef_Tsh hev hω 1 (topOf ω y')
    have hv1 : (1 : ZMod n).val = 1 := ZMod.val_one'' (by omega)
    constructor
    · rw [H28_yMinus_top hev h4 h3 hω hL1 0, ZMod.val_zero, H28_div_two, H28_Ycoef_neg, H28_Ycoef_add, hT0]
      linear_combination (Ycoef ω 0 (topOf ω y')) * h3L
    · rw [H28_yMinus_top hev h4 h3 hω hL1 1, hv1, H28_div_two, H28_Ycoef_neg, H28_Ycoef_sub, hT1]
      linear_combination (Ycoef ω 1 (topOf ω y')) * h3L

#print axioms thm_5_1_d_V_proved

end Xia.Proofs
