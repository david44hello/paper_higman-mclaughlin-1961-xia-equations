/- Xia/Proofs/Cor35Fibre.lean — proofs of the rows cor_3_5_fibre of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import Xia.Defs.Symmetry
import Xia.Proofs.BSubst

namespace Xia.Proofs

open Xia Finset

set_option linter.unusedSectionVars false

section H39

variable {n : ℕ} [NeZero n]

/-- For `L = F` the transform `dftA` is `dft` (`algebraMap F F = id`). -/
theorem H39_dftA_eq (ξ0 : GaloisField 3 (n / 2)) (y : ZMod n → GaloisField 3 (n / 2)) (k : ZMod n) :
    dftA ξ0 y k = dft ξ0 y k := rfl

/-- (F1) at `k` and at `k + m`: the product `h(k) h(k+m)` at `3k` is fixed by its value at `k`. -/
theorem H39_nu_three {L : Type*} [Field L] (hev : Even n) {ω : L} {h h' : ZMod n → L} (hF1 : F1 3 2 ω h)
    (hF1' : F1 3 2 ω h') {x : ZMod n} (hx : h x * h (x + half n) = h' x * h' (x + half n)) :
    h (3 * x) * h (3 * x + half n) = h' (3 * x) * h' (3 * x + half n) := by
  have e3 : 3 * x + half n = 3 * (x + half n) := by
    have h2 := H7_two_half hev
    linear_combination (-1 : ZMod n) * h2
  rw [e3, H26_F1_at hF1, H26_F1_at hF1, H26_F1_at hF1', H26_F1_at hF1']
  calc (ω ^ x.val) ^ 6 * h x ^ 3 * ((ω ^ (x + half n).val) ^ 6 * h (x + half n) ^ 3)
      = (ω ^ x.val) ^ 6 * (ω ^ (x + half n).val) ^ 6 * (h x * h (x + half n)) ^ 3 := by ring
    _ = (ω ^ x.val) ^ 6 * (ω ^ (x + half n).val) ^ 6 * (h' x * h' (x + half n)) ^ 3 := by rw [hx]
    _ = (ω ^ x.val) ^ 6 * h' x ^ 3 * ((ω ^ (x + half n).val) ^ 6 * h' (x + half n) ^ 3) := by ring

/-- (F3) at `k` and at `k + m`: the product `h(k) h(k+m)` at `-k` is fixed by its value at `k`. -/
theorem H39_nu_neg {L : Type*} [Field L] (hev : Even n) {ω : L} (hω0 : ω ≠ 0) {h h' : ZMod n → L} (hF3 : F3 ω h)
    (hF3' : F3 ω h') {x : ZMod n} (hx : h x * h (x + half n) = h' x * h' (x + half n)) :
    h (-x) * h (-x + half n) = h' (-x) * h' (-x + half n) := by
  have e1 := hF3 x
  have e2 := hF3 (x + half n)
  have e1' := hF3' x
  have e2' := hF3' (x + half n)
  rw [H7_neg_add_half hev]
  have hne : h x * h (x + half n) ≠ 0 := mul_ne_zero (H5_F3_ne hω0 h hF3 x) (H5_F3_ne hω0 h hF3 _)
  apply mul_left_cancel₀ hne
  calc h x * h (x + half n) * (h (-x) * h (-(x + half n)))
      = (h x * h (-x)) * (h (x + half n) * h (-(x + half n))) := by ring
    _ = (h' x * h' (-x)) * (h' (x + half n) * h' (-(x + half n))) := by rw [e1, e2, e1', e2']
    _ = h x * h (x + half n) * (h' (-x) * h' (-(x + half n))) := by rw [hx]; ring

/-- Along the orbit of `1` under `k ↦ 3k`. -/
theorem H39_nu_pow3 {L : Type*} [Field L] (hev : Even n) {ω : L} {h h' : ZMod n → L} (hF1 : F1 3 2 ω h)
    (hF1' : F1 3 2 ω h') (h1 : h 1 * h (1 + half n) = h' 1 * h' (1 + half n)) (j : ℕ) :
    h (3 ^ j) * h (3 ^ j + half n) = h' (3 ^ j) * h' (3 ^ j + half n) := by
  induction j with
  | zero => rw [pow_zero]; exact h1
  | succ j ih => rw [pow_succ']; exact H39_nu_three hev hF1 hF1' ih

/-- Equal `ν`-data at `1` give equal `ν`-data at every odd `ρ`, once every odd residue is `±3^j`. -/
theorem H39_nu_all {L : Type*} [Field L] (hev : Even n) {ω : L} (hω0 : ω ≠ 0) {h h' : ZMod n → L}
    (hF1 : F1 3 2 ω h) (hF1' : F1 3 2 ω h') (hF3 : F3 ω h) (hF3' : F3 ω h')
    (hdec : ∀ x : ZMod n, Odd x.val → ∃ j : ℕ, x = 3 ^ j ∨ x = -3 ^ j)
    (h1 : h 1 * h (1 + half n) = h' 1 * h' (1 + half n)) :
    ∀ ρ : ZMod n, Odd ρ.val → h ρ * h (ρ + half n) = h' ρ * h' (ρ + half n) := by
  intro ρ hρ
  obtain ⟨j, rfl | rfl⟩ := hdec ρ hρ
  · exact H39_nu_pow3 hev hF1 hF1' h1 j
  · exact H39_nu_neg hev hω0 hF3 hF3' (H39_nu_pow3 hev hF1 hF1' h1 j)

/-- Every odd residue mod `2^e` (`e ≥ 3`) is `±3^j`. -/
theorem H39_dec {e : ℕ} (hne : n = 2 ^ e) (he : 3 ≤ e) (x : ZMod n) (hx : Odd x.val) :
    ∃ j : ℕ, x = 3 ^ j ∨ x = -3 ^ j := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 3 := ⟨e - 3, by omega⟩
  subst hne
  exact H3_unit_decomp k x (H3_isUnit_of_odd k x hx)

end H39

/-- `ν(1) = ŷ(1) ŷ(1 + m) = ι ŷ(1)^{1+q}` on `NF(n)` (the substitution acts on `ŷ(ξ_0)` as `T x = ι x^q`). -/
theorem H39_nu_one (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 5 ≤ e) (heo : Odd e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2) :
    dftA ξ0 y 1 * dftA ξ0 y (1 + half n) = iota n ξ0 * dftA ξ0 y 1 ^ (1 + qq n) := by
  have hna : n = 2 ^ e * 1 := by rw [hne, mul_one]
  have h4 : 4 ∣ n := H19_four_dvd hna (by omega)
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hn32 : 32 ≤ n := by
    have : 2 ^ 5 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    omega
  have hone : Odd (1 : ZMod n).val := by
    rw [ZMod.val_one'' (by omega)]
    exact odd_one
  have hfib : y ∈ fibre ξ0 y := ⟨hy, fun k _ => rfl⟩
  obtain ⟨-, -, -, -, hsub⟩ := thm_B_pow2_V_full n e hne he heo ξ0 hξ0 y hy
  have hs := hsub y hfib
  rw [H6_dftA_subst h2 h4 hξ0.pow_eq_one, H6_u_odd h2 hone] at hs
  rw [hs]
  unfold Tmap
  ring

theorem cor_3_5_fibre_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 5 ≤ e) (heo : Odd e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) (y y' : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2) (hy' : y' ∈ NFSet n 2) :
    y' ∈ fibre ξ0 y ↔
      (dft ξ0 y' 1 ^ (1 + qq n) = dft ξ0 y 1 ^ (1 + qq n) ∧ S y' = S y ∧ dft ξ0 y' 0 = dft ξ0 y 0) := by
  have hna : n = 2 ^ e * 1 := by rw [hne, mul_one]
  have h3 : ¬ 3 ∣ n := H4_not3_of_pow2 hne
  have h4 : 4 ∣ n := H19_four_dvd hna (by omega)
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hev : Even n := even_iff_two_dvd.mpr h2
  have hn32 : 32 ≤ n := by
    have : 2 ^ 5 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    omega
  have hone : Odd (1 : ZMod n).val := by
    rw [ZMod.val_one'' (by omega)]
    exact odd_one
  have hξ00 : ξ0 ≠ 0 := hξ0.ne_zero (NeZero.ne n)
  have hι : iota n ξ0 ≠ 0 := pow_ne_zero _ hξ00
  have hP24 := prop_2_4_bij_proved n hev h3 ξ0 hξ0
  have hiff := (thm_5_1_c_yform_of n e 1 hna (by omega) odd_one h3 ξ0 hξ0 hP24).2.1 y' hy' y hy
  have hν1 := H39_nu_one n e hne he heo ξ0 hξ0 y hy
  have hν1' := H39_nu_one n e hne he heo ξ0 hξ0 y' hy'
  have hzero : ∀ k : ZMod n, 2 ^ e ∣ k.val → k = 0 := fun k hk =>
    by_contra (fun hk0 => H4_nonzero_ndvd hne k hk0 hk)
  obtain ⟨hF1, hF3, -⟩ := hP24.mapsTo hy
  obtain ⟨hF1', hF3', -⟩ := hP24.mapsTo hy'
  simp only [← H39_dftA_eq]
  constructor
  · rintro ⟨-, hfib⟩
    obtain ⟨hS, -, hν⟩ := hiff.mpr hfib
    refine ⟨?_, hS, hfib 0 (by simp)⟩
    have e1 := hν 1 hone
    rw [hν1', hν1] at e1
    exact mul_left_cancel₀ hι e1
  · rintro ⟨hq, hS, h0⟩
    refine ⟨hy', hiff.mp ⟨hS, fun k hk => by rw [hzero k hk]; exact h0, ?_⟩⟩
    have h1 : dftA ξ0 y' 1 * dftA ξ0 y' (1 + half n) = dftA ξ0 y 1 * dftA ξ0 y (1 + half n) := by
      rw [hν1', hν1, hq]
    exact H39_nu_all hev hξ00 hF1' hF1 hF3' hF3 (H39_dec hne (by omega)) h1

#print axioms Xia.Proofs.cor_3_5_fibre_proved

end Xia.Proofs
