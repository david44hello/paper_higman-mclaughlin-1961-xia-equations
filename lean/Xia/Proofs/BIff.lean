/- Xia/Proofs/BIff.lean — proofs of the rows thm_B_components, thm_B_xia_iff of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry
import Xia.Defs.BlockSpace
import Xia.Proofs.FourierSteps
import Xia.Proofs.Sec22
import Xia.Proofs.Sec5
import Xia.Proofs.Prop24
import Xia.Proofs.VcV
import Xia.Proofs.VdV

namespace Xia.Proofs

open Xia Finset

/-! ## (0) the parameters `a`, `nodd` of the installed Section 5 rows -/

/-- `n ≡ 8 (mod 24)` gives `n = 2^a nodd` with `nodd` odd, `a ≥ 3`, and `3 ∤ n`. -/
theorem H38_params {n : ℕ} (hn : n % 24 = 8) :
    ∃ a nodd : ℕ, n = 2 ^ a * nodd ∧ 3 ≤ a ∧ Odd nodd ∧ ¬ 3 ∣ n := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨a, nodd, hodd, hfac⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  refine ⟨a, nodd, hfac, ?_, hodd, by omega⟩
  by_contra hge
  have hlt : a < 3 := not_le.mp hge
  obtain ⟨j, hj⟩ := hodd
  interval_cases a <;> norm_num at hfac <;> omega

/-! ## (1) Row thm_B_components -/

theorem thm_B_components_proved (n : ℕ) [NeZero n] (hn : n % 24 = 8) {L : Type*} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2))
    (hy : y ∈ NFSet n 2) :
    let ν := nuData (topOf ω y)
    (∀ v ∈ VfibPlus ω ν, Ycoef ω 1 v = 0) ∧ (∀ v ∈ VfibMinus ω ν, Ycoef ω 0 v = 0) ∧
    (∀ v ∈ Vfib ω ν, ∀ v' ∈ Vfib ω ν, Ycoef ω 0 v = Ycoef ω 0 v' → (v + Tsh v) / 2 = (v' + Tsh v') / 2) ∧
    ∀ v ∈ Vfib ω ν, ∀ v' ∈ Vfib ω ν, Ycoef ω 1 v = Ycoef ω 1 v' → (v - Tsh v) / 2 = (v' - Tsh v') / 2 := by
  intro ν
  obtain ⟨a, nodd, hn', ha, hodd, h3⟩ := H38_params hn
  obtain ⟨hdec, -, hadd, -, hinj0, hinj1, hm0, hp1, -⟩ :=
    thm_5_1_d_V_proved n a nodd hn' ha hodd h3 ω hω y hy
  refine ⟨hp1, hm0, ?_, ?_⟩
  · -- `𝒴_0` sees only the `V_+`-component, and is injective there
    intro v hv v' hv' heq
    obtain ⟨hvp, hvm, hvd⟩ := hdec v hv
    obtain ⟨hvp', hvm', hvd'⟩ := hdec v' hv'
    have e1 := congrArg (Ycoef ω 0) hvd
    have e2 := congrArg (Ycoef ω 0) hvd'
    rw [hadd, hm0 _ hvm, add_zero] at e1
    rw [hadd, hm0 _ hvm', add_zero] at e2
    exact hinj0 hvp hvp' (by rw [← e1, ← e2, heq])
  · -- `𝒴_1` sees only the `V_-`-component, and is injective there
    intro v hv v' hv' heq
    obtain ⟨hvp, hvm, hvd⟩ := hdec v hv
    obtain ⟨hvp', hvm', hvd'⟩ := hdec v' hv'
    have e1 := congrArg (Ycoef ω 1) hvd
    have e2 := congrArg (Ycoef ω 1) hvd'
    rw [hadd, hp1 _ hvp, zero_add] at e1
    rw [hadd, hp1 _ hvp', zero_add] at e2
    exact hinj1 hvm hvm' (by rw [← e1, ← e2, heq])

/-! ## (2) Row thm_B_xia_iff -/

section H38Iff

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

/-- `((v_+ + v_-) + T(v_+ + v_-))/2 = v_+` when `T v_+ = v_+`, `T v_- = -v_-` (characteristic 3). -/
theorem H38_plus_part [CharP L 3] {vp vm : ZMod n → L} (hp : Tsh vp = vp) (hm : Tsh vm = -vm) :
    (vp + vm + Tsh (vp + vm)) / 2 = vp := by
  have h3L : (3 : L) = 0 := H28_three_eq_zero
  rw [H28_div_two]
  funext k
  have e1 : vp (k + half n) = vp k := congrFun hp k
  have e2 : vm (k + half n) = -vm k := congrFun hm k
  simp only [Pi.neg_apply, Pi.add_apply, Tsh, e1, e2]
  linear_combination (-vp k) * h3L

/-- `((v_+ + v_-) - T(v_+ + v_-))/2 = v_-` when `T v_+ = v_+`, `T v_- = -v_-` (characteristic 3). -/
theorem H38_minus_part [CharP L 3] {vp vm : ZMod n → L} (hp : Tsh vp = vp) (hm : Tsh vm = -vm) :
    (vp + vm - Tsh (vp + vm)) / 2 = vm := by
  have h3L : (3 : L) = 0 := H28_three_eq_zero
  rw [H28_div_two]
  funext k
  have e1 : vp (k + half n) = vp k := congrFun hp k
  have e2 : vm (k + half n) = -vm k := congrFun hm k
  simp only [Pi.neg_apply, Pi.sub_apply, Pi.add_apply, Tsh, e1, e2]
  linear_combination (-vm k) * h3L

end H38Iff

theorem thm_B_xia_iff_proved (n : ℕ) [NeZero n] (hn : n % 24 = 8) {L : Type*} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) :
    (XiaSet n 2).Nonempty ↔
      ∃ y ∈ NFSet n 2, ∃ vp ∈ VfibPlus ω (nuData (topOf ω y)), ∃ vm ∈ VfibMinus ω (nuData (topOf ω y)),
        (∃ x : GaloisField 3 (n / 2), algebraMap _ L x = algebraMap _ L (yPlus n (y 0)) + Ycoef ω 0 vp ∧ Nm n x = -1) ∧
        (∃ x : GaloisField 3 (n / 2), algebraMap _ L x = algebraMap _ L (yPlus n (y 1)) + Ycoef ω 1 vm ∧ Nm n x = -1) ∧
        vp + vm ∈ topOf ω '' fibre ω y := by
  obtain ⟨a, nodd, hn', ha, hodd, h3⟩ := H38_params hn
  have : CharP L 3 := H19_charP n
  have hev : Even n := H19_even_of hn' ha
  have h4 : 4 ∣ n := H19_four_dvd hn' ha
  have hxia := (sec_2_2_xia_eq_proved n hn).2
  constructor
  · -- (→) the fibre of a solution itself
    rintro ⟨y, hyX⟩
    have hyN : y ∈ NFSet n 2 := (sec_2_2_xia_eq_proved n hn).1 hyX
    rw [hxia] at hyX
    obtain ⟨-, hN0, hN1⟩ := hyX
    have hyF : y ∈ fibre ω y := ⟨hyN, fun _ _ => rfl⟩
    obtain ⟨-, -, -, -, hfibV, -, -⟩ := thm_5_1_c_V_proved n a nodd hn' ha hodd h3 ω hω y hyN
    obtain ⟨hdec, -, -, -, -, -, -, -, hpts⟩ := thm_5_1_d_V_proved n a nodd hn' ha hodd h3 ω hω y hyN
    obtain ⟨hvp, hvm, hvd⟩ := hdec _ (hfibV y hyF).1
    obtain ⟨hpt0, hpt1⟩ := hpts y hyF
    refine ⟨y, hyN, (topOf ω y + Tsh (topOf ω y)) / 2, hvp, (topOf ω y - Tsh (topOf ω y)) / 2, hvm,
      ⟨y 0, ?_, hN0⟩, ⟨y 1, ?_, hN1⟩, ⟨y, hyF, hvd⟩⟩
    · rw [← hpt0, ← map_add, H9_split]
    · rw [← hpt1, ← map_add, H9_split]
  · -- (←) a fibre point with top data `v_+ + v_-` solves Xia's system
    rintro ⟨y, hyN, vp, hvp, vm, hvm, ⟨x0, hx0, hN0⟩, ⟨x1, hx1, hN1⟩, ⟨y', hy'F, htop'⟩⟩
    obtain ⟨-, -, -, -, -, -, -, -, hpts⟩ := thm_5_1_d_V_proved n a nodd hn' ha hodd h3 ω hω y hyN
    obtain ⟨hpt0, hpt1⟩ := hpts y' hy'F
    rw [htop', H38_plus_part hvp.2 hvm.2] at hpt0
    rw [htop', H38_minus_part hvp.2 hvm.2] at hpt1
    have hFI : ∀ (ω' : L), IsPrimitiveRoot ω' n → (n : L) ≠ 0 → ∀ z : ZMod n → L,
        (∀ t : ZMod n, z t = (n : L)⁻¹ * ∑ k : ZMod n, dft ω' z k * ((ω' ^ k.val)⁻¹) ^ t.val) ∧
          dft ω' z (half n) = S z := fun ω' hω' hnL' z => fourier_inversion_proved n hev ω' hω' hnL' z
    have hplus : ∀ t : ZMod n, yPlus n (y' t) = yPlus n (y t) := fun t =>
      (H19_yMinus_diff h4 h3 hFI hω hy'F.1.1 hyN.1 hy'F.2 t).2
    have hx0' : y' 0 = x0 := by
      apply (algebraMap (GaloisField 3 (n / 2)) L).injective
      rw [hx0, ← hplus 0, ← hpt0, ← map_add, H9_split]
    have hx1' : y' 1 = x1 := by
      apply (algebraMap (GaloisField 3 (n / 2)) L).injective
      rw [hx1, ← hplus 1, ← hpt1, ← map_add, H9_split]
    refine ⟨y', ?_⟩
    rw [hxia]
    exact ⟨hy'F.1, by rw [hx0']; exact hN0, by rw [hx1']; exact hN1⟩

end Xia.Proofs

#print axioms Xia.Proofs.thm_B_components_proved
#print axioms Xia.Proofs.thm_B_xia_iff_proved
