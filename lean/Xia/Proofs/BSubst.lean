/- Xia/Proofs/BSubst.lean — proofs of the rows thm_B_subst_fibre, thm_B_pow2_V of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import Xia.Proofs.VcV
import Xia.Proofs.Sec5
import Xia.Proofs.BPow2V

namespace Xia.Proofs

open Xia Finset

/-- The substitution `y ↦ y^{(u)}` maps the fibre of `y` to itself (`ŷ^{(u)}(k) = ŷ((1+n/2)k) = ŷ(k)` for even `k`). -/
theorem BS_subst_mem_fibre {n : ℕ} [NeZero n] (h4 : 4 ∣ n) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L]
    {ω : L} (hω : IsPrimitiveRoot ω n) {y y' : ZMod n → GaloisField 3 (n / 2)} (hy' : y' ∈ fibre ω y) :
    ySubst y' ∈ fibre ω y := by
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  obtain ⟨hy'N, hy'f⟩ := hy'
  refine ⟨H19_nf_subst h4 hy'N, fun k hk => ?_⟩
  rw [H6_dftA_subst h2 h4 hω.pow_eq_one, H6_u_even h2 hk, hy'f k hk]

theorem thm_B_subst_fibre_proved (n : ℕ) [NeZero n] (hn : n % 24 = 8) {L : Type*} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2))
    (hy : y ∈ NFSet n 2) :
    let ν := nuData (topOf ω y)
    (∀ y' ∈ fibre ω y, ySubst y' ∈ fibre ω y ∧ ySubst (ySubst y') = y') ∧
    (∀ y' ∈ fibre ω y, topOf ω y' ∈ Vfib ω ν) ∧ Set.InjOn (topOf ω) (fibre ω y) ∧
    (∀ y' ∈ fibre ω y, topOf ω (ySubst y') = Tsh (topOf ω y')) ∧
    (∀ h h' : ZMod n → L, Tsh (h + h') = Tsh h + Tsh h') ∧ (∀ h ∈ Vfib ω ν, Tsh h ∈ Vfib ω ν ∧ Tsh (Tsh h) = h) := by
  intro ν
  obtain ⟨a, nodd, hna, ha, hodd, h3⟩ := H19_decomp n hn
  have h4 : 4 ∣ n := by omega
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  obtain ⟨-, hadd, hinv, hmaps, hpts, hinj, -⟩ := thm_5_1_c_V_proved n a nodd hna ha hodd h3 ω hω y hy
  refine ⟨fun y' hy' => ⟨BS_subst_mem_fibre h4 hω hy', H6_subst_subst h2 h4 y'⟩, fun y' hy' => (hpts y' hy').1, hinj,
    fun y' hy' => (hpts y' hy').2, hadd, fun h hh => ⟨(hmaps h hh).1, hinv h⟩⟩

/-- Row thm_B_pow2_V: `thm_B_pow2_V_proved` (BPow2V.lean) plus `ŷ'(ξ_0) ∈ Vsp n` for every point `y'` of the fibre
(so that "a point of the fibre is given by `x ∈ V`" then reads in this one row). -/
theorem thm_B_pow2_V_full (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 5 ≤ e) (heo : Odd e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2) :
    let ν := nuData (topOf ξ0 y)
    Set.BijOn (fun v : ZMod n → GaloisField 3 (n / 2) => v 1) (Vfib ξ0 ν) (Vsp n) ∧
    (∀ y' ∈ fibre ξ0 y, topOf ξ0 y' 1 = dftA ξ0 y' 1 ∧ dftA ξ0 y' 1 ∈ Vsp n) ∧
    Set.InjOn (fun y' : ZMod n → GaloisField 3 (n / 2) => dftA ξ0 y' 1) (fibre ξ0 y) ∧
    (∀ v ∈ Vfib ξ0 ν, Tsh v 1 = Tmap n ξ0 (v 1)) ∧
    ∀ y' ∈ fibre ξ0 y, dftA ξ0 (ySubst y') 1 = Tmap n ξ0 (dftA ξ0 y' 1) := by
  intro ν
  obtain ⟨hbij, htop, hinj, hT, hsub⟩ := thm_B_pow2_V_proved n e hne he heo ξ0 hξ0 y hy
  have hna : n = 2 ^ e * 1 := by rw [hne, mul_one]
  have h3 : ¬ 3 ∣ n := by
    rw [hne]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  obtain ⟨-, -, -, -, hpts, -, -⟩ :=
    thm_5_1_c_V_proved n e 1 hna (by omega) odd_one h3 ξ0 hξ0 y hy
  refine ⟨hbij, fun y' hy' => ⟨htop y' hy', ?_⟩, hinj, hT, hsub⟩
  rw [← htop y' hy']
  exact hbij.mapsTo (hpts y' hy').1

#print axioms Xia.Proofs.thm_B_subst_fibre_proved
#print axioms Xia.Proofs.thm_B_pow2_V_full

end Xia.Proofs
