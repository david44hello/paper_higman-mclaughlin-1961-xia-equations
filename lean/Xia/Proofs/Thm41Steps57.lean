/- Xia/Proofs/Thm41Steps57.lean — proofs of the rows thm_4_1_step5, rem_4_4_G, thm_4_1_step7 of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry
import Xia.Defs.Layer0

namespace Xia.Proofs

open Xia Finset

set_option linter.unusedSectionVars false

/-! ## 1. Arithmetic of the layer `μ_{n_odd} ∖ {1}` (exponent model: `layer0' n a`) -/

section Basic

variable {n a nodd : ℕ} [NeZero n]

theorem H12_two_pow_dvd (hn : n = 2 ^ a * nodd) : 2 ^ a ∣ n := ⟨nodd, hn⟩

theorem H12_dvd_val_mul (hn : n = 2 ^ a * nodd) (c k : ZMod n) (hk : 2 ^ a ∣ k.val) :
    2 ^ a ∣ (c * k).val := by
  rw [ZMod.val_mul, Nat.dvd_mod_iff (H12_two_pow_dvd hn)]
  exact Dvd.dvd.mul_left hk _

theorem H12_nodd_mul (hn : n = 2 ^ a * nodd) (k : ZMod n) (hk : 2 ^ a ∣ k.val) :
    (nodd : ZMod n) * k = 0 := by
  obtain ⟨j, hj⟩ := hk
  rw [← ZMod.natCast_zmod_val k, hj, ← Nat.cast_mul,
    show nodd * (2 ^ a * j) = n * j by rw [hn]; ring, Nat.cast_mul, ZMod.natCast_self, zero_mul]

/-- `u := (n_odd+1)/2` inverts `2` on the multiples of `2^a`. -/
theorem H12_two_inv (hn : n = 2 ^ a * nodd) (hodd : Odd nodd) (k : ZMod n) (hk : 2 ^ a ∣ k.val) :
    (((nodd + 1) / 2 : ℕ) : ZMod n) * (2 * k) = k := by
  have h2 : (((nodd + 1) / 2 : ℕ) : ZMod n) * (2 * k) = (nodd : ZMod n) * k + k := by
    obtain ⟨r, hr⟩ := hodd
    have h1 : (nodd + 1) / 2 = r + 1 := by omega
    rw [h1, hr]; push_cast; ring
  rw [h2, H12_nodd_mul hn k hk, zero_add]

theorem H12_two_u (hn : n = 2 ^ a * nodd) (hodd : Odd nodd) (k : ZMod n) (hk : 2 ^ a ∣ k.val) :
    2 * ((((nodd + 1) / 2 : ℕ) : ZMod n) * k) = k := by
  rw [mul_left_comm]; exact H12_two_inv hn hodd k hk

theorem H12_two_val_ne (hn : n = 2 ^ a * nodd) (hodd : Odd nodd) (x : ZMod n) (hx : 2 ^ a ∣ x.val) :
    2 * x.val ≠ n := by
  obtain ⟨j, hj⟩ := hx
  obtain ⟨r, hr⟩ := hodd
  intro h
  rw [hj] at h
  rw [hn, hr] at h
  have hpos : 0 < 2 ^ a := pow_pos two_pos a
  have h' : 2 ^ a * (2 * j) = 2 ^ a * (2 * r + 1) := by rw [← h]; ring
  have := Nat.eq_of_mul_eq_mul_left hpos h'
  omega

theorem H12_mem_X {k : ZMod n} : k ∈ layer0' n a ↔ 2 ^ a ∣ k.val ∧ k ≠ 0 := by
  simp [layer0']

theorem H12_isUnit3 (h3 : ¬ 3 ∣ n) : IsUnit (3 : ZMod n) := by
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have h := (ZMod.unitOfCoprime 3 hcop).isUnit
  rwa [ZMod.coe_unitOfCoprime, Nat.cast_ofNat] at h

theorem H12_X_mul3 (hn : n = 2 ^ a * nodd) (h3 : ¬ 3 ∣ n) {k : ZMod n} (hk : k ∈ layer0' n a) :
    3 * k ∈ layer0' n a := by
  rw [H12_mem_X] at hk ⊢
  exact ⟨H12_dvd_val_mul hn _ _ hk.1, fun h => hk.2 ((H12_isUnit3 h3).mul_right_eq_zero.mp h)⟩

theorem H12_X_neg (hn : n = 2 ^ a * nodd) {k : ZMod n} (hk : k ∈ layer0' n a) : -k ∈ layer0' n a := by
  rw [H12_mem_X] at hk ⊢
  refine ⟨?_, neg_ne_zero.mpr hk.2⟩
  rw [show -k = (-1 : ZMod n) * k by ring]
  exact H12_dvd_val_mul hn _ _ hk.1

theorem H12_X_mul2 (hn : n = 2 ^ a * nodd) (hodd : Odd nodd) {k : ZMod n} (hk : k ∈ layer0' n a) :
    2 * k ∈ layer0' n a := by
  rw [H12_mem_X] at hk ⊢
  refine ⟨H12_dvd_val_mul hn _ _ hk.1, fun h => hk.2 ?_⟩
  rw [← H12_two_inv hn hodd k hk.1, h, mul_zero]

theorem H12_X_u (hn : n = 2 ^ a * nodd) (hodd : Odd nodd) {k : ZMod n} (hk : k ∈ layer0' n a) :
    (((nodd + 1) / 2 : ℕ) : ZMod n) * k ∈ layer0' n a := by
  rw [H12_mem_X] at hk ⊢
  refine ⟨H12_dvd_val_mul hn _ _ hk.1, fun h => hk.2 ?_⟩
  rw [← H12_two_u hn hodd k hk.1, h, mul_zero]

theorem H12_X_pow3 (hn : n = 2 ^ a * nodd) (h3 : ¬ 3 ∣ n) {k : ZMod n} (hk : k ∈ layer0' n a) (j : ℕ) :
    (3 : ZMod n) ^ j * k ∈ layer0' n a := by
  induction j with
  | zero => simpa using hk
  | succ j ih => rw [pow_succ', mul_assoc]; exact H12_X_mul3 hn h3 ih

/-- On layer 0, `α^m = 1` (`m = n/2`). -/
theorem H12_om_half (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) {L : Type*} [Field L] {ω : L} (hω1 : ω ^ n = 1)
    (k : ZMod n) (hk : 2 ^ a ∣ k.val) : (ω ^ k.val) ^ (n / 2) = 1 := by
  obtain ⟨j, hj⟩ := hk
  have hn2 : n / 2 = 2 ^ (a - 1) * nodd := by
    have e : n = 2 * (2 ^ (a - 1) * nodd) := by
      rw [hn, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel ha]
    rw [e, Nat.mul_div_cancel_left _ two_pos]
  rw [← pow_mul, hj, hn2, show 2 ^ a * j * (2 ^ (a - 1) * nodd) = n * (j * 2 ^ (a - 1)) by rw [hn]; ring,
    pow_mul, hω1, one_pow]

theorem H12_pow_two_val {M : Type*} [Monoid M] {x : M} (hx : x ^ n = 1) (k : ZMod n) :
    x ^ (2 * k).val = (x ^ k.val) ^ 2 := by
  rw [two_mul, ZMod.val_add, ← pow_eq_pow_mod _ hx, pow_add, sq]

theorem H12_orderOf_pos (h3 : ¬ 3 ∣ n) : 0 < orderOf (3 : ZMod n) := by
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have hu : ((ZMod.unitOfCoprime 3 hcop : (ZMod n)ˣ) : ZMod n) = 3 := by
    rw [ZMod.coe_unitOfCoprime, Nat.cast_ofNat]
  rw [← hu, orderOf_units]
  exact orderOf_pos _

theorem H12_exists_N (h3 : ¬ 3 ∣ n) : ∃ N : ℕ, (3 : ZMod n) ^ N = 1 ∧ 0 < N :=
  ⟨_, pow_orderOf_eq_one _, H12_orderOf_pos h3⟩

end Basic

/-! ## 2. The group `G`, the map `τ`, the torsor `G'` -/

section Groups

variable {n a nodd : ℕ} [NeZero n] {L : Type*} [Field L]

theorem H12_memG {g : ZMod n → L} : g ∈ (Ggrp n a 3 : Set (ZMod n → L)) ↔
    (∀ k ∈ layer0' n a, g (3 * k) = g k ^ 3 ∧ g (-k) * g k = 1) ∧ ∀ k ∉ layer0' n a, g k = 1 := by
  simp only [Ggrp, Set.mem_ofPred_eq, Nat.cast_ofNat]

theorem H12_memGp (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) {ω : L} (hω1 : ω ^ n = 1) {f : ZMod n → L} :
    f ∈ (Gprime n a 3 2 1 ω : Set (ZMod n → L)) ↔
    (∀ k ∈ layer0' n a, f (3 * k) = (ω ^ k.val) ^ 6 * f k ^ 3 ∧ f k * f (-k) = 1) ∧
      ∀ k ∉ layer0' n a, f k = 1 := by
  have e6 : ∀ x : L, x ^ ((3 : ℤ) * 2) = x ^ 6 := fun x => by
    rw [show (3 : ℤ) * 2 = ((6 : ℕ) : ℤ) by norm_num, zpow_natCast]
  simp only [Gprime, Set.mem_ofPred_eq, Nat.cast_ofNat, e6, one_mul]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun k hk => ⟨(h1 k hk).1, ?_⟩, h2⟩
    rw [(h1 k hk).2, H12_om_half hn ha hω1 k (H12_mem_X.mp hk).1]
  · rintro ⟨h1, h2⟩
    refine ⟨fun k hk => ⟨(h1 k hk).1, ?_⟩, h2⟩
    rw [(h1 k hk).2, H12_om_half hn ha hω1 k (H12_mem_X.mp hk).1]

theorem H12_G_ne {g : ZMod n → L} (hg : g ∈ (Ggrp n a 3 : Set (ZMod n → L))) (k : ZMod n) : g k ≠ 0 := by
  rw [H12_memG] at hg
  by_cases hk : k ∈ layer0' n a
  · exact right_ne_zero_of_mul_eq_one (hg.1 k hk).2
  · rw [hg.2 k hk]; exact one_ne_zero

theorem H12_Gp_ne (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) {ω : L} (hω1 : ω ^ n = 1) {f : ZMod n → L}
    (hf : f ∈ (Gprime n a 3 2 1 ω : Set (ZMod n → L))) (k : ZMod n) : f k ≠ 0 := by
  rw [H12_memGp hn ha hω1] at hf
  by_cases hk : k ∈ layer0' n a
  · exact left_ne_zero_of_mul_eq_one (hf.1 k hk).2
  · rw [hf.2 k hk]; exact one_ne_zero

theorem H12_G_one : (1 : ZMod n → L) ∈ (Ggrp n a 3 : Set (ZMod n → L)) := by
  rw [H12_memG]; exact ⟨fun k _ => by simp, fun k _ => rfl⟩

theorem H12_G_mul {g g' : ZMod n → L} (hg : g ∈ (Ggrp n a 3 : Set (ZMod n → L)))
    (hg' : g' ∈ (Ggrp n a 3 : Set (ZMod n → L))) : g * g' ∈ (Ggrp n a 3 : Set (ZMod n → L)) := by
  rw [H12_memG] at hg hg' ⊢
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun k hk => ?_⟩
  · simp only [Pi.mul_apply]; rw [(hg.1 k hk).1, (hg'.1 k hk).1, mul_pow]
  · simp only [Pi.mul_apply]
    calc g (-k) * g' (-k) * (g k * g' k) = (g (-k) * g k) * (g' (-k) * g' k) := by ring
      _ = 1 := by rw [(hg.1 k hk).2, (hg'.1 k hk).2, one_mul]
  · simp only [Pi.mul_apply]; rw [hg.2 k hk, hg'.2 k hk, one_mul]

theorem H12_G_inv {g : ZMod n → L} (hg : g ∈ (Ggrp n a 3 : Set (ZMod n → L))) :
    g⁻¹ ∈ (Ggrp n a 3 : Set (ZMod n → L)) := by
  rw [H12_memG] at hg ⊢
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun k hk => ?_⟩
  · simp only [Pi.inv_apply]; rw [(hg.1 k hk).1, inv_pow]
  · simp only [Pi.inv_apply]; rw [← mul_inv, (hg.1 k hk).2, inv_one]
  · simp only [Pi.inv_apply]; rw [hg.2 k hk, inv_one]

theorem H12_G_div {g g' : ZMod n → L} (hg : g ∈ (Ggrp n a 3 : Set (ZMod n → L)))
    (hg' : g' ∈ (Ggrp n a 3 : Set (ZMod n → L))) : g / g' ∈ (Ggrp n a 3 : Set (ZMod n → L)) := by
  rw [div_eq_mul_inv]; exact H12_G_mul hg (H12_G_inv hg')

theorem H12_tau_mem (g : ZMod n → L) {k : ZMod n} (hk : k ∈ layer0' n a) : tauG n a g k = g (2 * k) := by
  simp [tauG, hk]

theorem H12_tau_nmem (g : ZMod n → L) {k : ZMod n} (hk : k ∉ layer0' n a) : tauG n a g k = 1 := by
  simp [tauG, hk]

theorem H12_tau_mul (g g' : ZMod n → L) : tauG n a (g * g') = tauG n a g * tauG n a g' := by
  funext k; by_cases hk : k ∈ layer0' n a <;> simp [tauG, hk]

theorem H12_tau_inv (g : ZMod n → L) : tauG n a g⁻¹ = (tauG n a g)⁻¹ := by
  funext k; by_cases hk : k ∈ layer0' n a <;> simp [tauG, hk]

theorem H12_tau_G (hn : n = 2 ^ a * nodd) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n) {g : ZMod n → L}
    (hg : g ∈ (Ggrp n a 3 : Set (ZMod n → L))) : tauG n a g ∈ (Ggrp n a 3 : Set (ZMod n → L)) := by
  rw [H12_memG] at hg ⊢
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun k hk => H12_tau_nmem g hk⟩
  · rw [H12_tau_mem g (H12_X_mul3 hn h3 hk), H12_tau_mem g hk, mul_left_comm,
      (hg.1 _ (H12_X_mul2 hn hodd hk)).1]
  · rw [H12_tau_mem g (H12_X_neg hn hk), H12_tau_mem g hk, mul_neg, (hg.1 _ (H12_X_mul2 hn hodd hk)).2]

theorem H12_tau_bij (hn : n = 2 ^ a * nodd) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n) :
    Set.BijOn (tauG n a) (Ggrp n a 3 : Set (ZMod n → L)) (Ggrp n a 3 : Set (ZMod n → L)) := by
  refine ⟨fun g hg => H12_tau_G hn hodd h3 hg, ?_, ?_⟩
  · intro g hg g' hg' h
    funext k
    by_cases hk : k ∈ layer0' n a
    · have hu := H12_X_u hn hodd hk
      have e := congrFun h ((((nodd + 1) / 2 : ℕ) : ZMod n) * k)
      rwa [H12_tau_mem g hu, H12_tau_mem g' hu, H12_two_u hn hodd k (H12_mem_X.mp hk).1] at e
    · rw [(H12_memG.mp hg).2 k hk, (H12_memG.mp hg').2 k hk]
  · intro g hg
    have hg2 := H12_memG.mp hg
    refine ⟨fun k => if k ∈ layer0' n a then g ((((nodd + 1) / 2 : ℕ) : ZMod n) * k) else 1, ?_, ?_⟩
    · rw [H12_memG]
      refine ⟨fun k hk => ⟨?_, ?_⟩, fun k hk => by simp only [ite_eq_right hk]⟩
      · simp only [ite_eq_left (H12_X_mul3 hn h3 hk), ite_eq_left hk]
        rw [mul_left_comm, (hg2.1 _ (H12_X_u hn hodd hk)).1]
      · simp only [ite_eq_left (H12_X_neg hn hk), ite_eq_left hk]
        rw [mul_neg, (hg2.1 _ (H12_X_u hn hodd hk)).2]
    · funext k
      by_cases hk : k ∈ layer0' n a
      · rw [H12_tau_mem _ hk]
        simp only [ite_eq_left (H12_X_mul2 hn hodd hk)]
        rw [H12_two_inv hn hodd k (H12_mem_X.mp hk).1]
      · rw [H12_tau_nmem _ hk, hg2.2 k hk]

theorem H12_G_iter (hn : n = 2 ^ a * nodd) (h3 : ¬ 3 ∣ n) {g : ZMod n → L}
    (hg : g ∈ (Ggrp n a 3 : Set (ZMod n → L))) {k : ZMod n} (hk : k ∈ layer0' n a) (j : ℕ) :
    g ((3 : ZMod n) ^ j * k) = g k ^ (3 ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_assoc, ((H12_memG.mp hg).1 _ (H12_X_pow3 hn h3 hk j)).1, ih, ← pow_mul, ← pow_succ]

theorem H12_G_finite (hn : n = 2 ^ a * nodd) (h3 : ¬ 3 ∣ n) : (Ggrp n a 3 : Set (ZMod n → L)).Finite := by
  obtain ⟨N, hN, hNpos⟩ := H12_exists_N (n := n) h3
  have hpos : 1 ≤ 3 ^ N := Nat.one_le_pow _ _ (by norm_num)
  have hM : 0 < 3 ^ N - 1 := by
    have : 3 ≤ 3 ^ N := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ N := Nat.pow_le_pow_right (by norm_num) hNpos
    omega
  have hfin : {x : L | x ^ (3 ^ N - 1) = 1}.Finite := by
    apply (Polynomial.nthRootsFinset (3 ^ N - 1) (1 : L)).finite_toSet.subset
    intro x hx
    rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset hM]
    exact hx
  apply (Set.Finite.pi (t := fun _ : ZMod n => {x : L | x ^ (3 ^ N - 1) = 1}) (fun _ => hfin)).subset
  intro g hg k _
  show g k ^ (3 ^ N - 1) = 1
  by_cases hk : k ∈ layer0' n a
  · have h1 := H12_G_iter hn h3 hg hk N
    rw [hN, one_mul] at h1
    have hne := H12_G_ne hg k
    calc g k ^ (3 ^ N - 1) = g k ^ (3 ^ N - 1) * g k / g k := by rw [mul_div_cancel_right₀ _ hne]
      _ = g k ^ (3 ^ N) / g k := by rw [← pow_succ, Nat.sub_add_cancel hpos]
      _ = 1 := by rw [← h1, div_self hne]
  · rw [(H12_memG.mp hg).2 k hk, one_pow]

/-! ### `G' ≠ ∅` by a global formula -/

/-- `E(k) := ∑_{j<N} v(3^j k)·3^{N-1-j}`, `v` the symmetric residue (`valMinAbs`). -/
def H12_E (N : ℕ) (k : ZMod n) : ℤ :=
  ∑ j ∈ range N, ((3 : ZMod n) ^ j * k).valMinAbs * (3 : ℤ) ^ (N - 1 - j)

theorem H12_E_three (N : ℕ) (hN : (3 : ZMod n) ^ N = 1) (k : ZMod n) :
    H12_E N (3 * k) = 3 * H12_E N k - ((3 : ℤ) ^ N - 1) * k.valMinAbs := by
  have hA : H12_E N (3 * k) =
      ∑ j ∈ range N, ((3 : ZMod n) ^ (j + 1) * k).valMinAbs * (3 : ℤ) ^ (N - (j + 1)) := by
    unfold H12_E
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_assoc, ← pow_succ, show N - (j + 1) = N - 1 - j by omega]
  have hB : 3 * H12_E N k = ∑ j ∈ range N, ((3 : ZMod n) ^ j * k).valMinAbs * (3 : ℤ) ^ (N - j) := by
    unfold H12_E
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [show N - j = (N - 1 - j) + 1 by omega, pow_succ]
    ring
  have hsub := Finset.sum_range_sub (fun j => ((3 : ZMod n) ^ j * k).valMinAbs * (3 : ℤ) ^ (N - j)) N
  have hbN : ((3 : ZMod n) ^ N * k).valMinAbs * (3 : ℤ) ^ (N - N) = k.valMinAbs := by simp [hN]
  have hb0 : ((3 : ZMod n) ^ 0 * k).valMinAbs * (3 : ℤ) ^ (N - 0) = k.valMinAbs * 3 ^ N := by simp
  rw [Finset.sum_sub_distrib, hbN, hb0] at hsub
  rw [hA, hB]
  linear_combination hsub

theorem H12_E_neg (hn : n = 2 ^ a * nodd) (hodd : Odd nodd) (N : ℕ) (k : ZMod n) (hk : 2 ^ a ∣ k.val) :
    H12_E N (-k) = -H12_E N k := by
  unfold H12_E
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_neg, ZMod.valMinAbs_neg_of_ne_half (H12_two_val_ne hn hodd _ (H12_dvd_val_mul hn _ _ hk)), neg_mul]

theorem H12_zpow_vma {ω : L} (hω0 : ω ≠ 0) (hω1 : ω ^ n = 1) (k : ZMod n) :
    ω ^ k.valMinAbs = ω ^ k.val := by
  have h : ((k.val : ℤ) : ZMod n) = ((k.valMinAbs : ℤ) : ZMod n) := by
    rw [ZMod.coe_valMinAbs, Int.cast_natCast, ZMod.natCast_zmod_val]
  obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h
  rw [show k.valMinAbs = (k.val : ℤ) + n * q by linarith, zpow_add₀ hω0, zpow_mul, zpow_natCast,
    zpow_natCast, hω1, one_zpow, mul_one]

theorem H12_pow6_vma {ω : L} (hω0 : ω ≠ 0) (hω1 : ω ^ n = 1) (k : ZMod n) :
    (ω ^ 6) ^ k.valMinAbs = (ω ^ k.val) ^ 6 := by
  rw [← zpow_natCast ω 6, ← zpow_mul, mul_comm ((6 : ℕ) : ℤ), zpow_mul, H12_zpow_vma hω0 hω1, zpow_natCast]

theorem H12_E2_core {θ c : L} (hθ0 : θ ≠ 0) {M : ℕ} (hθ : θ ^ M = c⁻¹) (E E' v : ℤ)
    (hE : E' = 3 * E - (M : ℤ) * v) : θ ^ E' = c ^ v * (θ ^ E) ^ 3 := by
  rw [hE, show 3 * E - (M : ℤ) * v = E * 3 + M * (-v) by ring, zpow_add₀ hθ0, zpow_mul, zpow_mul,
    zpow_natCast, hθ, inv_zpow', neg_neg, zpow_ofNat, mul_comm]

theorem H12_Gp_nonempty (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    [IsAlgClosed L] {ω : L} (hω : IsPrimitiveRoot ω n) :
    (Gprime n a 3 2 1 ω : Set (ZMod n → L)).Nonempty := by
  have hω1 : ω ^ n = 1 := hω.pow_eq_one
  have hω0 : ω ≠ 0 := hω.ne_zero (NeZero.ne n)
  obtain ⟨N, hN, hNpos⟩ := H12_exists_N (n := n) h3
  have hpos : 1 ≤ 3 ^ N := Nat.one_le_pow _ _ (by norm_num)
  have hM : 0 < 3 ^ N - 1 := by
    have : 3 ≤ 3 ^ N := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ N := Nat.pow_le_pow_right (by norm_num) hNpos
    omega
  obtain ⟨θ, hθ⟩ := IsAlgClosed.exists_pow_nat_eq ((ω ^ 6)⁻¹) hM
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hθ
    exact inv_ne_zero (pow_ne_zero 6 hω0) hθ.symm
  have hMc : ((3 ^ N - 1 : ℕ) : ℤ) = (3 : ℤ) ^ N - 1 := by
    rw [Nat.cast_sub hpos, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  refine ⟨fun k => if k ∈ layer0' n a then θ ^ H12_E N k else 1, ?_⟩
  rw [H12_memGp hn ha hω1]
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun k hk => by simp only [ite_eq_right hk]⟩
  · simp only [ite_eq_left (H12_X_mul3 hn h3 hk), ite_eq_left hk]
    rw [H12_E2_core hθ0 hθ (H12_E N k) (H12_E N (3 * k)) k.valMinAbs (by rw [H12_E_three N hN k, hMc]),
      H12_pow6_vma hω0 hω1]
  · simp only [ite_eq_left (H12_X_neg hn hk), ite_eq_left hk]
    rw [H12_E_neg hn hodd N k (H12_mem_X.mp hk).1, zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ hθ0)]

/-! ### The torsor statements -/

theorem H12_Gp_div (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) {ω : L} (hω0 : ω ≠ 0) (hω1 : ω ^ n = 1)
    {f f' : ZMod n → L} (hf : f ∈ (Gprime n a 3 2 1 ω : Set (ZMod n → L)))
    (hf' : f' ∈ (Gprime n a 3 2 1 ω : Set (ZMod n → L))) : f' / f ∈ (Ggrp n a 3 : Set (ZMod n → L)) := by
  rw [H12_memGp hn ha hω1] at hf hf'
  rw [H12_memG]
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun k hk => ?_⟩
  · simp only [Pi.div_apply]
    rw [(hf.1 k hk).1, (hf'.1 k hk).1, mul_div_mul_left _ _ (pow_ne_zero 6 (pow_ne_zero _ hω0)), div_pow]
  · simp only [Pi.div_apply]
    rw [div_mul_div_comm, mul_comm (f' (-k)), (hf'.1 k hk).2, mul_comm (f (-k)), (hf.1 k hk).2, div_one]
  · simp only [Pi.div_apply]; rw [hf.2 k hk, hf'.2 k hk, div_one]

theorem H12_G_mul_Gp (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) {ω : L} (hω1 : ω ^ n = 1)
    {g f : ZMod n → L} (hg : g ∈ (Ggrp n a 3 : Set (ZMod n → L)))
    (hf : f ∈ (Gprime n a 3 2 1 ω : Set (ZMod n → L))) : g * f ∈ (Gprime n a 3 2 1 ω : Set (ZMod n → L)) := by
  rw [H12_memG] at hg
  rw [H12_memGp hn ha hω1] at hf ⊢
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun k hk => ?_⟩
  · simp only [Pi.mul_apply]; rw [(hg.1 k hk).1, (hf.1 k hk).1]; ring
  · simp only [Pi.mul_apply]
    calc g k * f k * (g (-k) * f (-k)) = (g (-k) * g k) * (f k * f (-k)) := by ring
      _ = 1 := by rw [(hg.1 k hk).2, (hf.1 k hk).2, one_mul]
  · simp only [Pi.mul_apply]; rw [hg.2 k hk, hf.2 k hk, one_mul]

theorem H12_tau_div_Gp (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n) {ω : L}
    (hω0 : ω ≠ 0) (hω1 : ω ^ n = 1) {f : ZMod n → L} (hf : f ∈ (Gprime n a 3 2 1 ω : Set (ZMod n → L))) :
    tauG n a f / f ∈ (Gprime n a 3 2 1 ω : Set (ZMod n → L)) := by
  have hfn := H12_Gp_ne hn ha hω1 hf
  rw [H12_memGp hn ha hω1] at hf ⊢
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun k hk => ?_⟩
  · simp only [Pi.div_apply]
    rw [H12_tau_mem f (H12_X_mul3 hn h3 hk), H12_tau_mem f hk, mul_left_comm,
      (hf.1 _ (H12_X_mul2 hn hodd hk)).1, (hf.1 k hk).1, H12_pow_two_val hω1 k]
    have h1 := hfn k
    have h2 := pow_ne_zero (k.val) hω0
    field_simp
  · simp only [Pi.div_apply]
    rw [H12_tau_mem f (H12_X_neg hn hk), H12_tau_mem f hk, mul_neg, div_mul_div_comm,
      (hf.1 _ (H12_X_mul2 hn hodd hk)).2, (hf.1 k hk).2, div_one]
  · simp only [Pi.div_apply]; rw [H12_tau_nmem f hk, hf.2 k hk, div_one]

theorem H12_E1_iff (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) {ω : L} (hω0 : ω ≠ 0) (hω1 : ω ^ n = 1)
    (P f0 : ZMod n → L) (hP : P ∈ (Gprime n a 3 2 1 ω : Set (ZMod n → L)))
    (hf0 : f0 ∈ (Gprime n a 3 2 1 ω : Set (ZMod n → L))) :
    (∃ f ∈ (Gprime n a 3 2 1 ω : Set (ZMod n → L)), ∀ k ∈ layer0' n a, f (2 * k) = P k * f k) ↔
      ∃ g ∈ (Ggrp n a 3 : Set (ZMod n → L)), P = tauG n a f0 / f0 * (tauG n a g / g) := by
  have hf0n := H12_Gp_ne hn ha hω1 hf0
  have hP1 := ((H12_memGp hn ha hω1).mp hP).2
  have hf01 := ((H12_memGp hn ha hω1).mp hf0).2
  constructor
  · rintro ⟨f, hf, hE⟩
    have hfn := H12_Gp_ne hn ha hω1 hf
    have hf1 := ((H12_memGp hn ha hω1).mp hf).2
    refine ⟨f / f0, H12_Gp_div hn ha hω0 hω1 hf0 hf, ?_⟩
    funext k
    simp only [Pi.mul_apply, Pi.div_apply]
    by_cases hk : k ∈ layer0' n a
    · rw [H12_tau_mem _ hk, H12_tau_mem _ hk, Pi.div_apply, hE k hk]
      have h1 := hfn k
      have h2 := hf0n k
      have h3' := hf0n (2 * k)
      field_simp
    · rw [H12_tau_nmem _ hk, H12_tau_nmem _ hk, hP1 k hk, hf1 k hk, hf01 k hk]
      simp
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g * f0, H12_G_mul_Gp hn ha hω1 hg hf0, fun k hk => ?_⟩
    have hgn := H12_G_ne hg
    simp only [Pi.mul_apply, Pi.div_apply]
    rw [H12_tau_mem _ hk, H12_tau_mem _ hk]
    have h1 := hgn k
    have h2 := hf0n k
    field_simp

theorem H12_E1_card (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) {ω : L} (hω0 : ω ≠ 0) (hω1 : ω ^ n = 1)
    (P : ZMod n → L) (hP : P ∈ (Gprime n a 3 2 1 ω : Set (ZMod n → L)))
    (hex : ∃ f ∈ (Gprime n a 3 2 1 ω : Set (ZMod n → L)), ∀ k ∈ layer0' n a, f (2 * k) = P k * f k) :
    Nat.card {f : ZMod n → L // f ∈ (Gprime n a 3 2 1 ω : Set (ZMod n → L)) ∧
        ∀ k ∈ layer0' n a, f (2 * k) = P k * f k} =
      Nat.card {g : ZMod n → L // g ∈ (Ggrp n a 3 : Set (ZMod n → L)) ∧ tauG n a g = g} := by
  obtain ⟨f1, hf1, hE1⟩ := hex
  have hf1n := H12_Gp_ne hn ha hω1 hf1
  have hf11 := ((H12_memGp hn ha hω1).mp hf1).2
  have hPn := H12_Gp_ne hn ha hω1 hP
  apply Nat.card_congr
  exact
    { toFun := fun f => ⟨f.1 / f1, H12_Gp_div hn ha hω0 hω1 hf1 f.2.1, by
        funext k
        by_cases hk : k ∈ layer0' n a
        · rw [H12_tau_mem _ hk]
          simp only [Pi.div_apply]
          rw [f.2.2 k hk, hE1 k hk, mul_div_mul_left _ _ (hPn k)]
        · rw [H12_tau_nmem _ hk]
          simp only [Pi.div_apply]
          rw [((H12_memGp hn ha hω1).mp f.2.1).2 k hk, hf11 k hk, div_one]⟩
      invFun := fun g => ⟨g.1 * f1, H12_G_mul_Gp hn ha hω1 g.2.1 hf1, fun k hk => by
        simp only [Pi.mul_apply]
        have e := congrFun g.2.2 k
        rw [H12_tau_mem _ hk] at e
        rw [e, hE1 k hk]; ring⟩
      left_inv := fun f => Subtype.ext (funext fun k => by
        simp only [Pi.mul_apply, Pi.div_apply]; exact div_mul_cancel₀ _ (hf1n k))
      right_inv := fun g => Subtype.ext (funext fun k => by
        simp only [Pi.mul_apply, Pi.div_apply]; exact mul_div_cancel_right₀ _ (hf1n k)) }

end Groups

/-! ## 3. Step 5 -/

theorem thm_4_1_step5_proved (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type*} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (hω : IsPrimitiveRoot ω n) :
    let G : Set (ZMod n → L) := Ggrp n a 3
    let G' : Set (ZMod n → L) := Gprime n a 3 2 1 ω
    let τ : (ZMod n → L) → ZMod n → L := tauG n a
    (G.Finite ∧ (1 : ZMod n → L) ∈ G ∧ (∀ g ∈ G, ∀ g' ∈ G, g * g' ∈ G ∧ g⁻¹ ∈ G) ∧ Set.BijOn τ G G ∧
      ∀ g ∈ G, ∀ g' ∈ G, τ (g * g') = τ g * τ g') ∧
    G'.Nonempty ∧ (∀ f ∈ G', ∀ f' ∈ G', f' / f ∈ G) ∧ (∀ g ∈ G, ∀ f ∈ G', g * f ∈ G') ∧
    (∀ f ∈ G', τ f / f ∈ G') ∧
    ∀ P ∈ G', ∀ f0 ∈ G',
      ((∃ f ∈ G', ∀ k ∈ layer0' n a, f (2 * k) = P k * f k) ↔ ∃ g ∈ G, P = τ f0 / f0 * (τ g / g)) ∧
      ((∃ f ∈ G', ∀ k ∈ layer0' n a, f (2 * k) = P k * f k) →
        Nat.card {f : ZMod n → L // f ∈ G' ∧ ∀ k ∈ layer0' n a, f (2 * k) = P k * f k} =
          Nat.card {g : ZMod n → L // g ∈ G ∧ τ g = g}) := by
  intro G G' τ
  have ha1 : 1 ≤ a := by omega
  have hω1 : ω ^ n = 1 := hω.pow_eq_one
  have hω0 : ω ≠ 0 := hω.ne_zero (NeZero.ne n)
  exact ⟨⟨H12_G_finite hn h3, H12_G_one, fun g hg g' hg' => ⟨H12_G_mul hg hg', H12_G_inv hg⟩,
      H12_tau_bij hn hodd h3, fun g _ g' _ => H12_tau_mul g g'⟩,
    H12_Gp_nonempty hn ha1 hodd h3 hω, fun f hf f' hf' => H12_Gp_div hn ha1 hω0 hω1 hf hf',
    fun g hg f hf => H12_G_mul_Gp hn ha1 hω1 hg hf, fun f hf => H12_tau_div_Gp hn ha1 hodd h3 hω0 hω1 hf,
    fun P hP f0 hf0 => ⟨H12_E1_iff hn ha1 hω0 hω1 P f0 hP hf0, fun hex => H12_E1_card hn ha1 hω0 hω1 P hP hex⟩⟩

/-! ## 4. Step 7, first part: `|(τ-1)G| · |G^τ| = |G|` (first isomorphism theorem, by an explicit bijection) -/

theorem H12_first_iso {ι L : Type*} [Field L] (G : Set (ι → L)) (τ : (ι → L) → ι → L)
    (hne : ∀ g ∈ G, ∀ x, g x ≠ 0) (hmul : ∀ g ∈ G, ∀ g' ∈ G, g * g' ∈ G) (hinv : ∀ g ∈ G, g⁻¹ ∈ G)
    (hτG : ∀ g ∈ G, τ g ∈ G) (hτmul : ∀ g g', τ (g * g') = τ g * τ g') (hτinv : ∀ g, τ g⁻¹ = (τ g)⁻¹) :
    Nat.card ((fun g => τ g / g) '' G) * Nat.card {g // g ∈ G ∧ τ g = g} = Nat.card G := by
  classical
  let φ : (ι → L) → ι → L := fun g => τ g / g
  let s : (ι → L) → ι → L := fun y => if h : y ∈ φ '' G then h.choose else 1
  have hs : ∀ y ∈ φ '' G, s y ∈ G ∧ φ (s y) = y := by
    intro y hy
    simp only [s, dite_eq_left hy]
    exact hy.choose_spec
  have hφmul : ∀ g h, φ (g * h) = φ g * φ h := by
    intro g h
    simp only [φ]
    rw [hτmul, div_mul_div_comm]
  have hdivG : ∀ g ∈ G, ∀ h ∈ G, g / h ∈ G := fun g hg h hh => by
    rw [div_eq_mul_inv]; exact hmul _ hg _ (hinv _ hh)
  have key : ∀ g ∈ G, ∀ h ∈ G, φ g = φ h → τ (g / h) = g / h := by
    intro g hg h hh hgh
    rw [div_eq_mul_inv, hτmul, hτinv]
    funext x
    have e := congrFun hgh x
    simp only [φ, Pi.div_apply] at e
    simp only [Pi.mul_apply, Pi.inv_apply]
    rw [div_eq_div_iff (hne g hg x) (hne h hh x)] at e
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff (hne _ (hτG h hh) x) (hne h hh x), e, mul_comm]
  have hmemφ : ∀ g ∈ G, φ g ∈ φ '' G := fun g hg => ⟨g, hg, rfl⟩
  let e : G ≃ (φ '' G) × {g // g ∈ G ∧ τ g = g} :=
    { toFun := fun g => (⟨φ g.1, hmemφ g.1 g.2⟩,
        ⟨g.1 / s (φ g.1), hdivG _ g.2 _ (hs _ (hmemφ g.1 g.2)).1,
          key _ g.2 _ (hs _ (hmemφ g.1 g.2)).1 (hs _ (hmemφ g.1 g.2)).2.symm⟩)
      invFun := fun p => ⟨s p.1.1 * p.2.1, hmul _ (hs _ p.1.2).1 _ p.2.2.1⟩
      left_inv := fun g => Subtype.ext (by
        funext x
        simp only [Pi.mul_apply, Pi.div_apply]
        rw [mul_div_assoc']
        exact mul_div_cancel_left₀ _ (hne _ (hs _ (hmemφ g.1 g.2)).1 x))
      right_inv := fun p => by
        obtain ⟨⟨y, hy⟩, ⟨k, hkG, hkτ⟩⟩ := p
        have hφk : φ k = 1 := by
          funext x
          simp only [φ, Pi.div_apply, Pi.one_apply]
          rw [hkτ]; exact div_self (hne k hkG x)
        have hy' : φ (s y * k) = y := by rw [hφmul, (hs y hy).2, hφk, mul_one]
        refine Prod.ext ?_ ?_
        · exact Subtype.ext hy'
        · apply Subtype.ext
          show (s y * k) / s (φ (s y * k)) = k
          rw [hy']
          funext x
          simp only [Pi.mul_apply, Pi.div_apply]
          exact mul_div_cancel_left₀ _ (hne _ (hs y hy).1 x) }
  rw [Nat.card_congr e, Nat.card_prod]

/-- Step 7, first part (the identity `|(τ-1)G|·|G^τ| = |G|` used in s4_normfree.tex:137). -/
theorem thm_4_1_step7_part1 (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type*} [Field L] :
    Nat.card ((fun g => tauG n a g / g) '' (Ggrp n a 3 : Set (ZMod n → L))) *
        Nat.card {g : ZMod n → L // g ∈ (Ggrp n a 3 : Set (ZMod n → L)) ∧ tauG n a g = g} =
      Nat.card (Ggrp n a 3 : Set (ZMod n → L)) :=
  H12_first_iso (Ggrp n a 3) (tauG n a) (fun _g hg x => H12_G_ne hg x) (fun _g hg _g' hg' => H12_G_mul hg hg')
    (fun _g hg => H12_G_inv hg) (fun _g hg => H12_tau_G hn hodd h3 hg) H12_tau_mul H12_tau_inv

/-! ## 5. Remark 4.4, `n = 80`: `G ≅ μ_10`, `G^τ ≅ μ_2`, `(τ-1)G = G[5] ≅ μ_5` -/

section N80

variable {L : Type*} [Field L]

theorem H12_card_roots [IsAlgClosed L] (d : ℕ) (hd : (d : L) ≠ 0) : Nat.card {t : L // t ^ d = 1} = d := by
  have : NeZero (d : L) := ⟨hd⟩
  have hd0 : 0 < d := Nat.pos_of_ne_zero (fun h => hd (by rw [h, Nat.cast_zero]))
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot L d
  have e : {t : L // t ^ d = 1} ≃ {t : L // t ∈ Polynomial.nthRootsFinset d (1 : L)} :=
    Equiv.subtypeEquivRight (fun t => (Polynomial.mem_nthRootsFinset hd0 (1 : L)).symm)
  rw [Nat.card_congr e, Nat.card_eq_finsetCard, hζ.card_nthRootsFinset]

theorem H12_X80_iff (k : ZMod 80) : k ∈ layer0' 80 4 ↔ k = 16 ∨ k = 32 ∨ k = 48 ∨ k = 64 := by
  simp only [layer0', Finset.mem_filter, Finset.mem_univ, true_and]
  revert k
  decide

/-- The element of `G` (for `n = 80`) with value `t` at `α = ω^16`: the orbit is `16 → 48 → 64 → 32 → 16`. -/
def H12_gen (t : L) : ZMod 80 → L := fun k =>
  if k = 16 then t else if k = 48 then t ^ 3 else if k = 64 then t ^ 9 else if k = 32 then t ^ 27 else 1

theorem H12_gen_def (t : L) (k : ZMod 80) : H12_gen t k =
    if k = 16 then t else if k = 48 then t ^ 3 else if k = 64 then t ^ 9 else if k = 32 then t ^ 27 else 1 := rfl

theorem H12_gen16 (t : L) : H12_gen t 16 = t := by rw [H12_gen_def, ite_eq_left rfl]
theorem H12_gen48 (t : L) : H12_gen t 48 = t ^ 3 := by
  rw [H12_gen_def, ite_eq_right (by decide), ite_eq_left rfl]
theorem H12_gen64 (t : L) : H12_gen t 64 = t ^ 9 := by
  rw [H12_gen_def, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
theorem H12_gen32 (t : L) : H12_gen t 32 = t ^ 27 := by
  rw [H12_gen_def, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
theorem H12_gen_off (t : L) (k : ZMod 80) (hk : k ∉ layer0' 80 4) : H12_gen t k = 1 := by
  rw [H12_X80_iff] at hk
  push Not at hk
  rw [H12_gen_def, ite_eq_right hk.1, ite_eq_right hk.2.2.1, ite_eq_right hk.2.2.2, ite_eq_right hk.2.1]

theorem H12_m16 : (16 : ZMod 80) ∈ layer0' 80 4 := (H12_X80_iff 16).mpr (Or.inl rfl)

theorem H12_gen_mem (t : L) (ht : t ^ 10 = 1) : H12_gen t ∈ (Ggrp 80 4 3 : Set (ZMod 80 → L)) := by
  rw [H12_memG]
  refine ⟨fun k hk => ?_, fun k hk => H12_gen_off t k hk⟩
  rw [H12_X80_iff] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · rw [show (3 : ZMod 80) * 16 = 48 by decide, show -(16 : ZMod 80) = 64 by decide, H12_gen48, H12_gen64,
      H12_gen16]
    exact ⟨rfl, by linear_combination ht⟩
  · rw [show (3 : ZMod 80) * 32 = 16 by decide, show -(32 : ZMod 80) = 48 by decide, H12_gen48, H12_gen32,
      H12_gen16]
    exact ⟨by linear_combination (-t * (t ^ 70 + t ^ 60 + t ^ 50 + t ^ 40 + t ^ 30 + t ^ 20 + t ^ 10 + 1)) * ht,
      by linear_combination (t ^ 20 + t ^ 10 + 1) * ht⟩
  · rw [show (3 : ZMod 80) * 48 = 64 by decide, show -(48 : ZMod 80) = 32 by decide, H12_gen48, H12_gen64,
      H12_gen32]
    exact ⟨by ring, by linear_combination (t ^ 20 + t ^ 10 + 1) * ht⟩
  · rw [show (3 : ZMod 80) * 64 = 32 by decide, show -(64 : ZMod 80) = 16 by decide, H12_gen16, H12_gen64,
      H12_gen32]
    exact ⟨by ring, by linear_combination ht⟩

theorem H12_G80_eq (g : ZMod 80 → L) (hg : g ∈ (Ggrp 80 4 3 : Set (ZMod 80 → L))) :
    g 16 ^ 10 = 1 ∧ g = H12_gen (g 16) := by
  rw [H12_memG] at hg
  obtain ⟨h1, h2⟩ := hg
  have m48 : (48 : ZMod 80) ∈ layer0' 80 4 := (H12_X80_iff 48).mpr (by decide)
  have m64 : (64 : ZMod 80) ∈ layer0' 80 4 := (H12_X80_iff 64).mpr (by decide)
  have e48 : g 48 = g 16 ^ 3 := by
    have := (h1 16 H12_m16).1
    rwa [show (3 : ZMod 80) * 16 = 48 by decide] at this
  have e64 : g 64 = g 16 ^ 9 := by
    have := (h1 48 m48).1
    rw [show (3 : ZMod 80) * 48 = 64 by decide, e48] at this
    rw [this]; ring
  have e32 : g 32 = g 16 ^ 27 := by
    have := (h1 64 m64).1
    rw [show (3 : ZMod 80) * 64 = 32 by decide, e64] at this
    rw [this]; ring
  have h10 : g 16 ^ 10 = 1 := by
    have := (h1 16 H12_m16).2
    rw [show -(16 : ZMod 80) = 64 by decide, e64] at this
    rw [← this]; ring
  refine ⟨h10, funext fun k => ?_⟩
  by_cases hk : k ∈ layer0' 80 4
  · rw [H12_X80_iff] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · rw [H12_gen16]
    · rw [H12_gen32, e32]
    · rw [H12_gen48, e48]
    · rw [H12_gen64, e64]
  · rw [h2 k hk, H12_gen_off _ k hk]

theorem H12_G80_ext {g g' : ZMod 80 → L} (hg : g ∈ (Ggrp 80 4 3 : Set (ZMod 80 → L)))
    (hg' : g' ∈ (Ggrp 80 4 3 : Set (ZMod 80 → L))) (h : g 16 = g' 16) : g = g' := by
  rw [(H12_G80_eq g hg).2, (H12_G80_eq g' hg').2, h]

theorem H12_gen_pow5 (t : L) (ht : t ^ 5 = 1) : H12_gen t ^ 5 = 1 := by
  funext k
  rw [Pi.pow_apply, Pi.one_apply, H12_gen_def]
  split_ifs
  · exact ht
  · rw [← pow_mul, mul_comm, pow_mul, ht, one_pow]
  · rw [← pow_mul, mul_comm, pow_mul, ht, one_pow]
  · rw [← pow_mul, mul_comm, pow_mul, ht, one_pow]
  · exact one_pow 5

theorem H12_sq_pows {t : L} (h2 : t ^ 2 = 1) : t ^ 3 = t ∧ t ^ 9 = t ∧ t ^ 27 = t := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show t ^ 3 = (t ^ 2) * t by ring, h2, one_mul]
  · rw [show t ^ 9 = (t ^ 2) ^ 4 * t by ring, h2, one_pow, one_mul]
  · rw [show t ^ 27 = (t ^ 2) ^ 13 * t by ring, h2, one_pow, one_mul]

theorem H12_two_ne [CharP L 3] (d : ℕ) (hd : ¬ 3 ∣ d) : (d : L) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff L 3]
  exact hd

end N80

theorem rem_4_4_G_proved {L : Type*} [Field L] [CharP L 3] [IsAlgClosed L] :
    Nat.card (Ggrp 80 4 3 : Set (ZMod 80 → L)) = 10 ∧
      Nat.card {g : ZMod 80 → L // g ∈ (Ggrp 80 4 3 : Set (ZMod 80 → L)) ∧ tauG 80 4 g = g} = 2 ∧
      (fun g => tauG 80 4 g / g) '' (Ggrp 80 4 3 : Set (ZMod 80 → L)) =
        {g | g ∈ (Ggrp 80 4 3 : Set (ZMod 80 → L)) ∧ g ^ 5 = 1} ∧
      Nat.card {g : ZMod 80 → L // g ∈ (Ggrp 80 4 3 : Set (ZMod 80 → L)) ∧ g ^ 5 = 1} = 5 := by
  have hn : (80 : ℕ) = 2 ^ 4 * 5 := by norm_num
  have hodd : Odd 5 := by decide
  have h3 : ¬ 3 ∣ 80 := by decide
  -- the value of `τg/g` at `16`
  have hval : ∀ g : ZMod 80 → L, g ∈ (Ggrp 80 4 3 : Set (ZMod 80 → L)) →
      (tauG 80 4 g / g) 16 = g 16 ^ 27 / g 16 := by
    intro g hg
    simp only [Pi.div_apply]
    rw [H12_tau_mem g H12_m16, show (2 : ZMod 80) * 16 = 32 by decide]
    have e := congrFun (H12_G80_eq g hg).2 32
    rw [H12_gen32] at e
    rw [e]
  have hτdiv : ∀ g : ZMod 80 → L, g ∈ (Ggrp 80 4 3 : Set (ZMod 80 → L)) →
      tauG 80 4 g / g ∈ (Ggrp 80 4 3 : Set (ZMod 80 → L)) := fun g hg =>
    H12_G_div (H12_tau_G hn hodd h3 hg) hg
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `|G| = 10`
    have e : (Ggrp 80 4 3 : Set (ZMod 80 → L)) ≃ {t : L // t ^ 10 = 1} :=
      { toFun := fun g => ⟨g.1 16, (H12_G80_eq g.1 g.2).1⟩
        invFun := fun t => ⟨H12_gen t.1, H12_gen_mem t.1 t.2⟩
        left_inv := fun g => Subtype.ext (H12_G80_eq g.1 g.2).2.symm
        right_inv := fun t => Subtype.ext (H12_gen16 t.1) }
    rw [Nat.card_congr e]
    exact H12_card_roots 10 (H12_two_ne 10 (by decide))
  · -- `|G^τ| = 2`
    have e : {g : ZMod 80 → L // g ∈ (Ggrp 80 4 3 : Set (ZMod 80 → L)) ∧ tauG 80 4 g = g} ≃
        {t : L // t ^ 2 = 1} :=
      { toFun := fun g => ⟨g.1 16, by
          obtain ⟨hg, hτ⟩ := g.2
          have h10 := (H12_G80_eq g.1 hg).1
          have hne := H12_G_ne hg 16
          have e := hval g.1 hg
          rw [hτ] at e
          simp only [Pi.div_apply] at e
          rw [div_self hne, eq_comm, div_eq_one_iff_eq hne] at e
          have h26 : g.1 16 ^ 26 = 1 := by
            have h' : g.1 16 * (g.1 16 ^ 26 - 1) = 0 := by linear_combination e
            rcases mul_eq_zero.mp h' with h | h
            · exact absurd h hne
            · linear_combination h
          linear_combination
            (-(g.1 16) ^ 2 * ((g.1 16) ^ 40 + (g.1 16) ^ 30 + (g.1 16) ^ 20 + (g.1 16) ^ 10 + 1)) * h10
              + ((g.1 16) ^ 26 + 1) * h26⟩
        invFun := fun t => ⟨H12_gen t.1, by
          have h2 := t.2
          obtain ⟨p3, p9, p27⟩ := H12_sq_pows h2
          have h10 : t.1 ^ 10 = 1 := by
            linear_combination (t.1 ^ 8 + t.1 ^ 6 + t.1 ^ 4 + t.1 ^ 2 + 1) * h2
          refine ⟨H12_gen_mem t.1 h10, ?_⟩
          funext k
          by_cases hk : k ∈ layer0' 80 4
          · rw [H12_tau_mem _ hk]
            rw [H12_X80_iff] at hk
            rcases hk with rfl | rfl | rfl | rfl
            · rw [show (2 : ZMod 80) * 16 = 32 by decide, H12_gen32, H12_gen16, p27]
            · rw [show (2 : ZMod 80) * 32 = 64 by decide, H12_gen64, H12_gen32, p9, p27]
            · rw [show (2 : ZMod 80) * 48 = 16 by decide, H12_gen16, H12_gen48, p3]
            · rw [show (2 : ZMod 80) * 64 = 48 by decide, H12_gen48, H12_gen64, p3, p9]
          · rw [H12_tau_nmem _ hk, H12_gen_off _ k hk]⟩
        left_inv := fun g => Subtype.ext (H12_G80_eq g.1 g.2.1).2.symm
        right_inv := fun t => Subtype.ext (H12_gen16 t.1) }
    rw [Nat.card_congr e]
    exact H12_card_roots 2 (H12_two_ne 2 (by decide))
  · -- `(τ-1)G = G[5]`
    ext g
    constructor
    · rintro ⟨h, hh, rfl⟩
      show tauG 80 4 h / h ∈ (Ggrp 80 4 3 : Set (ZMod 80 → L)) ∧ (tauG 80 4 h / h) ^ 5 = 1
      refine ⟨hτdiv h hh, ?_⟩
      have h10 := (H12_G80_eq h hh).1
      have hne := H12_G_ne hh 16
      rw [(H12_G80_eq _ (hτdiv h hh)).2]
      apply H12_gen_pow5
      rw [hval h hh, div_pow, div_eq_one_iff_eq (pow_ne_zero _ hne), ← pow_mul,
        show 27 * 5 = 10 * 13 + 5 by norm_num, pow_add, pow_mul, h10, one_pow, one_mul]
    · rintro ⟨hg, hg5⟩
      refine ⟨g, hg, ?_⟩
      show tauG 80 4 g / g = g
      apply H12_G80_ext (hτdiv g hg) hg
      have h5 : g 16 ^ 5 = 1 := by
        have := congrFun hg5 16
        simpa using this
      have hne := H12_G_ne hg 16
      rw [hval g hg, div_eq_iff hne, show 27 = 5 * 5 + 2 by norm_num, pow_add, pow_mul, h5, one_pow,
        one_mul, sq]
  · -- `|G[5]| = 5`
    have e : {g : ZMod 80 → L // g ∈ (Ggrp 80 4 3 : Set (ZMod 80 → L)) ∧ g ^ 5 = 1} ≃ {t : L // t ^ 5 = 1} :=
      { toFun := fun g => ⟨g.1 16, by
          have := congrFun g.2.2 16
          simpa using this⟩
        invFun := fun t => ⟨H12_gen t.1, H12_gen_mem t.1 (by
            rw [show 10 = 5 * 2 by norm_num, pow_mul, t.2, one_pow]), H12_gen_pow5 t.1 t.2⟩
        left_inv := fun g => Subtype.ext (H12_G80_eq g.1 g.2.1).2.symm
        right_inv := fun t => Subtype.ext (H12_gen16 t.1) }
    rw [Nat.card_congr e]
    exact H12_card_roots 5 (H12_two_ne 5 (by decide))

/-! ## 6. Step 7, second part: `|K_n| = 4 ∏_i (3^{L_i}-1)`, given Steps 2 and 6

Plan (s4_normfree.tex:134-139, homogeneous laws). `K := {λ : (h1),(h3),(h4)}` is a group; `λ ↦ (λ(-1), λ(-1)·λ)` gives
`K ≃ {±1} × K₁`, `K₁ := {λ ∈ K : λ(-1) = 1}` (there (h4) reads `λ(ξ²) = λ(ξ)λ(-ξ)`). For `res : K₁ → 𝒟⁰` (restriction
to the top layer): `ker res ≃ {±1} × G^τ` and `res(K₁) = Π⁻¹((τ-1)G)`. Both use the layer products
`N_i(λ)(k) := ∏_{ρ ∈ 𝓛_a, 2^i ρ = k} λ(ρ)`, with `N_{i+1}(2k) = N_i(k) N_i(k+m)`; the descent is `λ(2^i z) = N_i(λ)(2^i z)`
(`z` odd, `i ≤ a-1`), and an extension of `λ₀ ∈ Π⁻¹((τ-1)G)`, `Π λ₀ = τg/g`, is `λ := M(λ₀)·g`, `M := ∏_{i<a} N_i`.
Then `|K| = 2·(2|G^τ|)·|ker Π|·|(τ-1)G| = 4|ker Π|·|G| = 4|𝒟⁰|` by the first part. -/

section Count

variable {n a nodd : ℕ} [NeZero n] {L : Type*} [Field L]

theorem H12_two_dvd (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) : 2 ∣ n := by
  rw [hn]; exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _

theorem H12_four_dvd (hn : n = 2 ^ a * nodd) (ha : 2 ≤ a) : 4 ∣ n := by
  rw [hn, show (4 : ℕ) = 2 ^ 2 by norm_num]; exact Dvd.dvd.mul_right (pow_dvd_pow 2 ha) _

theorem H12_mem_topLayer (k : ZMod n) : k ∈ topLayer n ↔ Odd k.val := by
  simp only [topLayer, Finset.mem_filter, Finset.mem_univ, true_and]

theorem H12_odd_iff (h2 : 2 ∣ n) (x : ZMod n) : Odd x.val ↔ ZMod.castHom h2 (ZMod 2) x = 1 := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_one_iff_odd]

theorem H12_mem_top (h2 : 2 ∣ n) (x : ZMod n) : x ∈ topLayer n ↔ ZMod.castHom h2 (ZMod 2) x = 1 := by
  rw [H12_mem_topLayer, H12_odd_iff h2]

theorem H12_half_val : (half n : ZMod n).val = n / 2 := by
  unfold half
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.div_lt_self (Nat.pos_of_ne_zero (NeZero.ne n)) one_lt_two)]

theorem H12_two_mul_half (h2 : 2 ∣ n) : (2 : ZMod n) * half n = 0 := by
  unfold half
  have h : ((2 * (n / 2) : ℕ) : ZMod n) = 0 := by
    rw [Nat.mul_div_cancel' h2]; exact ZMod.natCast_self n
  push_cast at h; exact h

theorem H12_half_ne (h2 : 2 ∣ n) : (half n : ZMod n) ≠ 0 := by
  intro h
  have e := H12_half_val (n := n)
  rw [h, ZMod.val_zero] at e
  have hn0 : n ≠ 0 := NeZero.ne n
  obtain ⟨c, hc⟩ := h2
  omega

theorem H12_neg_half (h2 : 2 ∣ n) : -(half n : ZMod n) = half n := by
  linear_combination -(H12_two_mul_half h2)

theorem H12_psi_half (h2 : 2 ∣ n) (h4 : 4 ∣ n) : ZMod.castHom h2 (ZMod 2) (half n) = 0 := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, H12_half_val, ZMod.natCast_eq_zero_iff_even]
  obtain ⟨c, hc⟩ := h4
  exact ⟨c, by omega⟩

theorem H12_ker_two (h2 : 2 ∣ n) (w : ZMod n) (hw : 2 * w = 0) : w = 0 ∨ w = half n := by
  have hv : n ∣ 2 * w.val := by
    rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [ZMod.natCast_zmod_val]; exact hw
  have hlt := ZMod.val_lt w
  obtain ⟨c, hc⟩ := hv
  have hc2 : c < 2 := by
    by_contra hcon
    push Not at hcon
    have : n * 2 ≤ n * c := Nat.mul_le_mul_left n hcon
    linarith
  interval_cases c
  · left; rw [← ZMod.val_eq_zero]; omega
  · right; apply ZMod.val_injective; rw [H12_half_val]; omega

theorem H12_n_div2 (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) : n / 2 = 2 ^ (a - 1) * nodd := by
  have e : n = 2 * (2 ^ (a - 1) * nodd) := by
    rw [hn, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel ha]
  rw [e, Nat.mul_div_cancel_left _ two_pos]

theorem H12_half_eq (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) :
    (half n : ZMod n) = (2 : ZMod n) ^ (a - 1) * nodd := by
  unfold half
  rw [H12_n_div2 hn ha, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem H12_nodd_half (hodd : Odd nodd) (h2 : 2 ∣ n) : (nodd : ZMod n) * half n = half n := by
  obtain ⟨r, hr⟩ := hodd
  rw [hr]; push_cast
  linear_combination (r : ZMod n) * H12_two_mul_half h2

theorem H12_half_mul_odd (h2 : 2 ∣ n) {x : ZMod n} (hx : ZMod.castHom h2 (ZMod 2) x = 1) :
    half n * x = half n := by
  obtain ⟨j, hj⟩ := (H12_odd_iff h2 x).mpr hx
  rw [← ZMod.natCast_zmod_val x, hj]
  push_cast
  linear_combination (j : ZMod n) * H12_two_mul_half h2

theorem H12_Y_iff (hn : n = 2 ^ a * nodd) (hodd : Odd nodd) (k : ZMod n) :
    2 ^ a ∣ k.val ↔ (nodd : ZMod n) * k = 0 := by
  constructor
  · exact H12_nodd_mul hn k
  · intro h
    have h' : n ∣ nodd * k.val := by
      rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [ZMod.natCast_zmod_val]; exact h
    obtain ⟨c, hc⟩ := h'
    refine ⟨c, ?_⟩
    have e : nodd * k.val = nodd * (2 ^ a * c) := by rw [hc, hn]; ring
    exact Nat.eq_of_mul_eq_mul_left hodd.pos e

theorem H12_mem_X' (hn : n = 2 ^ a * nodd) (hodd : Odd nodd) {k : ZMod n} :
    k ∈ layer0' n a ↔ (nodd : ZMod n) * k = 0 ∧ k ≠ 0 := by
  rw [H12_mem_X, H12_Y_iff hn hodd]

theorem H12_top_notY (h2 : 2 ∣ n) (hodd : Odd nodd) {k : ZMod n} (hk : k ∈ topLayer n) :
    (nodd : ZMod n) * k ≠ 0 := by
  intro h
  have e := congrArg (ZMod.castHom h2 (ZMod 2)) h
  rw [map_mul, map_natCast, (H12_mem_top h2 k).mp hk, mul_one, map_zero,
    (ZMod.natCast_eq_one_iff_odd).mpr hodd] at e
  exact absurd e (by decide)

theorem H12_inv3 (h3 : ¬ 3 ∣ n) : ∃ v : ZMod n, v * 3 = 1 := by
  obtain ⟨u, hu⟩ := H12_isUnit3 h3
  exact ⟨↑u⁻¹, by rw [← hu, Units.inv_mul]⟩

/-- `2^{a-1-i}·n_odd·(2^i ρ) = m` for odd `ρ`, `i ≤ a-1`. -/
theorem H12_theta (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) (h2 : 2 ∣ n) {i : ℕ} (hi : i ≤ a - 1) {ρ : ZMod n}
    (hρ : ZMod.castHom h2 (ZMod 2) ρ = 1) :
    (2 : ZMod n) ^ (a - 1 - i) * nodd * ((2 : ZMod n) ^ i * ρ) = half n := by
  obtain ⟨j, hj⟩ : ∃ j, a - 1 = j + i := ⟨a - 1 - i, by omega⟩
  have hj' : a - 1 - i = j := by omega
  have e : (2 : ZMod n) ^ (a - 1 - i) * nodd * ((2 : ZMod n) ^ i * ρ) = ((2 : ZMod n) ^ (a - 1) * nodd) * ρ := by
    rw [hj', hj, pow_add]; ring
  rw [e, ← H12_half_eq hn ha, H12_half_mul_odd h2 hρ]

theorem H12_T1 (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) (h2 : 2 ∣ n) {i : ℕ} (hi : i ≤ a - 1) {ρ : ZMod n}
    (hρ : ZMod.castHom h2 (ZMod 2) ρ = 1) {k : ZMod n} (hk : (nodd : ZMod n) * k = 0) :
    (2 : ZMod n) ^ i * ρ ≠ k := by
  intro h
  have e := H12_theta hn ha h2 hi hρ
  rw [h, mul_assoc, hk, mul_zero] at e
  exact H12_half_ne h2 e.symm

theorem H12_T2 (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) (hodd : Odd nodd) (h2 : 2 ∣ n) {i : ℕ} (hi : i < a - 1)
    {ρ : ZMod n} (hρ : ZMod.castHom h2 (ZMod 2) ρ = 1) {k : ZMod n} (hk : (nodd : ZMod n) * k = 0) :
    (2 : ZMod n) ^ i * ρ ≠ k + half n := by
  intro h
  have e := H12_theta hn ha h2 hi.le hρ
  rw [h, mul_assoc, mul_add, hk, zero_add, H12_nodd_half hodd h2] at e
  obtain ⟨j, hj⟩ : ∃ j, a - 1 - i = j + 1 := ⟨a - 2 - i, by omega⟩
  rw [hj, pow_succ, mul_assoc, H12_two_mul_half h2, mul_zero] at e
  exact H12_half_ne h2 e.symm

theorem H12_T3 (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) (hodd : Odd nodd) (h2 : 2 ∣ n) {ρ : ZMod n}
    (hρ : ZMod.castHom h2 (ZMod 2) ρ = 1) {k : ZMod n} (h : (2 : ZMod n) ^ (a - 1) * ρ = k) :
    (nodd : ZMod n) * (k + half n) = 0 := by
  have e := H12_theta hn ha h2 (le_refl (a - 1)) hρ
  rw [Nat.sub_self, pow_zero, one_mul, h] at e
  rw [mul_add, e, H12_nodd_half hodd h2]
  linear_combination H12_two_mul_half h2

theorem H12_T5 (hodd : Odd nodd) (h2 : 2 ∣ n) {k : ZMod n} (hk : (nodd : ZMod n) * k ≠ 0)
    (h2k : (nodd : ZMod n) * (2 * k) = 0) : (nodd : ZMod n) * (k + half n) = 0 := by
  rw [mul_left_comm] at h2k
  rcases H12_ker_two h2 _ h2k with h | h
  · exact absurd h hk
  · rw [mul_add, h, H12_nodd_half hodd h2]; linear_combination H12_two_mul_half h2

/-- Every `k ∉ μ_{n_odd}` is `2^i z` with `z` odd and `i < a`. -/
theorem H12_decomp (hn : n = 2 ^ a * nodd) (hodd : Odd nodd) (h2 : 2 ∣ n) (k : ZMod n)
    (hk : (nodd : ZMod n) * k ≠ 0) :
    ∃ i < a, ∃ z : ZMod n, ZMod.castHom h2 (ZMod 2) z = 1 ∧ k = (2 : ZMod n) ^ i * z := by
  have hk0 : k.val ≠ 0 := by
    intro h; apply hk; rw [(ZMod.val_eq_zero k).mp h, mul_zero]
  obtain ⟨i, w, hw, hkw⟩ := Nat.exists_eq_two_pow_mul_odd hk0
  refine ⟨i, ?_, (w : ZMod n), ?_, ?_⟩
  · by_contra hia
    push Not at hia
    apply hk
    rw [← H12_Y_iff hn hodd, hkw]
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 hia) w
  · rw [map_natCast]; exact (ZMod.natCast_eq_one_iff_odd).mpr hw
  · rw [← ZMod.natCast_zmod_val k, hkw, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

/-! ### The layer products `N_i` -/

/-- `N_i(λ)(k) := ∏_{ρ ∈ 𝓛_a, 2^i ρ = k} λ(ρ)`. -/
noncomputable def H12_N (lam : ZMod n → L) (i : ℕ) (k : ZMod n) : L :=
  ∏ ρ ∈ (topLayer n).filter (fun ρ => (2 : ZMod n) ^ i * ρ = k), lam ρ

theorem H12_N_succ (h2 : 2 ∣ n) (lam : ZMod n → L) (i : ℕ) (k : ZMod n) :
    H12_N lam (i + 1) (2 * k) = H12_N lam i k * H12_N lam i (k + half n) := by
  unfold H12_N
  rw [← Finset.prod_union]
  · apply Finset.prod_congr _ (fun _ _ => rfl)
    ext ρ
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hρ, h⟩
      have h' : 2 * ((2 : ZMod n) ^ i * ρ - k) = 0 := by
        rw [mul_sub, ← mul_assoc, ← pow_succ', h, sub_self]
      rcases H12_ker_two h2 _ h' with e | e
      · exact Or.inl ⟨hρ, sub_eq_zero.mp e⟩
      · exact Or.inr ⟨hρ, by rw [← e]; ring⟩
    · rintro (⟨hρ, h⟩ | ⟨hρ, h⟩)
      · exact ⟨hρ, by rw [pow_succ', mul_assoc, h]⟩
      · refine ⟨hρ, ?_⟩
        rw [pow_succ', mul_assoc, h, mul_add, H12_two_mul_half h2, add_zero]
  · rw [Finset.disjoint_filter]
    intro ρ _ h1 h2'
    apply H12_half_ne h2
    have e := h1.symm.trans h2'
    linear_combination -e

theorem H12_N_zero_odd (lam : ZMod n → L) {k : ZMod n} (hk : k ∈ topLayer n) : H12_N lam 0 k = lam k := by
  unfold H12_N
  simp only [pow_zero, one_mul]
  rw [Finset.filter_eq', ite_eq_left hk, Finset.prod_singleton]

theorem H12_N_one (lam : ZMod n → L) (i : ℕ) (k : ZMod n) (h : ∀ ρ ∈ topLayer n, (2 : ZMod n) ^ i * ρ ≠ k) :
    H12_N lam i k = 1 := by
  unfold H12_N
  apply Finset.prod_eq_one
  intro ρ hρ
  rw [Finset.mem_filter] at hρ
  exact absurd hρ.2 (h ρ hρ.1)

theorem H12_N_allone {lam : ZMod n → L} (h : ∀ ρ ∈ topLayer n, lam ρ = 1) (i : ℕ) (k : ZMod n) :
    H12_N lam i k = 1 := by
  unfold H12_N
  exact Finset.prod_eq_one (fun ρ hρ => h ρ (Finset.mem_filter.mp hρ).1)

theorem H12_N_congr {lam lam' : ZMod n → L} (h : ∀ ρ ∈ topLayer n, lam ρ = lam' ρ) (i : ℕ) (k : ZMod n) :
    H12_N lam i k = H12_N lam' i k := by
  unfold H12_N
  exact Finset.prod_congr rfl (fun ρ hρ => h ρ (Finset.mem_filter.mp hρ).1)

theorem H12_N_three (h2 : 2 ∣ n) (h3 : ¬ 3 ∣ n) (lam : ZMod n → L)
    (hlam : ∀ ρ ∈ topLayer n, lam (3 * ρ) = lam ρ ^ 3) (i : ℕ) (k : ZMod n) :
    H12_N lam i (3 * k) = H12_N lam i k ^ 3 := by
  obtain ⟨v, hv⟩ := H12_inv3 h3
  have hψ3 : ZMod.castHom h2 (ZMod 2) 3 = 1 := by rw [map_ofNat]; decide
  have hψv : ZMod.castHom h2 (ZMod 2) v = 1 := by
    have e := congrArg (ZMod.castHom h2 (ZMod 2)) hv
    rw [map_mul, map_one, hψ3, mul_one] at e; exact e
  unfold H12_N
  rw [← Finset.prod_pow]
  apply Finset.prod_nbij' (fun ρ => v * ρ) (fun ρ => 3 * ρ)
  · intro ρ hρ
    rw [Finset.mem_filter, H12_mem_top h2] at hρ ⊢
    refine ⟨by rw [map_mul, hψv, hρ.1, one_mul], ?_⟩
    rw [mul_left_comm, hρ.2, ← mul_assoc, hv, one_mul]
  · intro ρ hρ
    rw [Finset.mem_filter, H12_mem_top h2] at hρ ⊢
    refine ⟨by rw [map_mul, hψ3, hρ.1, one_mul], ?_⟩
    rw [mul_left_comm, hρ.2]
  · intro ρ _; rw [← mul_assoc, mul_comm 3 v, hv, one_mul]
  · intro ρ _; rw [← mul_assoc, hv, one_mul]
  · intro ρ hρ
    have hvρ : v * ρ ∈ topLayer n := by
      rw [Finset.mem_filter, H12_mem_top h2] at hρ
      rw [H12_mem_top h2, map_mul, hψv, hρ.1, one_mul]
    rw [← hlam _ hvρ, ← mul_assoc, mul_comm 3 v, hv, one_mul]

theorem H12_N_neg (h2 : 2 ∣ n) (lam : ZMod n → L) (hlam : ∀ ρ ∈ topLayer n, lam ρ * lam (-ρ) = 1)
    (i : ℕ) (k : ZMod n) : H12_N lam i k * H12_N lam i (-k) = 1 := by
  have hneg : H12_N lam i (-k) =
      ∏ ρ ∈ (topLayer n).filter (fun ρ => (2 : ZMod n) ^ i * ρ = k), lam (-ρ) := by
    unfold H12_N
    apply Finset.prod_nbij' (fun ρ => -ρ) (fun ρ => -ρ)
    · intro ρ hρ
      rw [Finset.mem_filter, H12_mem_top h2] at hρ ⊢
      exact ⟨by rw [map_neg, hρ.1]; decide, by rw [mul_neg, hρ.2, neg_neg]⟩
    · intro ρ hρ
      rw [Finset.mem_filter, H12_mem_top h2] at hρ ⊢
      exact ⟨by rw [map_neg, hρ.1]; decide, by rw [mul_neg, hρ.2]⟩
    · intro ρ _; exact neg_neg ρ
    · intro ρ _; exact neg_neg ρ
    · intro ρ _; rw [neg_neg]
  rw [hneg]
  unfold H12_N
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one (fun ρ hρ => hlam ρ (Finset.mem_filter.mp hρ).1)

/-- If `-k = k`, the product pairs `ρ` with `-ρ` (s4_normfree.tex:84-86: `∏_{Ξ_a} = 1`). -/
theorem H12_N_negself (h2 : 2 ∣ n) (h4 : 4 ∣ n) (lam : ZMod n → L)
    (hlam : ∀ ρ ∈ topLayer n, lam ρ * lam (-ρ) = 1) (i : ℕ) {k : ZMod n} (hk : -k = k) :
    H12_N lam i k = 1 := by
  unfold H12_N
  apply Finset.prod_involution (fun ρ _ => -ρ)
  · intro ρ hρ; exact hlam ρ (Finset.mem_filter.mp hρ).1
  · intro ρ hρ _ h
    have hρ' := (H12_mem_top h2 ρ).mp (Finset.mem_filter.mp hρ).1
    have e : 2 * ρ = 0 := by linear_combination -h
    rcases H12_ker_two h2 ρ e with e' | e'
    · rw [e', map_zero] at hρ'; exact absurd hρ' (by decide)
    · rw [e', H12_psi_half h2 h4] at hρ'; exact absurd hρ' (by decide)
  · intro ρ _; exact neg_neg ρ
  · intro ρ hρ
    rw [Finset.mem_filter] at hρ ⊢
    refine ⟨?_, by rw [mul_neg, hρ.2, hk]⟩
    rw [H12_mem_top h2] at hρ ⊢
    rw [map_neg, hρ.1]; decide

theorem H12_Pmap_eq (lam0 : ZMod n → L) {α : ZMod n} (hα : α ∈ layer0' n a) :
    Pmap n a lam0 α = H12_N lam0 (a - 1) (α + half n) := by
  simp only [Pmap, H12_N, ite_eq_left hα]

theorem H12_Pmap_off (lam0 : ZMod n → L) {α : ZMod n} (hα : α ∉ layer0' n a) : Pmap n a lam0 α = 1 := by
  simp only [Pmap, ite_eq_right hα]

theorem H12_Pmap_inv (lam : ZMod n → L) : Pmap n a lam⁻¹ = (Pmap n a lam)⁻¹ := by
  funext k
  by_cases hk : k ∈ layer0' n a
  · simp only [Pmap, ite_eq_left hk, Pi.inv_apply]
    rw [Finset.prod_inv_distrib]
  · simp only [Pmap, ite_eq_right hk, Pi.inv_apply, inv_one]

/-! ### `K`, `K₁`, the restriction `res` -/

/-- The homogeneous laws (h1), (h3), (h4) on all of `μ_n` (the set `K_n`). -/
def H12_K (lam : ZMod n → L) : Prop :=
  (∀ k, lam (3 * k) = lam k ^ 3) ∧ (∀ k, lam k * lam (-k) = 1) ∧
    ∀ k, lam k * lam (k + half n) = lam (half n) * lam (2 * k)

/-- `K₁ := {λ ∈ K : λ(-1) = 1}`. -/
def H12_K1 : Set (ZMod n → L) := {lam | H12_K lam ∧ lam (half n) = 1}

/-- Restriction to the top layer (value 1 elsewhere). -/
noncomputable def H12_res (lam : ZMod n → L) : ZMod n → L := fun k => if k ∈ topLayer n then lam k else 1

theorem H12_K_ne {lam : ZMod n → L} (hK : H12_K lam) (k : ZMod n) : lam k ≠ 0 :=
  left_ne_zero_of_mul_eq_one (hK.2.1 k)

theorem H12_res_top (lam : ZMod n → L) : ∀ ρ ∈ topLayer n, H12_res lam ρ = lam ρ := by
  intro ρ hρ; simp only [H12_res, ite_eq_left hρ]

theorem H12_res_mul (x y : ZMod n → L) : H12_res (x * y) = H12_res x * H12_res y := by
  funext k
  by_cases hk : k ∈ topLayer n
  · simp only [H12_res, ite_eq_left hk, Pi.mul_apply]
  · simp only [H12_res, ite_eq_right hk, Pi.mul_apply, mul_one]

theorem H12_res_inv (x : ZMod n → L) : H12_res x⁻¹ = (H12_res x)⁻¹ := by
  funext k
  by_cases hk : k ∈ topLayer n
  · simp only [H12_res, ite_eq_left hk, Pi.inv_apply]
  · simp only [H12_res, ite_eq_right hk, Pi.inv_apply, inv_one]

theorem H12_K1_mul {x y : ZMod n → L} (hx : x ∈ (H12_K1 : Set (ZMod n → L)))
    (hy : y ∈ (H12_K1 : Set (ZMod n → L))) : x * y ∈ (H12_K1 : Set (ZMod n → L)) := by
  obtain ⟨⟨x1, x3, x4⟩, xm⟩ := hx
  obtain ⟨⟨y1, y3, y4⟩, ym⟩ := hy
  refine ⟨⟨fun k => ?_, fun k => ?_, fun k => ?_⟩, ?_⟩
  · simp only [Pi.mul_apply]; rw [x1, y1, mul_pow]
  · simp only [Pi.mul_apply]; linear_combination (y k * y (-k)) * x3 k + y3 k
  · simp only [Pi.mul_apply]
    linear_combination (y k * y (k + half n)) * x4 k + (x (half n) * x (2 * k)) * y4 k
  · simp only [Pi.mul_apply]; rw [xm, ym, one_mul]

theorem H12_K1_inv {x : ZMod n → L} (hx : x ∈ (H12_K1 : Set (ZMod n → L))) :
    x⁻¹ ∈ (H12_K1 : Set (ZMod n → L)) := by
  obtain ⟨⟨x1, x3, x4⟩, xm⟩ := hx
  refine ⟨⟨fun k => ?_, fun k => ?_, fun k => ?_⟩, ?_⟩
  · simp only [Pi.inv_apply]; rw [x1, inv_pow]
  · simp only [Pi.inv_apply]; rw [← mul_inv, x3, inv_one]
  · simp only [Pi.inv_apply]; rw [← mul_inv, ← mul_inv, x4]
  · simp only [Pi.inv_apply]; rw [xm, inv_one]

theorem H12_memD0 {lam : ZMod n → L} : lam ∈ (topData0 n 3 : Set (ZMod n → L)) ↔
    (∀ k : ZMod n, Odd k.val → lam (3 * k) = lam k ^ 3 ∧ lam k * lam (-k) = 1) ∧
      ∀ k : ZMod n, Even k.val → lam k = 1 := by
  simp only [topData0, Set.mem_ofPred_eq, Nat.cast_ofNat]

theorem H12_D0_ne {lam0 : ZMod n → L} (hD : lam0 ∈ (topData0 n 3 : Set (ZMod n → L))) (k : ZMod n) :
    lam0 k ≠ 0 := by
  obtain ⟨h1, h2'⟩ := H12_memD0.mp hD
  rcases Nat.even_or_odd k.val with he | ho
  · rw [h2' k he]; exact one_ne_zero
  · exact left_ne_zero_of_mul_eq_one (h1 k ho).2

theorem H12_res_D0 (h2 : 2 ∣ n) {lam : ZMod n → L} (hK : H12_K lam) :
    H12_res lam ∈ (topData0 n 3 : Set (ZMod n → L)) := by
  rw [H12_memD0]
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · have hk' : k ∈ topLayer n := (H12_mem_topLayer k).mpr hk
    have h3k : 3 * k ∈ topLayer n := by
      rw [H12_mem_top h2] at hk' ⊢; rw [map_mul, hk', map_ofNat, mul_one]; decide
    have hnk : -k ∈ topLayer n := by
      rw [H12_mem_top h2] at hk' ⊢; rw [map_neg, hk']; decide
    simp only [H12_res, ite_eq_left hk', ite_eq_left h3k, ite_eq_left hnk]
    exact ⟨hK.1 k, hK.2.1 k⟩
  · have hk' : k ∉ topLayer n := by rw [H12_mem_topLayer]; exact Nat.not_odd_iff_even.mpr hk
    simp only [H12_res, ite_eq_right hk']

/-! ### The descent (s4_normfree.tex:80-83) -/

theorem H12_descent (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (_hodd : Odd nodd) (h2 : 2 ∣ n) {lam : ZMod n → L}
    (hK : H12_K lam) (hm1 : lam (half n) = 1) :
    ∀ i, i ≤ a - 1 → ∀ z : ZMod n, ZMod.castHom h2 (ZMod 2) z = 1 →
      lam ((2 : ZMod n) ^ i * z) = H12_N lam i ((2 : ZMod n) ^ i * z) := by
  have h4' : ∀ x, lam (2 * x) = lam x * lam (x + half n) := fun x => by
    have e := hK.2.2 x; rw [hm1, one_mul] at e; exact e.symm
  intro i
  induction i with
  | zero =>
    intro _ z hz
    rw [pow_zero, one_mul, H12_N_zero_odd lam ((H12_mem_top h2 z).mpr hz)]
  | succ i ih =>
    intro hi z hz
    have e1 : (2 : ZMod n) ^ (i + 1) * z = 2 * ((2 : ZMod n) ^ i * z) := by rw [pow_succ', mul_assoc]
    have e2 : (2 : ZMod n) ^ i * z + half n = (2 : ZMod n) ^ i * (z + (2 : ZMod n) ^ (a - 1 - i) * nodd) := by
      rw [mul_add, H12_half_eq hn (by omega), ← mul_assoc, ← pow_add, show i + (a - 1 - i) = a - 1 by omega]
    have hz' : ZMod.castHom h2 (ZMod 2) (z + (2 : ZMod n) ^ (a - 1 - i) * nodd) = 1 := by
      obtain ⟨j, hj⟩ : ∃ j, a - 1 - i = j + 1 := ⟨a - 2 - i, by omega⟩
      have h20 : (2 : ZMod 2) = 0 := by decide
      rw [map_add, map_mul, map_pow, map_ofNat, map_natCast, hz, hj, pow_succ, h20, mul_zero, zero_mul,
        add_zero]
    rw [e1, h4', H12_N_succ h2, ih (by omega) z hz, e2, ih (by omega) _ hz']

theorem H12_C1 (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h2 : 2 ∣ n) {lam : ZMod n → L}
    (hK : H12_K lam) (hm1 : lam (half n) = 1) {α : ZMod n} (hα : (nodd : ZMod n) * α = 0) :
    lam (α + half n) = H12_N lam (a - 1) (α + half n) := by
  have hY : (nodd : ZMod n) * (α + half n) ≠ 0 := by
    rw [mul_add, hα, zero_add, H12_nodd_half hodd h2]; exact H12_half_ne h2
  obtain ⟨i, hi, z, hz, hzk⟩ := H12_decomp hn hodd h2 _ hY
  have hia : i = a - 1 := by
    by_contra hne
    exact H12_T2 hn (by omega) hodd h2 (by omega : i < a - 1) hz hα hzk.symm
  subst hia
  rw [hzk]
  exact H12_descent hn ha hodd h2 hK hm1 (a - 1) le_rfl z hz

theorem H12_C2 (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h2 : 2 ∣ n) {lam : ZMod n → L}
    (hK : H12_K lam) (hm1 : lam (half n) = 1) (h1 : ∀ ρ ∈ topLayer n, lam ρ = 1) {k : ZMod n}
    (hk : (nodd : ZMod n) * k ≠ 0) : lam k = 1 := by
  obtain ⟨i, hi, z, hz, hzk⟩ := H12_decomp hn hodd h2 _ hk
  rw [hzk, H12_descent hn ha hodd h2 hK hm1 i (by omega) z hz, H12_N_allone h1]

/-! ### The extension `λ := M(λ₀)·g` -/

/-- `M(λ₀)(k) := ∏_{i<a} N_i(λ₀)(k)`. -/
noncomputable def H12_M (a : ℕ) (lam0 : ZMod n → L) (k : ZMod n) : L := ∏ i ∈ range a, H12_N lam0 i k

theorem H12_M_Y (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) (h2 : 2 ∣ n) (lam0 : ZMod n → L) {k : ZMod n}
    (hk : (nodd : ZMod n) * k = 0) : H12_M a lam0 k = 1 := by
  unfold H12_M
  apply Finset.prod_eq_one
  intro i hi
  apply H12_N_one
  intro ρ hρ
  exact H12_T1 hn ha h2 (by have := Finset.mem_range.mp hi; omega) ((H12_mem_top h2 ρ).mp hρ) hk

theorem H12_M_top (ha : 1 ≤ a) (h2 : 2 ∣ n) (lam0 : ZMod n → L) {k : ZMod n} (hk : k ∈ topLayer n) :
    H12_M a lam0 k = lam0 k := by
  unfold H12_M
  rw [show range a = range (a - 1 + 1) by congr 1; omega, Finset.prod_range_succ',
    H12_N_zero_odd lam0 hk, Finset.prod_eq_one, one_mul]
  intro i _
  apply H12_N_one
  intro ρ _ h
  have hk' := (H12_mem_top h2 k).mp hk
  rw [← h, map_mul, map_pow, map_ofNat, pow_succ, show (2 : ZMod 2) = 0 by decide, mul_zero, zero_mul] at hk'
  exact absurd hk' (by decide)

theorem H12_M_three (h2 : 2 ∣ n) (h3 : ¬ 3 ∣ n) (lam0 : ZMod n → L)
    (hlam : ∀ ρ ∈ topLayer n, lam0 (3 * ρ) = lam0 ρ ^ 3) (k : ZMod n) :
    H12_M a lam0 (3 * k) = H12_M a lam0 k ^ 3 := by
  unfold H12_M
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl (fun i _ => H12_N_three h2 h3 lam0 hlam i k)

theorem H12_M_neg (h2 : 2 ∣ n) (lam0 : ZMod n → L) (hlam : ∀ ρ ∈ topLayer n, lam0 ρ * lam0 (-ρ) = 1)
    (k : ZMod n) : H12_M a lam0 k * H12_M a lam0 (-k) = 1 := by
  unfold H12_M
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one (fun i _ => H12_N_neg h2 lam0 hlam i k)

theorem H12_M_half (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) (hodd : Odd nodd) (h2 : 2 ∣ n) (lam0 : ZMod n → L)
    {α : ZMod n} (hα : (nodd : ZMod n) * α = 0) :
    H12_M a lam0 (α + half n) = H12_N lam0 (a - 1) (α + half n) := by
  unfold H12_M
  rw [show range a = range (a - 1 + 1) by congr 1; omega, Finset.prod_range_succ, Finset.prod_eq_one, one_mul]
  intro i hi
  apply H12_N_one
  intro ρ hρ
  exact H12_T2 hn ha hodd h2 (Finset.mem_range.mp hi) ((H12_mem_top h2 ρ).mp hρ) hα

theorem H12_M_two (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) (hodd : Odd nodd) (h2 : 2 ∣ n) (lam0 : ZMod n → L)
    {k : ZMod n} (hk : (nodd : ZMod n) * k ≠ 0) (hkm : (nodd : ZMod n) * (k + half n) ≠ 0) :
    H12_M a lam0 (2 * k) = H12_M a lam0 k * H12_M a lam0 (k + half n) := by
  unfold H12_M
  rw [show range a = range (a - 1 + 1) by congr 1; omega]
  rw [Finset.prod_range_succ' (fun i => H12_N lam0 i (2 * k)), Finset.prod_range_succ (fun i => H12_N lam0 i k),
    Finset.prod_range_succ (fun i => H12_N lam0 i (k + half n))]
  have e0 : H12_N lam0 0 (2 * k) = 1 := by
    apply H12_N_one
    intro ρ hρ h
    have hρ' := (H12_mem_top h2 ρ).mp hρ
    have e := congrArg (ZMod.castHom h2 (ZMod 2)) h
    rw [pow_zero, one_mul, map_mul, map_ofNat, hρ', show (2 : ZMod 2) = 0 by decide, zero_mul] at e
    exact absurd e (by decide)
  have eL : H12_N lam0 (a - 1) k = 1 := by
    apply H12_N_one
    intro ρ hρ h
    exact hkm (H12_T3 hn ha hodd h2 ((H12_mem_top h2 ρ).mp hρ) h)
  have eR : H12_N lam0 (a - 1) (k + half n) = 1 := by
    apply H12_N_one
    intro ρ hρ h
    have e := H12_T3 hn ha hodd h2 ((H12_mem_top h2 ρ).mp hρ) h
    rw [add_assoc, ← two_mul, H12_two_mul_half h2, add_zero] at e
    exact hk e
  rw [e0, eL, eR, mul_one, mul_one, mul_one, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun i _ => H12_N_succ h2 lam0 i k)

theorem H12_G3all (hn : n = 2 ^ a * nodd) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n) {g : ZMod n → L}
    (hg : g ∈ (Ggrp n a 3 : Set (ZMod n → L))) (k : ZMod n) : g (3 * k) = g k ^ 3 := by
  by_cases hk : k ∈ layer0' n a
  · exact ((H12_memG.mp hg).1 k hk).1
  · have h3k : 3 * k ∉ layer0' n a := by
      intro h; apply hk
      rw [H12_mem_X' hn hodd] at h ⊢
      obtain ⟨v, hv⟩ := H12_inv3 h3
      refine ⟨?_, fun h0 => h.2 (by rw [h0, mul_zero])⟩
      have e : k = v * (3 * k) := by rw [← mul_assoc, hv, one_mul]
      rw [e, mul_left_comm, h.1, mul_zero]
    rw [(H12_memG.mp hg).2 k hk, (H12_memG.mp hg).2 _ h3k, one_pow]

theorem H12_Gnegall (hn : n = 2 ^ a * nodd) {g : ZMod n → L} (hg : g ∈ (Ggrp n a 3 : Set (ZMod n → L)))
    (k : ZMod n) : g k * g (-k) = 1 := by
  by_cases hk : k ∈ layer0' n a
  · rw [mul_comm]; exact ((H12_memG.mp hg).1 k hk).2
  · have hk' : -k ∉ layer0' n a := fun h => hk (by have e := H12_X_neg hn h; rwa [neg_neg] at e)
    rw [(H12_memG.mp hg).2 k hk, (H12_memG.mp hg).2 _ hk', one_mul]

theorem H12_construct (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {lam0 : ZMod n → L} (hD : lam0 ∈ (topData0 n 3 : Set (ZMod n → L)))
    {g : ZMod n → L} (hg : g ∈ (Ggrp n a 3 : Set (ZMod n → L))) (hP : Pmap n a lam0 = tauG n a g / g) :
    (fun k => H12_M a lam0 k * g k) ∈ (H12_K1 : Set (ZMod n → L)) ∧
      H12_res (fun k => H12_M a lam0 k * g k) = lam0 := by
  have ha1 : 1 ≤ a := by omega
  have h2 : 2 ∣ n := H12_two_dvd hn ha1
  have h4 : 4 ∣ n := H12_four_dvd hn (by omega)
  obtain ⟨hD1, hD2⟩ := H12_memD0.mp hD
  have hl3 : ∀ ρ ∈ topLayer n, lam0 (3 * ρ) = lam0 ρ ^ 3 :=
    fun ρ hρ => (hD1 ρ ((H12_mem_topLayer ρ).mp hρ)).1
  have hlneg : ∀ ρ ∈ topLayer n, lam0 ρ * lam0 (-ρ) = 1 :=
    fun ρ hρ => (hD1 ρ ((H12_mem_topLayer ρ).mp hρ)).2
  have hgY : ∀ k, (nodd : ZMod n) * k ≠ 0 → g k = 1 :=
    fun k hk => (H12_memG.mp hg).2 k (fun hX => hk ((H12_mem_X' hn hodd).mp hX).1)
  have hNm : H12_N lam0 (a - 1) (half n) = 1 := H12_N_negself h2 h4 lam0 hlneg _ (H12_neg_half h2)
  have hMm : H12_M a lam0 (half n) = 1 := by
    have e := H12_M_half hn ha1 hodd h2 lam0 (mul_zero (nodd : ZMod n))
    rw [zero_add] at e
    rw [e, hNm]
  have hgm : g (half n) = 1 := hgY _ (by rw [H12_nodd_half hodd h2]; exact H12_half_ne h2)
  -- (h4) when `α ∈ μ_{n_odd}`
  have hYcase : ∀ α : ZMod n, (nodd : ZMod n) * α = 0 →
      H12_M a lam0 α * g α * (H12_M a lam0 (α + half n) * g (α + half n)) =
        H12_M a lam0 (2 * α) * g (2 * α) := by
    intro α hα
    have hαm : (nodd : ZMod n) * (α + half n) ≠ 0 := by
      rw [mul_add, hα, zero_add, H12_nodd_half hodd h2]; exact H12_half_ne h2
    rw [H12_M_Y hn ha1 h2 lam0 hα, H12_M_Y hn ha1 h2 lam0 (k := 2 * α) (by rw [mul_left_comm, hα, mul_zero]), hgY _ hαm,
      H12_M_half hn ha1 hodd h2 lam0 hα, one_mul, one_mul, mul_one]
    by_cases h0 : α = 0
    · subst h0
      rw [zero_add, hNm, mul_zero, mul_one]
    · have hX : α ∈ layer0' n a := (H12_mem_X' hn hodd).mpr ⟨hα, h0⟩
      rw [← H12_Pmap_eq lam0 hX, hP, Pi.div_apply, H12_tau_mem g hX, mul_div_assoc',
        mul_div_cancel_left₀ _ (H12_G_ne hg α)]
  refine ⟨⟨⟨fun k => ?_, fun k => ?_, fun k => ?_⟩, ?_⟩, ?_⟩
  · show H12_M a lam0 (3 * k) * g (3 * k) = (H12_M a lam0 k * g k) ^ 3
    rw [H12_M_three h2 h3 lam0 hl3, H12_G3all hn hodd h3 hg k, mul_pow]
  · show H12_M a lam0 k * g k * (H12_M a lam0 (-k) * g (-k)) = 1
    calc H12_M a lam0 k * g k * (H12_M a lam0 (-k) * g (-k))
        = (H12_M a lam0 k * H12_M a lam0 (-k)) * (g k * g (-k)) := by ring
      _ = 1 := by rw [H12_M_neg h2 lam0 hlneg, H12_Gnegall hn hg k, one_mul]
  · show H12_M a lam0 k * g k * (H12_M a lam0 (k + half n) * g (k + half n)) =
      H12_M a lam0 (half n) * g (half n) * (H12_M a lam0 (2 * k) * g (2 * k))
    rw [hMm, hgm, one_mul, one_mul]
    by_cases hk : (nodd : ZMod n) * k = 0
    · exact hYcase k hk
    · by_cases hkm : (nodd : ZMod n) * (k + half n) = 0
      · have e1 : k + half n + half n = k := by rw [add_assoc, ← two_mul, H12_two_mul_half h2, add_zero]
        have e2 : 2 * (k + half n) = 2 * k := by rw [mul_add, H12_two_mul_half h2, add_zero]
        have e := hYcase (k + half n) hkm
        rw [e1, e2] at e
        rw [← e]; ring
      · have h2k : (nodd : ZMod n) * (2 * k) ≠ 0 := fun h => hkm (H12_T5 hodd h2 hk h)
        rw [hgY _ hk, hgY _ hkm, hgY _ h2k, mul_one, mul_one, mul_one, H12_M_two hn ha1 hodd h2 lam0 hk hkm]
  · show H12_M a lam0 (half n) * g (half n) = 1
    rw [hMm, hgm, one_mul]
  · funext k
    by_cases hk : k ∈ topLayer n
    · simp only [H12_res, ite_eq_left hk]
      rw [H12_M_top ha1 h2 lam0 hk, hgY _ (H12_top_notY h2 hodd hk), mul_one]
    · simp only [H12_res, ite_eq_right hk]
      exact (hD2 k (Nat.not_odd_iff_even.mp ((H12_mem_topLayer k).not.mp hk))).symm

/-! ### `res(K₁) = Π⁻¹((τ-1)G)` and `ker res ≃ {±1} × G^τ` -/

theorem H12_gl_mem (hn : n = 2 ^ a * nodd) (h3 : ¬ 3 ∣ n) {lam : ZMod n → L} (hK : H12_K lam) :
    (fun k => if k ∈ layer0' n a then lam k else 1) ∈ (Ggrp n a 3 : Set (ZMod n → L)) := by
  rw [H12_memG]
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun k hk => by simp only [ite_eq_right hk]⟩
  · simp only [ite_eq_left (H12_X_mul3 hn h3 hk), ite_eq_left hk]; exact hK.1 k
  · simp only [ite_eq_left (H12_X_neg hn hk), ite_eq_left hk]; rw [mul_comm]; exact hK.2.1 k

theorem H12_res_Pmap (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n) {lam : ZMod n → L}
    (hl : lam ∈ (H12_K1 : Set (ZMod n → L))) :
    Pmap n a (H12_res lam) ∈ (fun g => tauG n a g / g) '' (Ggrp n a 3 : Set (ZMod n → L)) := by
  have ha1 : 1 ≤ a := by omega
  have h2 := H12_two_dvd hn ha1
  obtain ⟨hK, hm1⟩ := hl
  refine ⟨fun k => if k ∈ layer0' n a then lam k else 1, H12_gl_mem hn h3 hK, ?_⟩
  funext k
  show tauG n a (fun k => if k ∈ layer0' n a then lam k else 1) k / (if k ∈ layer0' n a then lam k else 1) =
    Pmap n a (H12_res lam) k
  by_cases hk : k ∈ layer0' n a
  · rw [H12_tau_mem _ hk, ite_eq_left hk, H12_Pmap_eq _ hk]
    simp only [ite_eq_left (H12_X_mul2 hn hodd hk)]
    have hY := ((H12_mem_X' hn hodd).mp hk).1
    have e4 := hK.2.2 k
    rw [hm1, one_mul] at e4
    rw [← e4, H12_N_congr (H12_res_top lam), ← H12_C1 hn ha hodd h2 hK hm1 hY,
      mul_div_cancel_left₀ _ (H12_K_ne hK k)]
  · rw [H12_tau_nmem _ hk, ite_eq_right hk, H12_Pmap_off _ hk, div_one]

theorem H12_ker_tau (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) {lam : ZMod n → L}
    (hl : lam ∈ (H12_K1 : Set (ZMod n → L))) (h1 : ∀ ρ ∈ topLayer n, lam ρ = 1) :
    tauG n a (fun k => if k ∈ layer0' n a then lam k else 1) = (fun k => if k ∈ layer0' n a then lam k else 1) := by
  have ha1 : 1 ≤ a := by omega
  have h2 := H12_two_dvd hn ha1
  obtain ⟨hK, hm1⟩ := hl
  funext k
  by_cases hk : k ∈ layer0' n a
  · rw [H12_tau_mem _ hk]
    simp only [ite_eq_left (H12_X_mul2 hn hodd hk), ite_eq_left hk]
    have hY := ((H12_mem_X' hn hodd).mp hk).1
    have e4 := hK.2.2 k
    rw [hm1, one_mul] at e4
    rw [← e4, H12_C1 hn ha hodd h2 hK hm1 hY, H12_N_allone h1, mul_one]
  · rw [H12_tau_nmem _ hk]; simp only [ite_eq_right hk]

theorem H12_ker_inv (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n) {s : L}
    (hs : s ^ 2 = 1) {g : ZMod n → L} (hg : g ∈ (Ggrp n a 3 : Set (ZMod n → L))) (hτ : tauG n a g = g) :
    (fun k => if k = 0 then s else g k) ∈ (H12_K1 : Set (ZMod n → L)) ∧
      H12_res (fun k => if k = 0 then s else g k) = 1 := by
  have ha1 : 1 ≤ a := by omega
  have h2 := H12_two_dvd hn ha1
  have hm0 := H12_half_ne h2 (n := n)
  have hg1 : ∀ k, (nodd : ZMod n) * k ≠ 0 → g k = 1 :=
    fun k hk => (H12_memG.mp hg).2 k (fun hX => hk ((H12_mem_X' hn hodd).mp hX).1)
  have hgm : g (half n) = 1 := hg1 _ (by rw [H12_nodd_half hodd h2]; exact hm0)
  have hgY : ∀ α, (nodd : ZMod n) * α = 0 → g (2 * α) = g α := by
    intro α hα
    by_cases h0 : α = 0
    · rw [h0, mul_zero]
    · have hX := (H12_mem_X' hn hodd).mpr ⟨hα, h0⟩
      have e := congrFun hτ α
      rwa [H12_tau_mem g hX] at e
  have hs3 : s ^ 3 = s := by linear_combination s * hs
  refine ⟨⟨⟨fun k => ?_, fun k => ?_, fun k => ?_⟩, ?_⟩, ?_⟩
  · show (if 3 * k = 0 then s else g (3 * k)) = (if k = 0 then s else g k) ^ 3
    by_cases hk : k = 0
    · rw [ite_eq_left (by rw [hk, mul_zero]), ite_eq_left hk, hs3]
    · rw [ite_eq_right (fun h => hk ((H12_isUnit3 h3).mul_right_eq_zero.mp h)), ite_eq_right hk, H12_G3all hn hodd h3 hg k]
  · show (if k = 0 then s else g k) * (if -k = 0 then s else g (-k)) = 1
    by_cases hk : k = 0
    · rw [ite_eq_left hk, ite_eq_left (by rw [hk, neg_zero]), ← sq, hs]
    · rw [ite_eq_right hk, ite_eq_right (neg_ne_zero.mpr hk), H12_Gnegall hn hg k]
  · show (if k = 0 then s else g k) * (if k + half n = 0 then s else g (k + half n)) =
      (if half n = 0 then s else g (half n)) * (if 2 * k = 0 then s else g (2 * k))
    rw [ite_eq_right hm0, hgm, one_mul]
    by_cases hk : k = 0
    · rw [ite_eq_left hk, ite_eq_right (by rw [hk, zero_add]; exact hm0), ite_eq_left (by rw [hk, mul_zero]), hk, zero_add, hgm,
        mul_one]
    · by_cases hkm : k + half n = 0
      · have hk' : k = half n := by rw [← H12_neg_half h2]; exact eq_neg_of_add_eq_zero_left hkm
        rw [ite_eq_right hk, ite_eq_left hkm, ite_eq_left (by rw [hk', H12_two_mul_half h2]), hk', hgm, one_mul]
      · have h2k0 : 2 * k ≠ 0 := by
          intro h
          rcases H12_ker_two h2 k h with e | e
          · exact hk e
          · apply hkm; rw [e, ← two_mul, H12_two_mul_half h2]
        rw [ite_eq_right hk, ite_eq_right hkm, ite_eq_right h2k0]
        by_cases hY : (nodd : ZMod n) * k = 0
        · rw [hg1 (k + half n) (by rw [mul_add, hY, zero_add, H12_nodd_half hodd h2]; exact hm0), mul_one,
            hgY k hY]
        · by_cases hYm : (nodd : ZMod n) * (k + half n) = 0
          · rw [hg1 k hY, one_mul, show 2 * k = 2 * (k + half n) by rw [mul_add, H12_two_mul_half h2, add_zero],
              hgY _ hYm]
          · rw [hg1 k hY, hg1 _ hYm, hg1 _ (fun h => hYm (H12_T5 hodd h2 hY h)), one_mul]
  · show (if half n = 0 then s else g (half n)) = 1
    rw [ite_eq_right hm0, hgm]
  · funext k
    by_cases hk : k ∈ topLayer n
    · have hk0 : k ≠ 0 := by
        intro h; rw [h, H12_mem_top h2, map_zero] at hk; exact absurd hk (by decide)
      simp only [H12_res, ite_eq_left hk, ite_eq_right hk0, Pi.one_apply]
      exact hg1 k (H12_top_notY h2 hodd hk)
    · simp only [H12_res, ite_eq_right hk, Pi.one_apply]

theorem H12_ker_card [CharP L 3] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n) :
    Nat.card {lam : ZMod n → L // lam ∈ (H12_K1 : Set (ZMod n → L)) ∧ H12_res lam = 1} =
      Nat.card {s : L // s ^ 2 = 1} *
        Nat.card {g : ZMod n → L // g ∈ (Ggrp n a 3 : Set (ZMod n → L)) ∧ tauG n a g = g} := by
  have ha1 : 1 ≤ a := by omega
  have h2 : 2 ∣ n := H12_two_dvd hn ha1
  have kf1 : ∀ lam : ZMod n → L, H12_res lam = 1 → ∀ ρ ∈ topLayer n, lam ρ = 1 := by
    intro lam hr ρ hρ
    have e := congrFun hr ρ
    simp only [H12_res, ite_eq_left hρ, Pi.one_apply] at e
    exact e
  rw [← Nat.card_prod]
  apply Nat.card_congr
  exact
    { toFun := fun lam => (⟨lam.1 0, by
          have e := lam.2.1.1.2.1 0
          rw [neg_zero] at e; rw [sq]; exact e⟩,
        ⟨fun k => if k ∈ layer0' n a then lam.1 k else 1, H12_gl_mem hn h3 lam.2.1.1,
          H12_ker_tau hn ha hodd lam.2.1 (kf1 _ lam.2.2)⟩)
      invFun := fun p => ⟨fun k => if k = 0 then p.1.1 else p.2.1 k,
        H12_ker_inv hn ha hodd h3 p.1.2 p.2.2.1 p.2.2.2⟩
      left_inv := fun lam => Subtype.ext (funext fun k => by
        show (if k = 0 then lam.1 0 else (if k ∈ layer0' n a then lam.1 k else 1)) = lam.1 k
        by_cases hk0 : k = 0
        · rw [ite_eq_left hk0, hk0]
        · rw [ite_eq_right hk0]
          by_cases hX : k ∈ layer0' n a
          · rw [ite_eq_left hX]
          · rw [ite_eq_right hX]
            have hY : (nodd : ZMod n) * k ≠ 0 := fun h => hX ((H12_mem_X' hn hodd).mpr ⟨h, hk0⟩)
            exact (H12_C2 hn ha hodd h2 lam.2.1.1 lam.2.1.2 (kf1 _ lam.2.2) hY).symm)
      right_inv := fun p => by
        obtain ⟨⟨s, hs⟩, ⟨g, hg, hτ⟩⟩ := p
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext (funext fun k => ?_))
        · show (if (0 : ZMod n) = 0 then s else g 0) = s
          rw [ite_eq_left rfl]
        · show (if k ∈ layer0' n a then (if k = 0 then s else g k) else 1) = g k
          by_cases hX : k ∈ layer0' n a
          · rw [ite_eq_left hX, ite_eq_right ((H12_mem_X' hn hodd).mp hX).2]
          · rw [ite_eq_right hX, (H12_memG.mp hg).2 k hX] }

/-- `K ≃ {±1} × K₁`, `λ ↦ (λ(-1), λ(-1)·λ)`. -/
theorem H12_K_card (h2 : 2 ∣ n) :
    Nat.card {lam : ZMod n → L // H12_K lam} =
      Nat.card {s : L // s ^ 2 = 1} * Nat.card (H12_K1 : Set (ZMod n → L)) := by
  have hS : ∀ lam : ZMod n → L, H12_K lam → lam (half n) ^ 2 = 1 := fun lam hl => by
    have e := hl.2.1 (half n); rw [H12_neg_half h2] at e; rw [sq]; exact e
  rw [← Nat.card_prod]
  apply Nat.card_congr
  exact
    { toFun := fun lam => (⟨lam.1 (half n), hS lam.1 lam.2⟩, ⟨fun k => lam.1 (half n) * lam.1 k, by
        obtain ⟨l1, l3, l4⟩ := lam.2
        have hs := hS lam.1 lam.2
        refine ⟨⟨fun k => ?_, fun k => ?_, fun k => ?_⟩, ?_⟩
        · show lam.1 (half n) * lam.1 (3 * k) = (lam.1 (half n) * lam.1 k) ^ 3
          rw [l1 k]; linear_combination (-(lam.1 (half n)) * lam.1 k ^ 3) * hs
        · show lam.1 (half n) * lam.1 k * (lam.1 (half n) * lam.1 (-k)) = 1
          linear_combination (lam.1 (half n)) ^ 2 * l3 k + hs
        · show lam.1 (half n) * lam.1 k * (lam.1 (half n) * lam.1 (k + half n)) =
            lam.1 (half n) * lam.1 (half n) * (lam.1 (half n) * lam.1 (2 * k))
          linear_combination (lam.1 (half n)) ^ 2 * l4 k
        · show lam.1 (half n) * lam.1 (half n) = 1
          rw [← sq]; exact hs⟩)
      invFun := fun p => ⟨fun k => p.1.1 * p.2.1 k, by
        obtain ⟨⟨l1, l3, l4⟩, lm⟩ := p.2.2
        have hs := p.1.2
        refine ⟨fun k => ?_, fun k => ?_, fun k => ?_⟩
        · show p.1.1 * p.2.1 (3 * k) = (p.1.1 * p.2.1 k) ^ 3
          rw [l1 k]; linear_combination (-(p.1.1) * p.2.1 k ^ 3) * hs
        · show p.1.1 * p.2.1 k * (p.1.1 * p.2.1 (-k)) = 1
          linear_combination (p.1.1) ^ 2 * l3 k + hs
        · show p.1.1 * p.2.1 k * (p.1.1 * p.2.1 (k + half n)) =
            p.1.1 * p.2.1 (half n) * (p.1.1 * p.2.1 (2 * k))
          linear_combination (p.1.1) ^ 2 * l4 k⟩
      left_inv := fun lam => Subtype.ext (funext fun k => by
        show lam.1 (half n) * (lam.1 (half n) * lam.1 k) = lam.1 k
        linear_combination lam.1 k * hS lam.1 lam.2)
      right_inv := fun p => by
        obtain ⟨⟨s, hs⟩, ⟨Λ, hΛ⟩⟩ := p
        have hΛm : Λ (half n) = 1 := hΛ.2
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext (funext fun k => ?_))
        · show s * Λ (half n) = s
          rw [hΛm, mul_one]
        · show s * Λ (half n) * (s * Λ k) = Λ k
          linear_combination (s ^ 2 * Λ k) * hΛm + Λ k * hs }

/-- Counting a preimage under a homomorphism of groups of functions: `|φ⁻¹(H) ∩ A| = |ker φ| · |H|`. -/
theorem H12_preimage_card {ι κ L : Type*} [Field L] (A : Set (ι → L)) (φ : (ι → L) → κ → L) (H : Set (κ → L))
    (hne : ∀ x ∈ A, ∀ i, x i ≠ 0) (hmul : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ A) (hinv : ∀ x ∈ A, x⁻¹ ∈ A)
    (hφmul : ∀ x ∈ A, ∀ y ∈ A, φ (x * y) = φ x * φ y) (hφinv : ∀ x ∈ A, φ x⁻¹ = (φ x)⁻¹)
    (hφne : ∀ x ∈ A, ∀ j, φ x j ≠ 0) (hH : H ⊆ φ '' A) :
    Nat.card {x // x ∈ A ∧ φ x ∈ H} = Nat.card {x // x ∈ A ∧ φ x = 1} * Nat.card H := by
  classical
  let s : (κ → L) → ι → L := fun y => if h : y ∈ φ '' A then h.choose else 1
  have hs : ∀ y ∈ φ '' A, s y ∈ A ∧ φ (s y) = y := by
    intro y hy
    simp only [s, dite_eq_left hy]
    exact hy.choose_spec
  have hdiv : ∀ x ∈ A, ∀ y ∈ A, x / y ∈ A := fun x hx y hy => by
    rw [div_eq_mul_inv]; exact hmul x hx _ (hinv y hy)
  have hφdiv : ∀ x ∈ A, ∀ y ∈ A, φ (x / y) = φ x / φ y := fun x hx y hy => by
    rw [div_eq_mul_inv, hφmul x hx _ (hinv y hy), hφinv y hy, ← div_eq_mul_inv]
  let e : {x // x ∈ A ∧ φ x ∈ H} ≃ {x // x ∈ A ∧ φ x = 1} × H :=
    { toFun := fun x => (⟨x.1 / s (φ x.1), hdiv _ x.2.1 _ (hs _ (hH x.2.2)).1, by
          rw [hφdiv _ x.2.1 _ (hs _ (hH x.2.2)).1, (hs _ (hH x.2.2)).2]
          funext j
          simp only [Pi.div_apply, Pi.one_apply]
          exact div_self (hφne _ x.2.1 j)⟩, ⟨φ x.1, x.2.2⟩)
      invFun := fun p => ⟨s p.2.1 * p.1.1, hmul _ (hs _ (hH p.2.2)).1 _ p.1.2.1, by
          rw [hφmul _ (hs _ (hH p.2.2)).1 _ p.1.2.1, (hs _ (hH p.2.2)).2, p.1.2.2, mul_one]
          exact p.2.2⟩
      left_inv := fun x => Subtype.ext (by
          funext j
          simp only [Pi.mul_apply, Pi.div_apply]
          rw [mul_div_assoc']
          exact mul_div_cancel_left₀ _ (hne _ (hs _ (hH x.2.2)).1 j))
      right_inv := fun p => by
          obtain ⟨⟨k, hkA, hk1⟩, ⟨y, hy⟩⟩ := p
          have hy' : φ (s y * k) = y := by
            rw [hφmul _ (hs _ (hH hy)).1 _ hkA, (hs _ (hH hy)).2, hk1, mul_one]
          refine Prod.ext ?_ ?_
          · apply Subtype.ext
            show (s y * k) / s (φ (s y * k)) = k
            rw [hy']
            funext j
            simp only [Pi.mul_apply, Pi.div_apply]
            exact mul_div_cancel_left₀ _ (hne _ (hs _ (hH hy)).1 j)
          · exact Subtype.ext hy' }
  rw [Nat.card_congr e, Nat.card_prod]

end Count

/-- Step 7 (s4_normfree.tex:134-139), with Steps 2 and 6 as exact-instance hypotheses (`h2` is
`Xia.Paper.thm_4_1_step2 n a nodd hn ha hodd h3 ω hω`, `h6` is `Xia.Paper.thm_4_1_step6 n a nodd hn ha hodd h3`). -/
theorem thm_4_1_step7_of (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type*} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (_hω : IsPrimitiveRoot ω n)
    (h2 : Nat.card (topData n 3 2 (1 : L) ω) = pairProd n 3 ∧
      Nat.card (topData0 n 3 : Set (ZMod n → L)) = pairProd n 3 ∧
      (1 : ZMod n → L) ∈ (topData0 n 3 : Set (ZMod n → L)) ∧
      ∀ l1 ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ l2 ∈ (topData0 n 3 : Set (ZMod n → L)),
        l1 * l2 ∈ (topData0 n 3 : Set (ZMod n → L)) ∧ l1⁻¹ ∈ (topData0 n 3 : Set (ZMod n → L)))
    (h6 : (∀ lam ∈ (topData0 n 3 : Set (ZMod n → L)), Pmap n a lam ∈ (Ggrp n a 3 : Set (ZMod n → L))) ∧
      (∀ l1 ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ l2 ∈ (topData0 n 3 : Set (ZMod n → L)),
        Pmap n a (l1 * l2) = Pmap n a l1 * Pmap n a l2) ∧
      Set.SurjOn (Pmap n a) (topData0 n 3 : Set (ZMod n → L)) (Ggrp n a 3)) :
    Nat.card ((fun g => tauG n a g / g) '' (Ggrp n a 3 : Set (ZMod n → L))) *
        Nat.card {g : ZMod n → L // g ∈ (Ggrp n a 3 : Set (ZMod n → L)) ∧ tauG n a g = g} =
      Nat.card (Ggrp n a 3 : Set (ZMod n → L)) ∧
    Nat.card {lam : ZMod n → L // (∀ k, lam (3 * k) = lam k ^ 3) ∧ (∀ k, lam k * lam (-k) = 1) ∧
      ∀ k, lam k * lam (k + half n) = lam (half n) * lam (2 * k)} = 4 * pairProd n 3 := by
  have ha1 : 1 ≤ a := by omega
  have htwo : 2 ∣ n := H12_two_dvd hn ha1
  have eG := thm_4_1_step7_part1 n a nodd hn hodd h3 (L := L)
  refine ⟨eG, ?_⟩
  obtain ⟨-, hD0card, -, hD0grp⟩ := h2
  obtain ⟨h6map, h6mul, h6surj⟩ := h6
  have hS2 : Nat.card {s : L // s ^ 2 = 1} = 2 := H12_card_roots 2 (H12_two_ne 2 (by decide))
  -- (A) `|K| = 2 |K₁|`
  have eA : Nat.card {lam : ZMod n → L // H12_K lam} = 2 * Nat.card (H12_K1 : Set (ZMod n → L)) := by
    rw [H12_K_card htwo, hS2]
  -- (B) `|K₁| = |ker res| · |res(K₁)|`
  have eB : Nat.card (H12_K1 : Set (ZMod n → L)) =
      Nat.card {x : ZMod n → L // x ∈ (H12_K1 : Set (ZMod n → L)) ∧ H12_res x = 1} *
        Nat.card (H12_res '' (H12_K1 : Set (ZMod n → L))) := by
    rw [← H12_preimage_card (H12_K1 : Set (ZMod n → L)) H12_res (H12_res '' (H12_K1 : Set (ZMod n → L)))
      (fun x hx k => H12_K_ne hx.1 k) (fun x hx y hy => H12_K1_mul hx hy) (fun x hx => H12_K1_inv hx)
      (fun x _ y _ => H12_res_mul x y) (fun x _ => H12_res_inv x)
      (fun x hx j => by
        by_cases hj : j ∈ topLayer n
        · rw [H12_res_top x j hj]; exact H12_K_ne hx.1 j
        · simp only [H12_res, ite_eq_right hj]; exact one_ne_zero)
      (subset_refl _)]
    apply Nat.card_congr
    exact
      { toFun := fun x => ⟨x.1, x.2, x.1, x.2, rfl⟩
        invFun := fun x => ⟨x.1, x.2.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  -- (C) `|ker res| = 2 |G^τ|`
  have eC := H12_ker_card hn ha hodd h3 (L := L)
  rw [hS2] at eC
  -- (D) `res(K₁) = Π⁻¹((τ-1)G)`
  have eD : H12_res '' (H12_K1 : Set (ZMod n → L)) =
      {lam0 | lam0 ∈ (topData0 n 3 : Set (ZMod n → L)) ∧
        Pmap n a lam0 ∈ (fun g => tauG n a g / g) '' (Ggrp n a 3 : Set (ZMod n → L))} := by
    ext lam0
    constructor
    · rintro ⟨lam, hl, rfl⟩
      exact ⟨H12_res_D0 htwo hl.1, H12_res_Pmap hn ha hodd h3 hl⟩
    · rintro ⟨hD, g, hg, hgP⟩
      exact ⟨_, (H12_construct hn ha hodd h3 hD hg hgP.symm).1, (H12_construct hn ha hodd h3 hD hg hgP.symm).2⟩
  -- (E), (F): preimages under `Π`
  have hPne : ∀ x ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ j, Pmap n a x j ≠ 0 :=
    fun x hx j => H12_G_ne (h6map x hx) j
  have hHsub : (fun g => tauG n a g / g) '' (Ggrp n a 3 : Set (ZMod n → L)) ⊆
      Pmap n a '' (topData0 n 3 : Set (ZMod n → L)) := by
    rintro y ⟨g, hg, rfl⟩
    exact h6surj (H12_G_div (H12_tau_G hn hodd h3 hg) hg)
  have eE := H12_preimage_card (topData0 n 3 : Set (ZMod n → L)) (Pmap n a)
    ((fun g => tauG n a g / g) '' (Ggrp n a 3 : Set (ZMod n → L))) (fun x hx k => H12_D0_ne hx k)
    (fun x hx y hy => (hD0grp x hx y hy).1) (fun x hx => (hD0grp x hx x hx).2) h6mul
    (fun x _ => H12_Pmap_inv x) hPne hHsub
  have eF : Nat.card (topData0 n 3 : Set (ZMod n → L)) =
      Nat.card {x : ZMod n → L // x ∈ (topData0 n 3 : Set (ZMod n → L)) ∧ Pmap n a x = 1} *
        Nat.card (Ggrp n a 3 : Set (ZMod n → L)) := by
    rw [← H12_preimage_card (topData0 n 3 : Set (ZMod n → L)) (Pmap n a) (Ggrp n a 3 : Set (ZMod n → L))
      (fun x hx k => H12_D0_ne hx k) (fun x hx y hy => (hD0grp x hx y hy).1) (fun x hx => (hD0grp x hx x hx).2)
      h6mul (fun x _ => H12_Pmap_inv x) hPne h6surj]
    apply Nat.card_congr
    exact
      { toFun := fun x => ⟨x.1, x.2, h6map x.1 x.2⟩
        invFun := fun x => ⟨x.1, x.2.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have eIm : Nat.card (H12_res '' (H12_K1 : Set (ZMod n → L))) =
      Nat.card {x : ZMod n → L // x ∈ (topData0 n 3 : Set (ZMod n → L)) ∧
        Pmap n a x ∈ (fun g => tauG n a g / g) '' (Ggrp n a 3 : Set (ZMod n → L))} := by
    rw [eD]; rfl
  show Nat.card {lam : ZMod n → L // H12_K lam} = 4 * pairProd n 3
  rw [← hD0card, eA, eB, eC, eIm, eE, eF, ← eG]
  ring

end Xia.Proofs

#print axioms Xia.Proofs.thm_4_1_step5_proved
#print axioms Xia.Proofs.thm_4_1_step7_part1
#print axioms Xia.Proofs.rem_4_4_G_proved
#print axioms Xia.Proofs.thm_4_1_step7_of
