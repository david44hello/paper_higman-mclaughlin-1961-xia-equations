/- Xia/Proofs/VcV.lean — proofs of the rows thm_5_1_c_V, caseB_delta, thm_B_V of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry
import Xia.Defs.BlockSpace
import Xia.Proofs.FibreCount

namespace Xia.Proofs

open Xia Finset

set_option linter.unusedSectionVars false

/-! ## Part A — algebra of `Vfib` and `Tsh` (any field) -/

section VAlg

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

/-- The ν-data of any function is `m`-periodic. -/
theorem H26_nuData_shift (hev : Even n) (g : ZMod n → L) (k : ZMod n) :
    nuData g (k + half n) = nuData g k := by
  unfold nuData
  rw [add_assoc, H7_two_half hev, add_zero, mul_comm]

theorem H26_Tsh_Tsh (hev : Even n) (h : ZMod n → L) : Tsh (Tsh h) = h := by
  funext k
  show h (k + half n + half n) = h k
  rw [add_assoc, H7_two_half hev, add_zero]

theorem H26_nuData_Tsh (hev : Even n) (h : ZMod n → L) : nuData (Tsh h) = nuData h := by
  funext k
  show h (k + half n) * h (k + half n + half n) = h k * h (k + half n)
  rw [add_assoc, H7_two_half hev, add_zero, mul_comm]

theorem H26_zero_mem (ω : L) (ν : ZMod n → L) : (0 : ZMod n → L) ∈ Vfib ω ν := by
  refine ⟨fun k _ => rfl, fun k _ => ?_, fun k _ => ?_⟩
  · simp
  · simp

theorem H26_add_mem [CharP L 3] (ω : L) (ν : ZMod n → L) {h h' : ZMod n → L} (hh : h ∈ Vfib ω ν)
    (hh' : h' ∈ Vfib ω ν) : h + h' ∈ Vfib ω ν := by
  obtain ⟨he, hf, hi⟩ := hh
  obtain ⟨he', hf', hi'⟩ := hh'
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · simp only [Pi.add_apply, he k hk, he' k hk, add_zero]
  · simp only [Pi.add_apply]
    rw [hf k hk, hf' k hk, add_pow_char]
    ring
  · simp only [Pi.add_apply]
    linear_combination hi k hk + hi' k hk

theorem H26_neg_mem (ω : L) (ν : ZMod n → L) {h : ZMod n → L} (hh : h ∈ Vfib ω ν) : -h ∈ Vfib ω ν := by
  obtain ⟨he, hf, hi⟩ := hh
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · simp only [Pi.neg_apply, he k hk, neg_zero]
  · simp only [Pi.neg_apply]
    rw [hf k hk]
    ring
  · simp only [Pi.neg_apply]
    linear_combination -(hi k hk)

/-- `T` maps `Vfib ω ν` to itself when `ν` is `m`-periodic. -/
theorem H26_Tsh_mem (h2 : 2 ∣ n) (h4 : 4 ∣ n) {ω : L} (hω : IsPrimitiveRoot ω n) {ν : ZMod n → L}
    (hνper : ∀ k, ν (k + half n) = ν k) {h : ZMod n → L} (hh : h ∈ Vfib ω ν) : Tsh h ∈ Vfib ω ν := by
  have hev : Even n := even_iff_two_dvd.mpr h2
  have hn2 : 2 ≤ n := Nat.le_of_dvd (NeZero.pos n) h2
  obtain ⟨he, hf, hi⟩ := hh
  refine ⟨fun k hk => he _ (H19_even_add_half h2 h4 hk), fun k hk => ?_, fun k hk => ?_⟩
  · show h (3 * k + half n) = (ω ^ k.val) ^ 6 * h (k + half n) ^ 3
    have hk' := H19_odd_add_half h2 h4 hk
    have e3 : 3 * k + half n = 3 * (k + half n) := by
      have h3m := H7_odd_mul_half hev 3 (by decide)
      push_cast at h3m
      linear_combination -h3m
    rw [e3, hf _ hk', H4_pow_val_add hω.pow_eq_one, H4_pow_val_half hω hev hn2]
    ring
  · show h (-k + half n) * ν k = -h (k + half n + half n)
    have hk' := H19_odd_add_half h2 h4 hk
    have hik := hi _ hk'
    rw [← H7_neg_add_half hev, hνper] at hik
    exact hik

theorem H26_zpow6 (x : L) : x ^ (((3 : ℕ) : ℤ) * 2) = x ^ 6 := by
  rw [show (((3 : ℕ) : ℤ) * 2) = ((6 : ℕ) : ℤ) by norm_num, zpow_natCast]

theorem H26_cast3 : ((3 : ℕ) : ZMod n) = 3 := by norm_num

/-- (F1) of Prop 2.4 at `3k`, with literal exponents. -/
theorem H26_F1_at {ω : L} {h : ZMod n → L} (hF1 : F1 3 2 ω h) (k : ZMod n) :
    h (3 * k) = (ω ^ k.val) ^ 6 * h k ^ 3 := by
  have hk := hF1 k
  rw [H26_zpow6, H26_cast3] at hk
  exact hk

end VAlg

/-! ## Part B — top data of sequences -/

section TopOf

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

theorem H26_topOf_odd {F : Type*} [CommRing F] [Algebra F L] (ω : L) (y : ZMod n → F) {k : ZMod n}
    (hk : Odd k.val) : topOf ω y k = dftA ω y k := by
  unfold topOf
  simp [hk]

theorem H26_topOf_even {F : Type*} [CommRing F] [Algebra F L] (ω : L) (y : ZMod n → F) {k : ZMod n}
    (hk : Even k.val) : topOf ω y k = 0 := by
  unfold topOf
  simp [Nat.not_odd_iff_even.mpr hk]

end TopOf

/-! ## Row 18V(c) — Theorem 5.1(c), V-form -/

theorem thm_5_1_c_V_proved (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2) :
    let ν := nuData (topOf ω y)
    ((0 : ZMod n → L) ∈ Vfib ω ν ∧ (∀ h ∈ Vfib ω ν, ∀ h' ∈ Vfib ω ν, h + h' ∈ Vfib ω ν) ∧
      ∀ h ∈ Vfib ω ν, -h ∈ Vfib ω ν) ∧
    (∀ h h' : ZMod n → L, Tsh (h + h') = Tsh h + Tsh h') ∧ (∀ h : ZMod n → L, Tsh (Tsh h) = h) ∧
    (∀ h ∈ Vfib ω ν, Tsh h ∈ Vfib ω ν ∧ nuData (Tsh h) = nuData h) ∧
    (∀ y' ∈ fibre ω y, topOf ω y' ∈ Vfib ω ν ∧ topOf ω (ySubst y') = Tsh (topOf ω y')) ∧
    Set.InjOn (topOf ω) (fibre ω y) ∧
    topOf ω '' fibre ω y = {h | h ∈ Vfib ω ν ∧ ∀ k : ZMod n, Odd k.val → nuData h k = ν k} := by
  intro ν
  have h4 := H19_four_dvd hn ha
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hev : Even n := even_iff_two_dvd.mpr h2
  have := H19_charP n (L := L)
  have hω0 : ω ≠ 0 := hω.ne_zero (NeZero.ne n)
  have hP24 := prop_2_4_bij_proved n hev h3 ω hω
  have hyf := thm_5_1_c_yform_of n a nodd hn ha hodd h3 ω hω hP24
  have hνper : ∀ k, ν (k + half n) = ν k := H26_nuData_shift hev _
  have hνodd : ∀ k : ZMod n, Odd k.val → ν k = dftA ω y k * dftA ω y (k + half n) := fun k hk => by
    show topOf ω y k * topOf ω y (k + half n) = _
    rw [H26_topOf_odd ω y hk, H26_topOf_odd ω y (H19_odd_add_half h2 h4 hk)]
  -- points of the fibre have the fibre's ν-data
  have hfibν : ∀ y' ∈ fibre ω y, ∀ k : ZMod n, Odd k.val →
      dftA ω y' k * dftA ω y' (k + half n) = ν k := by
    intro y' hy' k hk
    rw [hνodd k hk]
    exact (((hyf.2.1 y hy y' hy'.1).mpr (fun j hj => (hy'.2 j hj).symm)).2.2 k hk).symm
  -- top data of points of the fibre lie in V
  have hmemV : ∀ y' ∈ fibre ω y, topOf ω y' ∈ Vfib ω ν := by
    intro y' hy'
    obtain ⟨hF1, hF3, -⟩ := hP24.mapsTo hy'.1
    refine ⟨fun k hk => H26_topOf_even ω y' hk, fun k hk => ?_, fun k hk => ?_⟩
    · have h3k : Odd (3 * k).val := by
        have := H19_odd_three_mul h2 hk
        rwa [H26_cast3] at this
      rw [H26_topOf_odd ω y' h3k, H26_topOf_odd ω y' hk]
      exact H26_F1_at hF1 k
    · rw [H26_topOf_odd ω y' (H6_odd_neg h2 hk), H26_topOf_odd ω y' (H19_odd_add_half h2 h4 hk),
        ← hfibν y' hy' k hk]
      have hk3 := hF3 k
      rw [H19_pow_half_odd hev hω hk] at hk3
      linear_combination (dftA ω y' (k + half n)) * hk3
  -- the substitution acts on top data by `T`
  have hsub : ∀ y' ∈ fibre ω y, topOf ω (ySubst y') = Tsh (topOf ω y') := by
    intro y' hy'
    funext k
    show topOf ω (ySubst y') k = topOf ω y' (k + half n)
    rcases Nat.even_or_odd k.val with hk | hk
    · rw [H26_topOf_even ω _ hk, H26_topOf_even ω _ (H19_even_add_half h2 h4 hk)]
    · rw [H26_topOf_odd ω _ hk, H26_topOf_odd ω _ (H19_odd_add_half h2 h4 hk)]
      exact (hyf.1 y' hy'.1 k hk).1
  -- injectivity through the top data
  have hinj : Set.InjOn (topOf ω) (fibre ω y) := by
    intro y1 hy1 y2 hy2 heq
    apply hP24.injOn hy1.1 hy2.1
    funext k
    rcases Nat.even_or_odd k.val with hk | hk
    · rw [hy1.2 k hk, hy2.2 k hk]
    · have hk' := congrFun heq k
      rwa [H26_topOf_odd ω y1 hk, H26_topOf_odd ω y2 hk] at hk'
  -- the image is the set of points of V with the fibre's ν-data
  have himg : topOf ω '' fibre ω y = {h | h ∈ Vfib ω ν ∧ ∀ k : ZMod n, Odd k.val → nuData h k = ν k} := by
    ext h
    constructor
    · rintro ⟨y', hy', rfl⟩
      refine ⟨hmemV y' hy', fun k hk => ?_⟩
      show topOf ω y' k * topOf ω y' (k + half n) = ν k
      rw [H26_topOf_odd ω y' hk, H26_topOf_odd ω y' (H19_odd_add_half h2 h4 hk)]
      exact hfibν y' hy' k hk
    · rintro ⟨hV, hνh⟩
      obtain ⟨-, hF3y, -⟩ := hP24.mapsTo hy
      have hν0 : ∀ k : ZMod n, Odd k.val → ν k ≠ 0 := fun k hk => by
        rw [hνodd k hk]
        exact mul_ne_zero (H5_F3_ne hω0 _ hF3y _) (H5_F3_ne hω0 _ hF3y _)
      have hT : h ∈ topData n 3 2 (1 : L) ω := by
        refine ⟨fun k hk => ⟨?_, ?_⟩, hV.1⟩
        · rw [H26_zpow6, H26_cast3]
          exact hV.2.1 k hk
        · rw [one_mul, H19_pow_half_odd hev hω hk]
          apply mul_right_cancel₀ (hν0 k hk)
          have hνk := hνh k hk
          unfold nuData at hνk
          linear_combination (h k) * (hV.2.2 k hk) - hνk
      have hcond : ∀ ρ : ZMod n, Odd ρ.val → h ρ * h (ρ + half n) = dftA ω y ρ * dftA ω y (ρ + half n) :=
        fun ρ hρ => (hνh ρ hρ).trans (hνodd ρ hρ)
      obtain ⟨y', ⟨hy'f, hy't⟩, -⟩ := hyf.2.2 y hy h hT hcond
      refine ⟨y', hy'f, funext fun k => ?_⟩
      rcases Nat.even_or_odd k.val with hk | hk
      · rw [H26_topOf_even ω y' hk, hV.1 k hk]
      · rw [H26_topOf_odd ω y' hk, hy't k hk]
  exact ⟨⟨H26_zero_mem ω ν, fun h hh h' hh' => H26_add_mem ω ν hh hh', fun h hh => H26_neg_mem ω ν hh⟩,
    fun h h' => rfl, H26_Tsh_Tsh hev, fun h hh => ⟨H26_Tsh_mem h2 h4 hω hνper hh, H26_nuData_Tsh hev h⟩,
    fun y' hy' => ⟨hmemV y' hy', hsub y' hy'⟩, hinj, himg⟩

/-! ## Coverage — case B: `δ_O ∈ F_{q_O}` (s5_twonorms.tex:145-147) -/

/-- The exponent identity behind `δ_O^{q_O} = δ_O`: with `u = ρ^{-1}`, `s = t_0^{-1}`, `u^{q+1} = -1`, `N` even and
`s^{q^2} u^{2N} = s` (the inverse of `t_0^{3^N} = ρ^{-2N} t_0`, `q^2 = 3^N`). -/
theorem H26_delta_alg {L : Type*} [Field L] (u s : L) (N q r : ℕ) (hq : Odd q) (hqr : q = r + 2) (hN : Even N)
    (hu : u ^ (q + 1) = -1) (hs : s ^ (q * q) * u ^ (2 * N) = s) :
    (-(u ^ (N * q)) * s ^ (1 + q)) ^ q = -(u ^ (N * q)) * s ^ (1 + q) := by
  have hpow : u ^ (N * q * q) = u ^ (N * q) * u ^ (2 * N) := by
    have e : N * q * q = N * q + 2 * N + (q + 1) * (N * r) := by rw [hqr]; ring
    rw [e, pow_add, pow_add, pow_mul u (q + 1) (N * r), hu, (hN.mul_right r).neg_one_pow, mul_one]
  have e1 : (s ^ (1 + q)) ^ q = s ^ q * s ^ (q * q) := by
    rw [← pow_mul, add_mul, one_mul, pow_add]
  have e2 : (u ^ (N * q)) ^ q = u ^ (N * q) * u ^ (2 * N) := by
    rw [← pow_mul, hpow]
  rw [neg_mul, hq.neg_pow, mul_pow, e1, e2]
  linear_combination (-(u ^ (N * q) * s ^ q)) * hs

/-- Facts on a case-B block: `|O| = 2j`, `q_O = 3^j`, `j ≥ 1`, and `ρ^{q_O+1} = -1` (from `-ρ = ρ^{-q_O}`). -/
theorem H26_caseB_facts {n a nodd : ℕ} [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n) {L : Type*} [Field L] {ω : L} (hω : IsPrimitiveRoot ω n) {B : Finset (Finset (ZMod n))}
    (hB : B ∈ blocksB n) {O : Finset (ZMod n)} (hO : O ∈ B) {ρ : ZMod n} (hρ : ρ ∈ O) :
    ∃ j : ℕ, O.card = 2 * j ∧ qO B = 3 ^ j ∧ 1 ≤ j ∧ (ω ^ ρ.val) ^ (3 ^ j + 1) = -1 := by
  classical
  have h8 := H19_eight_dvd hn ha
  have h4 := H19_four_dvd hn ha
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hev : Even n := even_iff_two_dvd.mpr h2
  have hn2 : 2 ≤ n := Nat.le_of_dvd (NeZero.pos n) h2
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  obtain ⟨hBb, hexB⟩ := mem_filter.mp hB
  obtain ⟨k, hk, rfl⟩ := H19_mem_blocks hBb
  obtain ⟨z, hz, rfl⟩ := H19_blockOf_mem hev h2 h4 hk hO
  have hcl := H19_blockOf_closed hev _ _ hO
  have hBz : IsCaseB (orbit 3 z) := (H22_caseB_iff hev (orbit 3 z)).mp (by rw [hcl]; exact hexB)
  have hρorb : orbit 3 ρ = orbit 3 z := H6_orbit_eq hcop hρ
  have hρodd : Odd ρ.val := H7_orbit_odd h2 z hz ρ hρ
  have hlen : blockLen (blockOf (orbit 3 k)) = (orbit 3 z).card := by
    rw [← hcl]; exact H22_blockLen hev h3 z
  have hevc := caseAB_even_proved n a nodd hn ha hodd h3 _ (H22_orbit_mem_topOrbits hz) (Or.inr hBz)
  obtain ⟨j, hj⟩ := hevc
  have hpos := H22_orbit_card_pos (n := n) z
  have hBρ : IsCaseB (orbit 3 ρ) := by rw [hρorb]; exact hBz
  have hρm : ρ + half n ∈ inv (orbit 3 ρ) := by
    rw [← (show negO (orbit 3 ρ) = inv (orbit 3 ρ) from hBρ)]
    exact mem_image_of_mem _ (H6_self_mem 3 ρ)
  have hcase := H19_caseB_pow hcop h8 hρodd ((H11_mem_inv _ _).mp hρm)
  rw [hρorb, show (orbit 3 z).card / 2 = j by omega] at hcase
  have e : ρ * ((3 ^ j + 1 : ℕ) : ZMod n) = half n := by
    push_cast
    linear_combination hcase - H7_two_half hev
  refine ⟨j, by omega, ?_, by omega, ?_⟩
  · unfold qO; rw [hlen, show (orbit 3 z).card / 2 = j by omega]
  · rw [H4_pow_val_mul_nat hω.pow_eq_one, e, H4_pow_val_half hω hev hn2]

theorem caseB_delta_proved (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) :
    ∀ B ∈ blocksB n, ∀ O ∈ B, ∀ ρ ∈ O, ∀ t0 : L, t0 ≠ 0 → t0 ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * t0 →
      (-((ω ^ ρ.val)⁻¹ ^ (O.card * qO B)) * t0⁻¹ ^ (1 + qO B)) ^ qO B =
        -((ω ^ ρ.val)⁻¹ ^ (O.card * qO B)) * t0⁻¹ ^ (1 + qO B) := by
  intro B hB O hO ρ hρ t0 ht0 ht
  obtain ⟨j, hLj, hq, hj1, hw1⟩ := H26_caseB_facts hn ha hodd h3 hω hB hO hρ
  have hw0 : ω ^ ρ.val ≠ 0 := pow_ne_zero _ (hω.ne_zero (NeZero.ne n))
  have hq3 : 3 ≤ qO B := by
    rw [hq]
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
  have hqodd : Odd (qO B) := by rw [hq]; exact Odd.pow (by decide)
  have hu : ((ω ^ ρ.val)⁻¹) ^ (qO B + 1) = -1 := by
    rw [inv_pow, hq, hw1, inv_neg_one]
  have hqq : qO B * qO B = 3 ^ O.card := by
    rw [hq, hLj, two_mul, pow_add]
  have hs : t0⁻¹ ^ (qO B * qO B) * ((ω ^ ρ.val)⁻¹) ^ (2 * O.card) = t0⁻¹ := by
    rw [hqq, inv_pow t0, ht, mul_inv_rev, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (inv_ne_zero hw0)), mul_one]
  exact H26_delta_alg (ω ^ ρ.val)⁻¹ t0⁻¹ O.card (qO B) (qO B - 2) hqodd (by omega) ⟨j, by omega⟩ hu hs

/-! ## Row BV — Theorem B, the V sentences, from rows 18V(c), 18V(c-blocks), 18V(d) -/

theorem thm_B_V_of (n : ℕ) [NeZero n] (hn : n % 24 = 8) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L)
    (_hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2)) (_hy : y ∈ NFSet n 2)
    (hcV : ∀ (a nodd : ℕ), n = 2 ^ a * nodd → 3 ≤ a → Odd nodd → ¬ 3 ∣ n →
      let ν := nuData (topOf ω y)
      ((0 : ZMod n → L) ∈ Vfib ω ν ∧ (∀ h ∈ Vfib ω ν, ∀ h' ∈ Vfib ω ν, h + h' ∈ Vfib ω ν) ∧
        ∀ h ∈ Vfib ω ν, -h ∈ Vfib ω ν) ∧
      (∀ h h' : ZMod n → L, Tsh (h + h') = Tsh h + Tsh h') ∧ (∀ h : ZMod n → L, Tsh (Tsh h) = h) ∧
      (∀ h ∈ Vfib ω ν, Tsh h ∈ Vfib ω ν ∧ nuData (Tsh h) = nuData h) ∧
      (∀ y' ∈ fibre ω y, topOf ω y' ∈ Vfib ω ν ∧ topOf ω (ySubst y') = Tsh (topOf ω y')) ∧
      Set.InjOn (topOf ω) (fibre ω y) ∧
      topOf ω '' fibre ω y = {h | h ∈ Vfib ω ν ∧ ∀ k : ZMod n, Odd k.val → nuData h k = ν k})
    (hcVB : ∀ (a nodd : ℕ), n = 2 ^ a * nodd → 3 ≤ a → Odd nodd → ¬ 3 ∣ n →
      let ν := nuData (topOf ω y)
      (∀ h ∈ Vfib ω ν, (∀ B ∈ blocks n, restrictBlock B h ∈ VfibBlock ω ν B) ∧ h = ∑ B ∈ blocks n, restrictBlock B h) ∧
      (∀ B ∈ blocks n, ∀ h ∈ VfibBlock ω ν B, Tsh h ∈ VfibBlock ω ν B) ∧
      (∀ B ∈ blocksA n, ∀ O ∈ B, ∀ ρ ∈ O,
        Set.BijOn (fun h : ZMod n → L => h ρ) (VfibBlock ω ν B)
          {t | t ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * t} ∧
        ∀ h ∈ VfibBlock ω ν B, Tsh h ρ = (ω ^ ρ.val) ^ (O.card * qO B) * h ρ ^ qO B ∧
          nuData h ρ = (ω ^ ρ.val) ^ (O.card * qO B) * h ρ ^ (1 + qO B)) ∧
      (∀ B ∈ blocksC n, ∀ O ∈ B, ∀ ρ ∈ O,
        Set.BijOn (fun h : ZMod n → L => (h ρ, h (ρ + half n))) (VfibBlock ω ν B)
          ({t | t ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * t} ×ˢ
            {t | t ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * t}) ∧
        ∀ h ∈ VfibBlock ω ν B, Tsh h ρ = h (ρ + half n) ∧ Tsh h (ρ + half n) = h ρ) ∧
      (∀ B ∈ blocksB n, ∀ O ∈ B, ∀ ρ ∈ O,
        Set.BijOn (fun h : ZMod n → L => (h ρ / topOf ω y ρ, -(topOf ω y ρ * h (-ρ)))) (VfibBlock ω ν B)
          ({x | x ^ qO B = x} ×ˢ {x | x ^ qO B = x}) ∧
        ∀ h ∈ VfibBlock ω ν B,
          Tsh h ρ / topOf ω y ρ = (-((ω ^ ρ.val)⁻¹ ^ (O.card * qO B)) * (topOf ω y ρ)⁻¹ ^ (1 + qO B)) *
              (-(topOf ω y ρ * h (-ρ))) ∧
          -(topOf ω y ρ * Tsh h (-ρ)) = (h ρ / topOf ω y ρ) /
              (-((ω ^ ρ.val)⁻¹ ^ (O.card * qO B)) * (topOf ω y ρ)⁻¹ ^ (1 + qO B)) ∧
          (Tsh h ρ / topOf ω y ρ) * (-(topOf ω y ρ * Tsh h (-ρ))) = (h ρ / topOf ω y ρ) * (-(topOf ω y ρ * h (-ρ)))))
    (hdV : ∀ (a nodd : ℕ), n = 2 ^ a * nodd → 3 ≤ a → Odd nodd → ¬ 3 ∣ n →
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
        algebraMap _ L (yMinus n (y' 1)) = Ycoef ω 1 ((topOf ω y' - Tsh (topOf ω y')) / 2)) :
    let ν := nuData (topOf ω y)
(((0 : ZMod n → L) ∈ Vfib ω ν ∧ (∀ h ∈ Vfib ω ν, ∀ h' ∈ Vfib ω ν, h + h' ∈ Vfib ω ν) ∧
      ∀ h ∈ Vfib ω ν, -h ∈ Vfib ω ν) ∧
    (∀ h h' : ZMod n → L, Tsh (h + h') = Tsh h + Tsh h') ∧ (∀ h : ZMod n → L, Tsh (Tsh h) = h) ∧
    (∀ h ∈ Vfib ω ν, Tsh h ∈ Vfib ω ν ∧ nuData (Tsh h) = nuData h) ∧
    (∀ y' ∈ fibre ω y, topOf ω y' ∈ Vfib ω ν ∧ topOf ω (ySubst y') = Tsh (topOf ω y')) ∧
    Set.InjOn (topOf ω) (fibre ω y) ∧
    topOf ω '' fibre ω y = {h | h ∈ Vfib ω ν ∧ ∀ k : ZMod n, Odd k.val → nuData h k = ν k}) ∧
    ((∀ h ∈ Vfib ω ν, (∀ B ∈ blocks n, restrictBlock B h ∈ VfibBlock ω ν B) ∧ h = ∑ B ∈ blocks n, restrictBlock B h) ∧
    (∀ B ∈ blocks n, ∀ h ∈ VfibBlock ω ν B, Tsh h ∈ VfibBlock ω ν B) ∧
    (∀ B ∈ blocksA n, ∀ O ∈ B, ∀ ρ ∈ O,
      Set.BijOn (fun h : ZMod n → L => h ρ) (VfibBlock ω ν B)
        {t | t ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * t} ∧
      ∀ h ∈ VfibBlock ω ν B, Tsh h ρ = (ω ^ ρ.val) ^ (O.card * qO B) * h ρ ^ qO B ∧
        nuData h ρ = (ω ^ ρ.val) ^ (O.card * qO B) * h ρ ^ (1 + qO B)) ∧
    (∀ B ∈ blocksC n, ∀ O ∈ B, ∀ ρ ∈ O,
      Set.BijOn (fun h : ZMod n → L => (h ρ, h (ρ + half n))) (VfibBlock ω ν B)
        ({t | t ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * t} ×ˢ
          {t | t ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * t}) ∧
      ∀ h ∈ VfibBlock ω ν B, Tsh h ρ = h (ρ + half n) ∧ Tsh h (ρ + half n) = h ρ) ∧
    (∀ B ∈ blocksB n, ∀ O ∈ B, ∀ ρ ∈ O,
      Set.BijOn (fun h : ZMod n → L => (h ρ / topOf ω y ρ, -(topOf ω y ρ * h (-ρ)))) (VfibBlock ω ν B)
        ({x | x ^ qO B = x} ×ˢ {x | x ^ qO B = x}) ∧
      ∀ h ∈ VfibBlock ω ν B,
        Tsh h ρ / topOf ω y ρ = (-((ω ^ ρ.val)⁻¹ ^ (O.card * qO B)) * (topOf ω y ρ)⁻¹ ^ (1 + qO B)) *
            (-(topOf ω y ρ * h (-ρ))) ∧
        -(topOf ω y ρ * Tsh h (-ρ)) = (h ρ / topOf ω y ρ) /
            (-((ω ^ ρ.val)⁻¹ ^ (O.card * qO B)) * (topOf ω y ρ)⁻¹ ^ (1 + qO B)) ∧
        (Tsh h ρ / topOf ω y ρ) * (-(topOf ω y ρ * Tsh h (-ρ))) = (h ρ / topOf ω y ρ) * (-(topOf ω y ρ * h (-ρ))))) ∧
    ((∀ h ∈ Vfib ω ν, (h + Tsh h) / 2 ∈ VfibPlus ω ν ∧ (h - Tsh h) / 2 ∈ VfibMinus ω ν ∧
      h = (h + Tsh h) / 2 + (h - Tsh h) / 2) ∧
    (∀ hp ∈ VfibPlus ω ν, ∀ hm ∈ VfibMinus ω ν, hp + hm = 0 → hp = 0 ∧ hm = 0) ∧
    (∀ (s : ℕ) (h h' : ZMod n → L), Ycoef ω s (h + h') = Ycoef ω s h + Ycoef ω s h') ∧
    (∀ h ∈ Vfib ω ν, (∃ x : GaloisField 3 (n / 2), algebraMap _ L x = Ycoef ω 0 h) ∧
      ∃ x : GaloisField 3 (n / 2), algebraMap _ L x = Ycoef ω 1 h) ∧
    Set.InjOn (Ycoef ω 0) (VfibPlus ω ν) ∧ Set.InjOn (Ycoef ω 1) (VfibMinus ω ν) ∧
    (∀ h ∈ VfibMinus ω ν, Ycoef ω 0 h = 0) ∧ (∀ h ∈ VfibPlus ω ν, Ycoef ω 1 h = 0) ∧
    ∀ y' ∈ fibre ω y,
      algebraMap _ L (yMinus n (y' 0)) = Ycoef ω 0 ((topOf ω y' + Tsh (topOf ω y')) / 2) ∧
      algebraMap _ L (yMinus n (y' 1)) = Ycoef ω 1 ((topOf ω y' - Tsh (topOf ω y')) / 2)) := by
  intro ν
  obtain ⟨a, nodd, hna, ha, hodd, h3⟩ := H19_decomp n hn
  exact ⟨hcV a nodd hna ha hodd h3, hcVB a nodd hna ha hodd h3, hdV a nodd hna ha hodd h3⟩

end Xia.Proofs

#print axioms Xia.Proofs.thm_5_1_c_V_proved
#print axioms Xia.Proofs.caseB_delta_proved
#print axioms Xia.Proofs.thm_B_V_of
