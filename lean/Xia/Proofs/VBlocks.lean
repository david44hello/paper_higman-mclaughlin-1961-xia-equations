/- Xia/Proofs/VBlocks.lean — proofs of the rows thm_5_1_c_V_blocks of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.BlockSpace
import Xia.Proofs.FibreCount

namespace Xia.Proofs

open Xia Finset

set_option linter.unusedSectionVars false

/-! ## 1. Orbits and the union of a block -/

section H29Orbits

variable {n : ℕ} [NeZero n]

theorem H29_mul3_mem {x a : ZMod n} (h : x ∈ orbit 3 a) : 3 * x ∈ orbit 3 a := by
  obtain ⟨i, rfl⟩ := H19_mem_orbit3.mp h
  exact H19_mem_orbit3.mpr ⟨i + 1, by ring⟩

theorem H29_of_mul3_mem (hcop : Nat.Coprime 3 n) {x a : ZMod n} (h : 3 * x ∈ orbit 3 a) : x ∈ orbit 3 a := by
  obtain ⟨m, hm⟩ := H6_pow_period (n := n) hcop
  obtain ⟨i, hi⟩ := H19_mem_orbit3.mp h
  simp only [Nat.cast_ofNat] at hm
  refine H19_mem_orbit3.mpr ⟨m + i, ?_⟩
  calc x = 3 ^ (m + 1) * x := by rw [hm, one_mul]
    _ = 3 ^ m * (3 * x) := by ring
    _ = 3 ^ (m + i) * a := by rw [hi]; ring

theorem H29_add_half_mem (hev : Even n) {x a : ZMod n} (h : x ∈ orbit 3 a) :
    x + half n ∈ orbit 3 (a + half n) := by
  obtain ⟨i, rfl⟩ := H19_mem_orbit3.mp h
  exact H19_mem_orbit3.mpr ⟨i, by rw [mul_add, H19_pow_mul_half hev]⟩

/-- The union of the orbits of the block of `ρ`: `O ∪ O^{-1} ∪ -O ∪ -O^{-1}`. -/
theorem H29_mem_U (hev : Even n) (ρ x : ZMod n) :
    x ∈ (blockOf (orbit 3 ρ)).biUnion id ↔
      x ∈ orbit 3 ρ ∨ x ∈ orbit 3 (-ρ) ∨ x ∈ orbit 3 (ρ + half n) ∨ x ∈ orbit 3 (-ρ + half n) := by
  unfold blockOf
  rw [H6_inv_orbit, H19_negO_orbit hev, H19_negO_orbit hev]
  simp only [mem_biUnion, mem_insert, mem_singleton, id]
  constructor
  · rintro ⟨O, hO, hx⟩
    rcases hO with rfl | rfl | rfl | rfl
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr hx))
  · rintro (hx | hx | hx | hx)
    · exact ⟨_, Or.inl rfl, hx⟩
    · exact ⟨_, Or.inr (Or.inl rfl), hx⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), hx⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), hx⟩

theorem H29_neg_neg_half (hev : Even n) (x : ZMod n) : -(-x + half n) = x + half n := by
  linear_combination -(H7_two_half hev)

theorem H29_add_half_half (hev : Even n) (x : ZMod n) : x + half n + half n = x := by
  rw [add_assoc, H7_two_half hev, add_zero]

theorem H29_U_neg (hev : Even n) {ρ x : ZMod n} (hx : x ∈ (blockOf (orbit 3 ρ)).biUnion id) :
    -x ∈ (blockOf (orbit 3 ρ)).biUnion id := by
  rw [H29_mem_U hev] at hx ⊢
  rcases hx with hx | hx | hx | hx
  · exact Or.inr (Or.inl (H6_neg_mem hx))
  · have := H6_neg_mem hx
    rw [neg_neg] at this
    exact Or.inl this
  · have := H6_neg_mem hx
    rw [← H7_neg_add_half hev] at this
    exact Or.inr (Or.inr (Or.inr this))
  · have := H6_neg_mem hx
    rw [H29_neg_neg_half hev] at this
    exact Or.inr (Or.inr (Or.inl this))

theorem H29_U_add_half (hev : Even n) {ρ x : ZMod n} (hx : x ∈ (blockOf (orbit 3 ρ)).biUnion id) :
    x + half n ∈ (blockOf (orbit 3 ρ)).biUnion id := by
  rw [H29_mem_U hev] at hx ⊢
  rcases hx with hx | hx | hx | hx
  · exact Or.inr (Or.inr (Or.inl (H29_add_half_mem hev hx)))
  · exact Or.inr (Or.inr (Or.inr (H29_add_half_mem hev hx)))
  · have := H29_add_half_mem hev hx
    rw [H29_add_half_half hev] at this
    exact Or.inl this
  · have := H29_add_half_mem hev hx
    rw [H29_add_half_half hev] at this
    exact Or.inr (Or.inl this)

theorem H29_U_mul3 (hev : Even n) {ρ x : ZMod n} (hx : x ∈ (blockOf (orbit 3 ρ)).biUnion id) :
    3 * x ∈ (blockOf (orbit 3 ρ)).biUnion id := by
  rw [H29_mem_U hev] at hx ⊢
  rcases hx with hx | hx | hx | hx
  · exact Or.inl (H29_mul3_mem hx)
  · exact Or.inr (Or.inl (H29_mul3_mem hx))
  · exact Or.inr (Or.inr (Or.inl (H29_mul3_mem hx)))
  · exact Or.inr (Or.inr (Or.inr (H29_mul3_mem hx)))

theorem H29_U_of_mul3 (hev : Even n) (hcop : Nat.Coprime 3 n) {ρ x : ZMod n}
    (hx : 3 * x ∈ (blockOf (orbit 3 ρ)).biUnion id) : x ∈ (blockOf (orbit 3 ρ)).biUnion id := by
  rw [H29_mem_U hev] at hx ⊢
  rcases hx with hx | hx | hx | hx
  · exact Or.inl (H29_of_mul3_mem hcop hx)
  · exact Or.inr (Or.inl (H29_of_mul3_mem hcop hx))
  · exact Or.inr (Or.inr (Or.inl (H29_of_mul3_mem hcop hx)))
  · exact Or.inr (Or.inr (Or.inr (H29_of_mul3_mem hcop hx)))

/-- Every member `O` of a block, and every `ρ ∈ O`: `ρ` is odd, `O = orbit ρ`, and the block is `blockOf (orbit ρ)`. -/
theorem H29_rep {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (h3 : ¬ 3 ∣ n)
    {B : Finset (Finset (ZMod n))} (hB : B ∈ blocks n) {O : Finset (ZMod n)} (hO : O ∈ B) {ρ : ZMod n}
    (hρ : ρ ∈ O) : Odd ρ.val ∧ O = orbit 3 ρ ∧ B = blockOf (orbit 3 ρ) := by
  have h4 := H19_four_dvd hn ha
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hev : Even n := even_iff_two_dvd.mpr h2
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  obtain ⟨k, hk, rfl⟩ := H19_mem_blocks hB
  obtain ⟨z, hz, rfl⟩ := H19_blockOf_mem hev h2 h4 hk hO
  have heq : orbit 3 ρ = orbit 3 z := H6_orbit_eq hcop hρ
  refine ⟨H7_orbit_odd h2 z hz ρ hρ, heq.symm, ?_⟩
  rw [heq, H19_blockOf_closed hev _ _ hO]

theorem H29_orbit_neg_ne {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {ρ : ZMod n} (hρ : Odd ρ.val) : orbit 3 (-ρ) ≠ orbit 3 ρ := by
  rw [← H6_inv_orbit]
  exact H19_top_mem hn ha hodd h3 hρ

theorem H29_orbit_neg_inj {x z : ZMod n} (h : orbit 3 (-x) = orbit 3 (-z)) : orbit 3 x = orbit 3 z := by
  rw [← H6_inv_orbit, ← H6_inv_orbit] at h
  exact H22_inv_inj h

theorem H29_blockOf_add_half (hev : Even n) (ρ : ZMod n) :
    blockOf (orbit 3 (ρ + half n)) = blockOf (orbit 3 ρ) := by
  apply H19_blockOf_closed hev
  rw [← H19_negO_orbit hev]
  unfold blockOf
  simp

theorem H29_blockOf_neg (hev : Even n) (ρ : ZMod n) : blockOf (orbit 3 (-ρ)) = blockOf (orbit 3 ρ) := by
  apply H19_blockOf_closed hev
  rw [← H6_inv_orbit]
  unfold blockOf
  simp

end H29Orbits

/-! ## 2. Generic facts on `Vfib` -/

section H29Vfib

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

/-- (F1) along an orbit: `h(3^i ρ) = (ω^ρ)^{2 i 3^i} h(ρ)^{3^i}`. -/
theorem H29_iter (h2 : 2 ∣ n) {ω : L} (hω1 : ω ^ n = 1) {h : ZMod n → L}
    (hF : ∀ k : ZMod n, Odd k.val → h (3 * k) = (ω ^ k.val) ^ 6 * h k ^ 3) {ρ : ZMod n} (hρ : Odd ρ.val)
    (i : ℕ) : h ((3 : ZMod n) ^ i * ρ) = (ω ^ ρ.val) ^ (2 * i * 3 ^ i) * h ρ ^ (3 ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hx : ω ^ ((3 : ZMod n) ^ i * ρ).val = (ω ^ ρ.val) ^ (3 ^ i) := by
      rw [H4_pow_val_mul_nat hω1 ρ (3 ^ i)]; congr 2; push_cast; ring
    rw [show (3 : ZMod n) ^ (i + 1) * ρ = 3 * (3 ^ i * ρ) by ring, hF _ (H11_pow_odd h2 i hρ), ih, hx,
      H4_step2a]

/-- (P1) wraps: `h(ρ)^{3^N} = ρ^{-2N} h(ρ)` when `3^N ρ = ρ`. -/
theorem H29_wrap (h2 : 2 ∣ n) {ω : L} (hω1 : ω ^ n = 1) (hω0 : ω ≠ 0) {h : ZMod n → L}
    (hF : ∀ k : ZMod n, Odd k.val → h (3 * k) = (ω ^ k.val) ^ 6 * h k ^ 3) {ρ : ZMod n} (hρ : Odd ρ.val)
    {N : ℕ} (hN : (3 : ZMod n) ^ N * ρ = ρ) : h ρ ^ (3 ^ N) = (ω ^ ρ.val)⁻¹ ^ (2 * N) * h ρ := by
  have e := H29_iter h2 hω1 hF hρ N
  rw [hN] at e
  have hρpow : (ω ^ ρ.val) ^ (3 ^ N) = ω ^ ρ.val := by
    rw [H4_pow_val_mul_nat hω1 ρ (3 ^ N)]
    congr 2
    push_cast
    rw [mul_comm, hN]
  have hX : (ω ^ ρ.val) ^ (2 * N * 3 ^ N) = (ω ^ ρ.val) ^ (2 * N) := by
    rw [mul_comm (2 * N), pow_mul, hρpow]
  rw [hX] at e
  have hX0 : (ω ^ ρ.val) ^ (2 * N) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hω0)
  rw [inv_pow]
  conv_rhs => rw [e]
  rw [← mul_assoc, inv_mul_cancel₀ hX0, one_mul]

theorem H29_Vfib_sub [CharP L 3] {ω : L} {ν : ZMod n → L} {h1 h2 : ZMod n → L} (hh1 : h1 ∈ Vfib ω ν)
    (hh2 : h2 ∈ Vfib ω ν) : h1 - h2 ∈ Vfib ω ν := by
  obtain ⟨a1, b1, c1⟩ := hh1
  obtain ⟨a2, b2, c2⟩ := hh2
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · simp only [Pi.sub_apply, a1 k hk, a2 k hk, sub_zero]
  · simp only [Pi.sub_apply]
    rw [b1 k hk, b2 k hk, sub_pow_char]
    ring
  · simp only [Pi.sub_apply]
    linear_combination c1 k hk - c2 k hk

theorem H29_block_sub [CharP L 3] {ω : L} {ν : ZMod n → L} {B : Finset (Finset (ZMod n))} {h1 h2 : ZMod n → L}
    (hh1 : h1 ∈ VfibBlock ω ν B) (hh2 : h2 ∈ VfibBlock ω ν B) : h1 - h2 ∈ VfibBlock ω ν B :=
  ⟨H29_Vfib_sub hh1.1 hh2.1, fun k hk => by simp only [Pi.sub_apply, hh1.2 k hk, hh2.2 k hk, sub_zero]⟩

theorem H29_zero_orbit (h2 : 2 ∣ n) {ω : L} (hω1 : ω ^ n = 1) {ν : ZMod n → L} {d : ZMod n → L}
    (hd : d ∈ Vfib ω ν) {ρ : ZMod n} (hρ : Odd ρ.val) (h0 : d ρ = 0) : ∀ x ∈ orbit 3 ρ, d x = 0 := by
  intro x hx
  obtain ⟨i, rfl⟩ := H19_mem_orbit3.mp hx
  rw [H29_iter h2 hω1 hd.2.1 hρ i, h0, zero_pow (pow_ne_zero _ (by norm_num)), mul_zero]

theorem H29_zero_inv (hev : Even n) (h2 : 2 ∣ n) (h4 : 4 ∣ n) {ω : L} {ν : ZMod n → L}
    (hν : ∀ k : ZMod n, Odd k.val → ν k ≠ 0) {d : ZMod n → L} (hd : d ∈ Vfib ω ν) {a : ZMod n}
    (hz : ∀ x ∈ orbit 3 a, d x = 0) (ha : Odd a.val) : ∀ x ∈ orbit 3 (-a + half n), d x = 0 := by
  intro x hx
  obtain ⟨i, rfl⟩ := H19_mem_orbit3.mp hx
  have hk : Odd (-((3 : ZMod n) ^ i * (-a + half n))).val :=
    H6_odd_neg h2 (H11_pow_odd h2 i (H19_odd_add_half h2 h4 (H6_odd_neg h2 ha)))
  have e := hd.2.2 _ hk
  have e2 : -((3 : ZMod n) ^ i * (-a + half n)) + half n = 3 ^ i * a := by
    rw [mul_add, H19_pow_mul_half hev]; ring
  rw [neg_neg, e2, hz _ (H19_mem_orbit3.mpr ⟨i, rfl⟩), neg_zero] at e
  exact (mul_eq_zero.mp e).resolve_right (hν _ hk)

/-- A block point vanishing at `ρ` and at `ρ + m` vanishes. -/
theorem H29_block_zero (hev : Even n) (h2 : 2 ∣ n) (h4 : 4 ∣ n) {ω : L} (hω1 : ω ^ n = 1) {ν : ZMod n → L}
    (hν : ∀ k : ZMod n, Odd k.val → ν k ≠ 0) {ρ : ZMod n} (hρ : Odd ρ.val) {d : ZMod n → L}
    (hd : d ∈ VfibBlock ω ν (blockOf (orbit 3 ρ))) (h0 : d ρ = 0) (h0' : d (ρ + half n) = 0) : d = 0 := by
  have hρm : Odd (ρ + half n).val := H19_odd_add_half h2 h4 hρ
  have z1 := H29_zero_orbit h2 hω1 hd.1 hρ h0
  have z2 := H29_zero_orbit h2 hω1 hd.1 hρm h0'
  have z3 := H29_zero_inv hev h2 h4 hν hd.1 z1 hρ
  have z4 := H29_zero_inv hev h2 h4 hν hd.1 z2 hρm
  rw [show -(ρ + half n) + half n = -ρ by ring] at z4
  funext k
  show d k = 0
  by_cases hk : k ∈ (blockOf (orbit 3 ρ)).biUnion id
  · rw [H29_mem_U hev] at hk
    rcases hk with hk | hk | hk | hk
    · exact z1 k hk
    · exact z4 k hk
    · exact z2 k hk
    · exact z3 k hk
  · exact hd.2 k hk

/-- `T` maps `Vfib` to itself. -/
theorem H29_Tsh_Vfib (h2 : 2 ∣ n) (h4 : 4 ∣ n) (hev : Even n) {ω : L} (hω : IsPrimitiveRoot ω n)
    {ν : ZMod n → L} (hν : ∀ k : ZMod n, ν (k + half n) = ν k) {h : ZMod n → L} (hh : h ∈ Vfib ω ν) :
    Tsh h ∈ Vfib ω ν := by
  obtain ⟨a1, b1, c1⟩ := hh
  have hω1 : ω ^ n = 1 := hω.pow_eq_one
  refine ⟨fun k hk => a1 _ (H19_even_add_half h2 h4 hk), fun k hk => ?_, fun k hk => ?_⟩
  · show h (3 * k + half n) = (ω ^ k.val) ^ 6 * h (k + half n) ^ 3
    have e3 : 3 * k + half n = 3 * (k + half n) := by
      have := H19_pow_mul_half hev 1
      rw [pow_one] at this
      rw [mul_add, this]
    have hpow : (ω ^ (k + half n).val) ^ 6 = (ω ^ k.val) ^ 6 := by
      rw [H4_pow_val_add hω1, H6_half_val, H7_pow_half_eq_neg_one hev hω, mul_neg_one,
        Even.neg_pow (by decide)]
    rw [e3, b1 _ (H19_odd_add_half h2 h4 hk), hpow]
  · show h (-k + half n) * ν k = -h (k + half n + half n)
    have e := c1 _ (H19_odd_add_half h2 h4 hk)
    rw [← H7_neg_add_half hev, hν] at e
    exact e

theorem H29_nu_half (hev : Even n) (f : ZMod n → L) (k : ZMod n) : nuData f (k + half n) = nuData f k := by
  unfold nuData
  rw [H29_add_half_half hev, mul_comm]

theorem H29_nu_inv (hev : Even n) (h2 : 2 ∣ n) (h4 : 4 ∣ n) {f : ZMod n → L}
    (hfn : ∀ k : ZMod n, Odd k.val → f k * f (-k) = -1) {k : ZMod n} (hk : Odd k.val) :
    nuData f k * nuData f (-k) = 1 := by
  unfold nuData
  have e1 := hfn k hk
  have e2 := hfn (k + half n) (H19_odd_add_half h2 h4 hk)
  rw [← H7_neg_add_half hev] at e2
  linear_combination (f (k + half n) * f (-k + half n)) * e1 - e2

/-- The construction: `f · φ ∈ Vfib` when `φ(3k) = φ(k)^3` and `φ(-k) = φ(k+m)`. -/
theorem H29_mk {ω : L} {f : ZMod n → L} (φ : ZMod n → L)
    (hf0 : ∀ k : ZMod n, Even k.val → f k = 0)
    (hf3 : ∀ k : ZMod n, Odd k.val → f (3 * k) = (ω ^ k.val) ^ 6 * f k ^ 3)
    (hfn : ∀ k : ZMod n, Odd k.val → f k * f (-k) = -1)
    (hφ3 : ∀ k : ZMod n, φ (3 * k) = φ k ^ 3) (hφn : ∀ k : ZMod n, φ (-k) = φ (k + half n)) :
    (fun k => f k * φ k) ∈ Vfib ω (nuData f) := by
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · show f k * φ k = 0
    rw [hf0 k hk, zero_mul]
  · show f (3 * k) * φ (3 * k) = (ω ^ k.val) ^ 6 * (f k * φ k) ^ 3
    rw [hf3 k hk, hφ3 k]
    ring
  · show f (-k) * φ (-k) * (f k * f (k + half n)) = -(f (k + half n) * φ (k + half n))
    rw [hφn k]
    linear_combination (f (k + half n) * φ (k + half n)) * hfn k hk

theorem H29_mk_block {ω : L} {f : ZMod n → L} (φ : ZMod n → L)
    (hf0 : ∀ k : ZMod n, Even k.val → f k = 0)
    (hf3 : ∀ k : ZMod n, Odd k.val → f (3 * k) = (ω ^ k.val) ^ 6 * f k ^ 3)
    (hfn : ∀ k : ZMod n, Odd k.val → f k * f (-k) = -1)
    (hφ3 : ∀ k : ZMod n, φ (3 * k) = φ k ^ 3) (hφn : ∀ k : ZMod n, φ (-k) = φ (k + half n))
    {B : Finset (Finset (ZMod n))} (hsupp : ∀ k : ZMod n, k ∉ B.biUnion id → φ k = 0) :
    (fun k => f k * φ k) ∈ VfibBlock ω (nuData f) B :=
  ⟨H29_mk φ hf0 hf3 hfn hφ3 hφn, fun k hk => by show f k * φ k = 0; rw [hsupp k hk, mul_zero]⟩

theorem H29_c_shift (hev : Even n) {ω : L} (hω : IsPrimitiveRoot ω n) (ρ : ZMod n) (N : ℕ) :
    (ω ^ (ρ + half n).val)⁻¹ ^ (2 * N) = (ω ^ ρ.val)⁻¹ ^ (2 * N) := by
  rw [H4_pow_val_add hω.pow_eq_one, H6_half_val, H7_pow_half_eq_neg_one hev hω, mul_neg_one, inv_neg,
    Even.neg_pow (even_two_mul N)]

theorem H29_negpow {x : L} {Lc : ℕ} (hLev : Even Lc) (hx : x ^ (3 ^ (Lc / 2)) = x) : (-x) ^ (3 ^ Lc) = -x := by
  have hqq : (3 : ℕ) ^ Lc = 3 ^ (Lc / 2) * 3 ^ (Lc / 2) := by
    rw [← pow_add]
    congr 1
    obtain ⟨r, hr⟩ := hLev
    omega
  have hodd3 : Odd ((3 : ℕ) ^ (Lc / 2)) := Odd.pow (by decide)
  rw [hqq, pow_mul, Odd.neg_pow hodd3, hx, Odd.neg_pow hodd3, hx]

theorem H29_three_eq_zero [CharP L 3] : (3 : L) = 0 := by
  have := CharP.cast_eq_zero L 3
  exact_mod_cast this

end H29Vfib

/-! ## 3. The orbit functions `P_{ρ,c}` and `Ψ_{ρ,c}` -/

section H29Psi

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

open Classical in
/-- `P_{ρ,c}(3^i ρ) := c^{3^i}` on the orbit of `ρ`, `0` elsewhere. -/
noncomputable def H29_P (ρ : ZMod n) (c : L) (k : ZMod n) : L :=
  if hk : ∃ i : ℕ, k = (3 : ZMod n) ^ i * ρ then c ^ (3 ^ Classical.choose hk) else 0

/-- `Ψ_{ρ,c}(k) := P_{ρ,c}(k) + P_{ρ,c}(-k + m)`. -/
noncomputable def H29_Psi (ρ : ZMod n) (c : L) (k : ZMod n) : L := H29_P ρ c k + H29_P ρ c (-k + half n)

theorem H29_pow3_mod {c : L} {N : ℕ} (hc : c ^ (3 ^ N) = c) (i : ℕ) : c ^ (3 ^ i) = c ^ (3 ^ (i % N)) := by
  have key : ∀ q r : ℕ, c ^ (3 ^ (N * q + r)) = c ^ (3 ^ r) := by
    intro q r
    induction q with
    | zero => simp
    | succ q ih => rw [show N * (q + 1) + r = N + (N * q + r) by ring, pow_add, pow_mul, hc, ih]
  conv_lhs => rw [← Nat.div_add_mod i N]
  exact key _ _

theorem H29_P_eq (h3 : ¬ 3 ∣ n) {ρ k : ZMod n} {c : L} (hc : c ^ (3 ^ (orbit 3 ρ).card) = c) {i : ℕ}
    (hi : k = (3 : ZMod n) ^ i * ρ) : H29_P ρ c k = c ^ (3 ^ i) := by
  have hex : ∃ i : ℕ, k = (3 : ZMod n) ^ i * ρ := ⟨i, hi⟩
  rw [H11_card_orbit h3] at hc
  rw [H29_P, dite_eq_left hex, H29_pow3_mod hc, H29_pow3_mod hc i]
  congr 2
  exact (H11_pow_eq_iff h3 ρ _ _).mp ((Classical.choose_spec hex).symm.trans hi)

theorem H29_P_self (h3 : ¬ 3 ∣ n) {ρ : ZMod n} {c : L} (hc : c ^ (3 ^ (orbit 3 ρ).card) = c) :
    H29_P ρ c ρ = c := by
  rw [H29_P_eq h3 hc (i := 0) (by simp), pow_zero, pow_one]

theorem H29_P_zero {ρ k : ZMod n} (c : L) (hk : k ∉ orbit 3 ρ) : H29_P ρ c k = 0 := by
  rw [H29_P, dite_eq_right]
  rintro ⟨i, hi⟩
  exact hk (H19_mem_orbit3.mpr ⟨i, hi⟩)

theorem H29_P_mul3 (h3 : ¬ 3 ∣ n) {ρ : ZMod n} {c : L} (hc : c ^ (3 ^ (orbit 3 ρ).card) = c) (k : ZMod n) :
    H29_P ρ c (3 * k) = H29_P ρ c k ^ 3 := by
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  by_cases hk : k ∈ orbit 3 ρ
  · obtain ⟨i, hi⟩ := H19_mem_orbit3.mp hk
    rw [H29_P_eq h3 hc hi, H29_P_eq h3 hc (i := i + 1) (by rw [hi]; ring), pow_succ, pow_mul]
  · rw [H29_P_zero c hk, H29_P_zero c (fun h => hk (H29_of_mul3_mem hcop h))]
    ring

theorem H29_Psi_mul3 [CharP L 3] (hev : Even n) (h3 : ¬ 3 ∣ n) {ρ : ZMod n} {c : L}
    (hc : c ^ (3 ^ (orbit 3 ρ).card) = c) (k : ZMod n) : H29_Psi ρ c (3 * k) = H29_Psi ρ c k ^ 3 := by
  have e : -(3 * k) + half n = 3 * (-k + half n) := by
    have := H19_pow_mul_half hev 1
    rw [pow_one] at this
    rw [mul_add, this]
    ring
  unfold H29_Psi
  rw [e, H29_P_mul3 h3 hc, H29_P_mul3 h3 hc, add_pow_char]

theorem H29_Psi_neg (ρ : ZMod n) (c : L) (k : ZMod n) : H29_Psi ρ c (-k) = H29_Psi ρ c (k + half n) := by
  unfold H29_Psi
  rw [neg_neg, show -(k + half n) + half n = -k by ring]
  exact add_comm _ _

theorem H29_Psi_supp (hev : Even n) {ρ k : ZMod n} (c : L) (hk : k ∉ (blockOf (orbit 3 ρ)).biUnion id) :
    H29_Psi ρ c k = 0 := by
  rw [H29_mem_U hev] at hk
  simp only [not_or] at hk
  unfold H29_Psi
  rw [H29_P_zero c hk.1, H29_P_zero c, add_zero]
  intro hm
  apply hk.2.2.2
  have := H29_add_half_mem hev (H6_neg_mem hm)
  rwa [show -(-k + half n) + half n = k by ring] at this

end H29Psi

/-! ## 4. The top function of a solution -/

section H29Top

variable {n : ℕ} [NeZero n]

theorem H29_top (hev : Even n) (h3 : ¬ 3 ∣ n) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] {ω : L}
    (hω : IsPrimitiveRoot ω n) {y : ZMod n → GaloisField 3 (n / 2)} (hy : y ∈ NFSet n 2) :
    (∀ k : ZMod n, Even k.val → topOf ω y k = 0) ∧
    (∀ k : ZMod n, Odd k.val → topOf ω y (3 * k) = (ω ^ k.val) ^ 6 * topOf ω y k ^ 3) ∧
    (∀ k : ZMod n, Odd k.val → topOf ω y k * topOf ω y (-k) = -1) := by
  have h2 : 2 ∣ n := even_iff_two_dvd.mp hev
  obtain ⟨hF1, hF3, -⟩ := (prop_2_4_bij_proved n hev h3 ω hω).mapsTo hy
  have hF1' := (H4_F1_iff ω _).mp hF1
  have hT : ∀ k : ZMod n, Odd k.val → topOf ω y k = dftA ω y k := fun k hk => by
    show (if Odd k.val then dftA ω y k else 0) = dftA ω y k
    rw [ite_eq_left hk]
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · show (if Odd k.val then dftA ω y k else 0) = 0
    rw [ite_eq_right (Nat.not_odd_iff_even.mpr hk)]
  · rw [hT _ (H11_odd_mul3 h2 hk), hT k hk, hF1']
  · rw [hT k hk, hT _ (H6_odd_neg h2 hk), hF3 k, H19_pow_half_odd hev hω hk]

end H29Top

/-! ## 5. The parts of the row -/

section H29Parts

variable {n : ℕ} [NeZero n]

/-- Part 1: `V` is the direct sum of its block subspaces. -/
theorem H29_part1 {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (h3 : ¬ 3 ∣ n) {L : Type*} [Field L]
    (ω : L) (ν : ZMod n → L) :
    ∀ h ∈ Vfib ω ν, (∀ B ∈ blocks n, restrictBlock B h ∈ VfibBlock ω ν B) ∧
      h = ∑ B ∈ blocks n, restrictBlock B h := by
  have h4 := H19_four_dvd hn ha
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hev : Even n := even_iff_two_dvd.mpr h2
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  intro h hh
  obtain ⟨a1, b1, c1⟩ := hh
  refine ⟨fun B hB => ?_, ?_⟩
  · obtain ⟨k0, -, rfl⟩ := H19_mem_blocks hB
    refine ⟨⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩, fun k hk => ?_⟩
    · simp only [restrictBlock, a1 k hk, ite_self]
    · simp only [restrictBlock]
      by_cases hU : k ∈ (blockOf (orbit 3 k0)).biUnion id
      · rw [ite_eq_left (H29_U_mul3 hev hU), ite_eq_left hU]
        exact b1 k hk
      · rw [ite_eq_right (fun h' => hU (H29_U_of_mul3 hev hcop h')), ite_eq_right hU]
        ring
    · simp only [restrictBlock]
      by_cases hU : k ∈ (blockOf (orbit 3 k0)).biUnion id
      · rw [ite_eq_left (H29_U_neg hev hU), ite_eq_left (H29_U_add_half hev hU)]
        exact c1 k hk
      · have hn1 : -k ∉ (blockOf (orbit 3 k0)).biUnion id := fun h' => by
          have := H29_U_neg hev h'
          rw [neg_neg] at this
          exact hU this
        have hn2 : k + half n ∉ (blockOf (orbit 3 k0)).biUnion id := fun h' => by
          have := H29_U_add_half hev h'
          rw [H29_add_half_half hev] at this
          exact hU this
        rw [ite_eq_right hn1, ite_eq_right hn2]
        ring
    · simp only [restrictBlock]
      rw [ite_eq_right hk]
  · funext k
    rw [Finset.sum_apply]
    rcases Nat.even_or_odd k.val with hk | hk
    · rw [a1 k hk]
      symm
      apply Finset.sum_eq_zero
      intro B _
      simp only [restrictBlock, a1 k hk, ite_self]
    · have hB0 : blockOf (orbit 3 k) ∈ blocks n := H22_blockOf_mem_blocks hk
      have hk0 : k ∈ (blockOf (orbit 3 k)).biUnion id :=
        mem_biUnion.mpr ⟨orbit 3 k, H22_self_mem_blockOf _, H6_self_mem 3 k⟩
      rw [Finset.sum_eq_single_of_mem _ hB0 (fun B hB hne => ?_)]
      · simp only [restrictBlock]
        rw [ite_eq_left hk0]
      · simp only [restrictBlock]
        rw [ite_eq_right]
        intro hkB
        have hdisj : Disjoint (B.biUnion id) ((blockOf (orbit 3 k)).biUnion id) :=
          H19_blocks_disj hn ha h3 (mem_coe.mpr hB) (mem_coe.mpr hB0) hne
        exact Finset.disjoint_left.mp hdisj hkB hk0

/-- Part 2: `T` keeps each block space. -/
theorem H29_part2 {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) {L : Type*} [Field L] {ω : L}
    (hω : IsPrimitiveRoot ω n) {ν : ZMod n → L} (hν : ∀ k : ZMod n, ν (k + half n) = ν k) :
    ∀ B ∈ blocks n, ∀ h ∈ VfibBlock ω ν B, Tsh h ∈ VfibBlock ω ν B := by
  have h4 := H19_four_dvd hn ha
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hev : Even n := even_iff_two_dvd.mpr h2
  intro B hB h hh
  obtain ⟨k0, -, rfl⟩ := H19_mem_blocks hB
  refine ⟨H29_Tsh_Vfib h2 h4 hev hω hν hh.1, fun k hk => hh.2 _ ?_⟩
  intro hkm
  apply hk
  have := H29_U_add_half hev hkm
  rwa [H29_add_half_half hev] at this

/-- Part 3: case A. -/
theorem H29_partA {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type*} [Field L] [CharP L 3] {ω : L} (hω : IsPrimitiveRoot ω n) {f : ZMod n → L}
    (hf0 : ∀ k : ZMod n, Even k.val → f k = 0)
    (hf3 : ∀ k : ZMod n, Odd k.val → f (3 * k) = (ω ^ k.val) ^ 6 * f k ^ 3)
    (hfn : ∀ k : ZMod n, Odd k.val → f k * f (-k) = -1) :
    ∀ B ∈ blocksA n, ∀ O ∈ B, ∀ ρ ∈ O,
      Set.BijOn (fun h : ZMod n → L => h ρ) (VfibBlock ω (nuData f) B)
        {t | t ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * t} ∧
      ∀ h ∈ VfibBlock ω (nuData f) B, Tsh h ρ = (ω ^ ρ.val) ^ (O.card * qO B) * h ρ ^ qO B ∧
        nuData h ρ = (ω ^ ρ.val) ^ (O.card * qO B) * h ρ ^ (1 + qO B) := by
  classical
  have h4 := H19_four_dvd hn ha
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hev : Even n := even_iff_two_dvd.mpr h2
  have hn2 : 2 ≤ n := Nat.le_of_dvd (NeZero.pos n) h2
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have hω1 : ω ^ n = 1 := hω.pow_eq_one
  have hω0 : ω ≠ 0 := hω.ne_zero (NeZero.ne n)
  have hfne : ∀ k : ZMod n, Odd k.val → f k ≠ 0 := fun k hk =>
    left_ne_zero_of_mul (by rw [hfn k hk]; exact neg_ne_zero.mpr one_ne_zero)
  have hν : ∀ k : ZMod n, Odd k.val → nuData f k ≠ 0 := fun k hk =>
    mul_ne_zero (hfne k hk) (hfne _ (H19_odd_add_half h2 h4 hk))
  intro B hB O hO ρ hρO
  have hBb : B ∈ blocks n := (mem_filter.mp hB).1
  obtain ⟨hρ, rfl, rfl⟩ := H29_rep hn ha h3 hBb hO hρO
  have hA : IsCaseA (orbit 3 ρ) := (H22_caseA_iff hev _).mp (mem_filter.mp hB).2
  have hLev : Even (orbit 3 ρ).card :=
    caseAB_even_proved n a nodd hn ha hodd h3 _ (H22_orbit_mem_topOrbits hρ) (Or.inl hA)
  have hq : qO (blockOf (orbit 3 ρ)) = 3 ^ ((orbit 3 ρ).card / 2) := by
    unfold qO; rw [H22_blockLen hev h3]
  have hmem : ρ + half n ∈ orbit 3 ρ := by
    rw [← (show negO (orbit 3 ρ) = orbit 3 ρ from hA)]
    exact mem_image_of_mem _ (H6_self_mem 3 ρ)
  have hρm : ρ + half n = 3 ^ ((orbit 3 ρ).card / 2) * ρ := H19_caseA_pow hcop hev hn2 hmem
  have hoA : orbit 3 (ρ + half n) = orbit 3 ρ := H6_orbit_eq hcop hmem
  have hwrapρ : (3 : ZMod n) ^ (orbit 3 ρ).card * ρ = ρ :=
    (H19_pow_eq_self_iff' hcop (H6_self_mem 3 ρ) _).mpr dvd_rfl
  have hfV : f ρ ^ (3 ^ (orbit 3 ρ).card) = (ω ^ ρ.val)⁻¹ ^ (2 * (orbit 3 ρ).card) * f ρ :=
    H29_wrap h2 hω1 hω0 hf3 hρ hwrapρ
  have hc0 : (ω ^ ρ.val)⁻¹ ^ (2 * (orbit 3 ρ).card) ≠ 0 := pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ hω0))
  have hfρ := hfne ρ hρ
  refine ⟨⟨fun h hh => H29_wrap h2 hω1 hω0 hh.1.2.1 hρ hwrapρ, fun h1 hh1 h1' hh1' heq => ?_,
    fun t ht => ?_⟩, fun h hh => ?_⟩
  · -- injective
    have heq' : h1 ρ = h1' ρ := heq
    have hd := H29_block_sub hh1 hh1'
    have hd0 : (h1 - h1') ρ = 0 := by simp only [Pi.sub_apply, heq', sub_self]
    have hdm : (h1 - h1') (ρ + half n) = 0 := H29_zero_orbit h2 hω1 hd.1 hρ hd0 _ hmem
    exact sub_eq_zero.mp (H29_block_zero hev h2 h4 hω1 hν hρ hd hd0 hdm)
  · -- surjective
    have ht' : t ^ (3 ^ (orbit 3 ρ).card) = (ω ^ ρ.val)⁻¹ ^ (2 * (orbit 3 ρ).card) * t := ht
    have hxc : (t / f ρ) ^ (3 ^ (orbit 3 ρ).card) = t / f ρ := by
      rw [div_pow, ht', hfV, mul_div_mul_left _ _ hc0]
    have hnot : -ρ + half n ∉ orbit 3 ρ := by
      intro hm
      have e := H6_orbit_eq hcop hm
      rw [H7_neg_add_half hev, ← H6_inv_orbit, hoA] at e
      exact H19_top_mem hn ha hodd h3 hρ e
    refine ⟨fun k => f k * H29_Psi ρ (t / f ρ) k,
      H29_mk_block _ hf0 hf3 hfn (H29_Psi_mul3 hev h3 hxc) (H29_Psi_neg ρ _)
        (fun k hk => H29_Psi_supp hev _ hk), ?_⟩
    show f ρ * H29_Psi ρ (t / f ρ) ρ = t
    unfold H29_Psi
    rw [H29_P_self h3 hxc, H29_P_zero _ hnot, add_zero]
    field_simp
  · -- T and the ν-datum
    have hit := H29_iter h2 hω1 hh.1.2.1 hρ ((orbit 3 ρ).card / 2)
    rw [← hρm, Nat.two_mul_div_two_of_even hLev] at hit
    rw [hq]
    refine ⟨?_, ?_⟩
    · show h (ρ + half n) = _
      rw [hit]
    · show h ρ * h (ρ + half n) = _
      rw [hit]
      ring

/-- Part 4: case C. -/
theorem H29_partC {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type*} [Field L] [CharP L 3] {ω : L} (hω : IsPrimitiveRoot ω n) {f : ZMod n → L}
    (hf0 : ∀ k : ZMod n, Even k.val → f k = 0)
    (hf3 : ∀ k : ZMod n, Odd k.val → f (3 * k) = (ω ^ k.val) ^ 6 * f k ^ 3)
    (hfn : ∀ k : ZMod n, Odd k.val → f k * f (-k) = -1) :
    ∀ B ∈ blocksC n, ∀ O ∈ B, ∀ ρ ∈ O,
      Set.BijOn (fun h : ZMod n → L => (h ρ, h (ρ + half n))) (VfibBlock ω (nuData f) B)
        ({t | t ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * t} ×ˢ
          {t | t ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * t}) ∧
      ∀ h ∈ VfibBlock ω (nuData f) B, Tsh h ρ = h (ρ + half n) ∧ Tsh h (ρ + half n) = h ρ := by
  classical
  have h4 := H19_four_dvd hn ha
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hev : Even n := even_iff_two_dvd.mpr h2
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have hω1 : ω ^ n = 1 := hω.pow_eq_one
  have hω0 : ω ≠ 0 := hω.ne_zero (NeZero.ne n)
  have hfne : ∀ k : ZMod n, Odd k.val → f k ≠ 0 := fun k hk =>
    left_ne_zero_of_mul (by rw [hfn k hk]; exact neg_ne_zero.mpr one_ne_zero)
  have hν : ∀ k : ZMod n, Odd k.val → nuData f k ≠ 0 := fun k hk =>
    mul_ne_zero (hfne k hk) (hfne _ (H19_odd_add_half h2 h4 hk))
  intro B hB O hO ρ hρO
  have hBb : B ∈ blocks n := (mem_filter.mp hB).1
  obtain ⟨hρ, rfl, rfl⟩ := H29_rep hn ha h3 hBb hO hρO
  have hC := (mem_filter.mp hB).2 (orbit 3 ρ) (H22_self_mem_blockOf _)
  have hnA : orbit 3 (ρ + half n) ≠ orbit 3 ρ := fun e =>
    hC.1 (by unfold IsCaseA; rw [H19_negO_orbit hev]; exact e)
  have hnB : orbit 3 (ρ + half n) ≠ orbit 3 (-ρ) := fun e =>
    hC.2 (by unfold IsCaseB; rw [H19_negO_orbit hev, H6_inv_orbit]; exact e)
  have hρm : Odd (ρ + half n).val := H19_odd_add_half h2 h4 hρ
  have hwrapρ : (3 : ZMod n) ^ (orbit 3 ρ).card * ρ = ρ :=
    (H19_pow_eq_self_iff' hcop (H6_self_mem 3 ρ) _).mpr dvd_rfl
  have hwrapm : (3 : ZMod n) ^ (orbit 3 ρ).card * (ρ + half n) = ρ + half n := by
    rw [mul_add, hwrapρ, H19_pow_mul_half hev]
  have hcardm : (orbit 3 (ρ + half n)).card = (orbit 3 ρ).card := by
    rw [← H19_negO_orbit hev, H22_card_negO]
  have hfV : f ρ ^ (3 ^ (orbit 3 ρ).card) = (ω ^ ρ.val)⁻¹ ^ (2 * (orbit 3 ρ).card) * f ρ :=
    H29_wrap h2 hω1 hω0 hf3 hρ hwrapρ
  have hfVm : f (ρ + half n) ^ (3 ^ (orbit 3 ρ).card) =
      (ω ^ ρ.val)⁻¹ ^ (2 * (orbit 3 ρ).card) * f (ρ + half n) := by
    rw [← H29_c_shift hev hω ρ]
    exact H29_wrap h2 hω1 hω0 hf3 hρm hwrapm
  have hc0 : (ω ^ ρ.val)⁻¹ ^ (2 * (orbit 3 ρ).card) ≠ 0 := pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ hω0))
  have hfρ := hfne ρ hρ
  have hfρm := hfne _ hρm
  refine ⟨⟨fun h hh => ⟨H29_wrap h2 hω1 hω0 hh.1.2.1 hρ hwrapρ, ?_⟩, fun h1 hh1 h1' hh1' heq => ?_,
    fun p hp => ?_⟩, fun h hh => ⟨rfl, ?_⟩⟩
  · -- maps to, second coordinate
    show h (ρ + half n) ^ (3 ^ (orbit 3 ρ).card) = (ω ^ ρ.val)⁻¹ ^ (2 * (orbit 3 ρ).card) * h (ρ + half n)
    rw [← H29_c_shift hev hω ρ]
    exact H29_wrap h2 hω1 hω0 hh.1.2.1 hρm hwrapm
  · -- injective
    simp only [Prod.mk.injEq] at heq
    obtain ⟨e1, e2⟩ := heq
    have hd := H29_block_sub hh1 hh1'
    have hd0 : (h1 - h1') ρ = 0 := by simp only [Pi.sub_apply, e1, sub_self]
    have hdm : (h1 - h1') (ρ + half n) = 0 := by simp only [Pi.sub_apply, e2, sub_self]
    exact sub_eq_zero.mp (H29_block_zero hev h2 h4 hω1 hν hρ hd hd0 hdm)
  · -- surjective
    obtain ⟨t, t'⟩ := p
    obtain ⟨ht, ht'⟩ := hp
    have ht1 : t ^ (3 ^ (orbit 3 ρ).card) = (ω ^ ρ.val)⁻¹ ^ (2 * (orbit 3 ρ).card) * t := ht
    have ht2 : t' ^ (3 ^ (orbit 3 ρ).card) = (ω ^ ρ.val)⁻¹ ^ (2 * (orbit 3 ρ).card) * t' := ht'
    have hxc : (t / f ρ) ^ (3 ^ (orbit 3 ρ).card) = t / f ρ := by
      rw [div_pow, ht1, hfV, mul_div_mul_left _ _ hc0]
    have hxc' : (t' / f (ρ + half n)) ^ (3 ^ (orbit 3 (ρ + half n)).card) = t' / f (ρ + half n) := by
      rw [hcardm, div_pow, ht2, hfVm, mul_div_mul_left _ _ hc0]
    -- non-membership facts
    have nm1 : -ρ + half n ∉ orbit 3 ρ := by
      intro hm
      have e := H6_orbit_eq hcop hm
      rw [H7_neg_add_half hev] at e
      apply hnB
      apply H29_orbit_neg_inj
      rw [e, neg_neg]
    have nm2 : ρ ∉ orbit 3 (ρ + half n) := fun hm => hnA (H6_orbit_eq hcop hm).symm
    have nm3 : -ρ + half n ∉ orbit 3 (ρ + half n) := by
      intro hm
      have e := H6_orbit_eq hcop hm
      rw [H7_neg_add_half hev] at e
      exact H29_orbit_neg_ne hn ha hodd h3 hρm e
    have nm4 : ρ + half n ∉ orbit 3 ρ := fun hm => hnA (H6_orbit_eq hcop hm)
    have nm5 : -ρ ∉ orbit 3 ρ := fun hm => H29_orbit_neg_ne hn ha hodd h3 hρ (H6_orbit_eq hcop hm)
    have nm6 : -ρ ∉ orbit 3 (ρ + half n) := fun hm => hnB (H6_orbit_eq hcop hm).symm
    have hblk := H29_blockOf_add_half hev ρ
    refine ⟨fun k => f k * (H29_Psi ρ (t / f ρ) k + H29_Psi (ρ + half n) (t' / f (ρ + half n)) k),
      H29_mk_block _ hf0 hf3 hfn (fun k => ?_) (fun k => ?_) (fun k hk => ?_), ?_⟩
    · show H29_Psi ρ _ (3 * k) + H29_Psi (ρ + half n) _ (3 * k) = (H29_Psi ρ _ k + H29_Psi (ρ + half n) _ k) ^ 3
      rw [H29_Psi_mul3 hev h3 hxc, H29_Psi_mul3 hev h3 hxc', add_pow_char]
    · show H29_Psi ρ _ (-k) + H29_Psi (ρ + half n) _ (-k) =
        H29_Psi ρ _ (k + half n) + H29_Psi (ρ + half n) _ (k + half n)
      rw [H29_Psi_neg, H29_Psi_neg]
    · show H29_Psi ρ _ k + H29_Psi (ρ + half n) _ k = 0
      rw [H29_Psi_supp hev _ hk, H29_Psi_supp hev _ (by rw [hblk]; exact hk), add_zero]
    · show (f ρ * (H29_Psi ρ _ ρ + H29_Psi (ρ + half n) _ ρ),
        f (ρ + half n) * (H29_Psi ρ _ (ρ + half n) + H29_Psi (ρ + half n) _ (ρ + half n))) = (t, t')
      unfold H29_Psi
      rw [show -(ρ + half n) + half n = -ρ by ring]
      rw [H29_P_self h3 hxc, H29_P_zero _ nm1, H29_P_zero _ nm2, H29_P_zero _ nm3, H29_P_zero _ nm4,
        H29_P_zero _ nm5, H29_P_self h3 hxc', H29_P_zero _ nm6]
      simp only [add_zero, zero_add]
      refine Prod.ext ?_ ?_
      · show f ρ * (t / f ρ) = t
        field_simp
      · show f (ρ + half n) * (t' / f (ρ + half n)) = t'
        field_simp
  · -- T, second formula
    show h (ρ + half n + half n) = h ρ
    rw [H29_add_half_half hev]

/-- Part 5: case B. -/
theorem H29_partB {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type*} [Field L] [CharP L 3] {ω : L} (hω : IsPrimitiveRoot ω n) {f : ZMod n → L}
    (hf0 : ∀ k : ZMod n, Even k.val → f k = 0)
    (hf3 : ∀ k : ZMod n, Odd k.val → f (3 * k) = (ω ^ k.val) ^ 6 * f k ^ 3)
    (hfn : ∀ k : ZMod n, Odd k.val → f k * f (-k) = -1) :
    ∀ B ∈ blocksB n, ∀ O ∈ B, ∀ ρ ∈ O,
      Set.BijOn (fun h : ZMod n → L => (h ρ / f ρ, -(f ρ * h (-ρ)))) (VfibBlock ω (nuData f) B)
        ({x | x ^ qO B = x} ×ˢ {x | x ^ qO B = x}) ∧
      ∀ h ∈ VfibBlock ω (nuData f) B,
        Tsh h ρ / f ρ = (-((ω ^ ρ.val)⁻¹ ^ (O.card * qO B)) * (f ρ)⁻¹ ^ (1 + qO B)) *
            (-(f ρ * h (-ρ))) ∧
        -(f ρ * Tsh h (-ρ)) = (h ρ / f ρ) /
            (-((ω ^ ρ.val)⁻¹ ^ (O.card * qO B)) * (f ρ)⁻¹ ^ (1 + qO B)) ∧
        (Tsh h ρ / f ρ) * (-(f ρ * Tsh h (-ρ))) = (h ρ / f ρ) * (-(f ρ * h (-ρ))) := by
  classical
  have h4 := H19_four_dvd hn ha
  have h8 := H19_eight_dvd hn ha
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hev : Even n := even_iff_two_dvd.mpr h2
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have hω1 : ω ^ n = 1 := hω.pow_eq_one
  have hω0 : ω ≠ 0 := hω.ne_zero (NeZero.ne n)
  have hfne : ∀ k : ZMod n, Odd k.val → f k ≠ 0 := fun k hk =>
    left_ne_zero_of_mul (by rw [hfn k hk]; exact neg_ne_zero.mpr one_ne_zero)
  have hν : ∀ k : ZMod n, Odd k.val → nuData f k ≠ 0 := fun k hk =>
    mul_ne_zero (hfne k hk) (hfne _ (H19_odd_add_half h2 h4 hk))
  have h30 : (3 : L) = 0 := H29_three_eq_zero
  intro B hB O hO ρ hρO
  have hBb : B ∈ blocks n := (mem_filter.mp hB).1
  obtain ⟨hρ, rfl, rfl⟩ := H29_rep hn ha h3 hBb hO hρO
  have hBc : IsCaseB (orbit 3 ρ) := (H22_caseB_iff hev _).mp (mem_filter.mp hB).2
  have hLev : Even (orbit 3 ρ).card :=
    caseAB_even_proved n a nodd hn ha hodd h3 _ (H22_orbit_mem_topOrbits hρ) (Or.inr hBc)
  have hq : qO (blockOf (orbit 3 ρ)) = 3 ^ ((orbit 3 ρ).card / 2) := by
    unfold qO; rw [H22_blockLen hev h3]
  have hmemB : -(ρ + half n) ∈ orbit 3 ρ := by
    have h1 : ρ + half n ∈ inv (orbit 3 ρ) := by
      rw [← (show negO (orbit 3 ρ) = inv (orbit 3 ρ) from hBc)]
      exact mem_image_of_mem _ (H6_self_mem 3 ρ)
    exact (H11_mem_inv _ _).mp h1
  have hρm : ρ + half n = -((3 : ZMod n) ^ ((orbit 3 ρ).card / 2) * ρ) := H19_caseB_pow hcop h8 hρ hmemB
  have hρm' : ρ + half n = (3 : ZMod n) ^ ((orbit 3 ρ).card / 2) * (-ρ) := by rw [hρm]; ring
  have hnegm : -ρ + half n = (3 : ZMod n) ^ ((orbit 3 ρ).card / 2) * ρ := by
    rw [H7_neg_add_half hev, hρm, neg_neg]
  have hnρ : Odd (-ρ).val := H6_odd_neg h2 hρ
  have hρmo : Odd (ρ + half n).val := H19_odd_add_half h2 h4 hρ
  have hfρ := hfne ρ hρ
  have hX0 : ω ^ ρ.val ≠ 0 := pow_ne_zero _ hω0
  have hqodd : Odd ((3 : ℕ) ^ ((orbit 3 ρ).card / 2)) := Odd.pow (by decide)
  have e2L : 2 * ((orbit 3 ρ).card / 2) = (orbit 3 ρ).card := Nat.two_mul_div_two_of_even hLev
  -- (F1) iterated to `-ρ + m` (from `ρ`) and to `ρ + m` (from `-ρ`)
  have hitR : ∀ h : ZMod n → L, (∀ k : ZMod n, Odd k.val → h (3 * k) = (ω ^ k.val) ^ 6 * h k ^ 3) →
      h (-ρ + half n) = (ω ^ ρ.val) ^ ((orbit 3 ρ).card * 3 ^ ((orbit 3 ρ).card / 2)) *
        h ρ ^ (3 ^ ((orbit 3 ρ).card / 2)) := by
    intro h hF
    have := H29_iter h2 hω1 hF hρ ((orbit 3 ρ).card / 2)
    rw [← hnegm, e2L] at this
    exact this
  have hitN : ∀ h : ZMod n → L, (∀ k : ZMod n, Odd k.val → h (3 * k) = (ω ^ k.val) ^ 6 * h k ^ 3) →
      h (ρ + half n) = (ω ^ ρ.val)⁻¹ ^ ((orbit 3 ρ).card * 3 ^ ((orbit 3 ρ).card / 2)) *
        h (-ρ) ^ (3 ^ ((orbit 3 ρ).card / 2)) := by
    intro h hF
    have := H29_iter h2 hω1 hF hnρ ((orbit 3 ρ).card / 2)
    rw [← hρm', e2L, H4_pow_val_neg hω1] at this
    exact this
  have hq0 : (ω ^ ρ.val) ^ ((orbit 3 ρ).card * 3 ^ ((orbit 3 ρ).card / 2)) ≠ 0 := pow_ne_zero _ hX0
  -- the ν-data at `ρ` and `-ρ`
  have ef : f ρ * nuData f (-ρ) = -((ω ^ ρ.val) ^ ((orbit 3 ρ).card * 3 ^ ((orbit 3 ρ).card / 2)) *
      f ρ ^ (3 ^ ((orbit 3 ρ).card / 2))) := by
    show f ρ * (f (-ρ) * f (-ρ + half n)) = _
    rw [← mul_assoc, hfn ρ hρ, hitR f hf3]
    ring
  have hνν : nuData f ρ * nuData f (-ρ) = 1 := H29_nu_inv hev h2 h4 hfn hρ
  have hXY : (ω ^ ρ.val) ^ ((orbit 3 ρ).card * 3 ^ ((orbit 3 ρ).card / 2)) *
      (ω ^ ρ.val)⁻¹ ^ ((orbit 3 ρ).card * 3 ^ ((orbit 3 ρ).card / 2)) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hX0, one_pow]
  -- non-membership facts
  have hmemR : -ρ + half n ∈ orbit 3 ρ := H19_mem_orbit3.mpr ⟨_, hnegm⟩
  have hmemN : ρ + half n ∈ orbit 3 (-ρ) := H19_mem_orbit3.mpr ⟨_, hρm'⟩
  have nm1 : ρ ∉ orbit 3 (-ρ) := fun hm => H29_orbit_neg_ne hn ha hodd h3 hρ (H6_orbit_eq hcop hm).symm
  have nm2 : -ρ + half n ∉ orbit 3 (-ρ) := fun hm =>
    H29_orbit_neg_ne hn ha hodd h3 hρ ((H6_orbit_eq hcop hm).symm.trans (H6_orbit_eq hcop hmemR))
  have nm3 : -ρ ∉ orbit 3 ρ := fun hm => H29_orbit_neg_ne hn ha hodd h3 hρ (H6_orbit_eq hcop hm)
  have nm4 : ρ + half n ∉ orbit 3 ρ := fun hm =>
    H29_orbit_neg_ne hn ha hodd h3 hρ ((H6_orbit_eq hcop hmemN).symm.trans (H6_orbit_eq hcop hm))
  have hcardN : (orbit 3 (-ρ)).card = (orbit 3 ρ).card := by rw [← H6_inv_orbit, H6_card_inv]
  rw [hq]
  refine ⟨⟨fun h hh => ⟨?_, ?_⟩, fun h1 hh1 h1' hh1' heq => ?_, fun p hp => ?_⟩, fun h hh => ?_⟩
  · -- maps to: first coordinate
    show (h ρ / f ρ) ^ (3 ^ ((orbit 3 ρ).card / 2)) = h ρ / f ρ
    have eh : h ρ * nuData f (-ρ) = -((ω ^ ρ.val) ^ ((orbit 3 ρ).card * 3 ^ ((orbit 3 ρ).card / 2)) *
        h ρ ^ (3 ^ ((orbit 3 ρ).card / 2))) := by
      have := hh.1.2.2 (-ρ) hnρ
      rw [neg_neg, hitR h hh.1.2.1] at this
      exact this
    rw [div_pow, div_eq_div_iff (pow_ne_zero _ hfρ) hfρ]
    apply mul_left_cancel₀ hq0
    linear_combination f ρ * eh - h ρ * ef
  · -- maps to: second coordinate
    show (-(f ρ * h (-ρ))) ^ (3 ^ ((orbit 3 ρ).card / 2)) = -(f ρ * h (-ρ))
    have eh2 : h (-ρ) * nuData f ρ = -((ω ^ ρ.val)⁻¹ ^ ((orbit 3 ρ).card * 3 ^ ((orbit 3 ρ).card / 2)) *
        h (-ρ) ^ (3 ^ ((orbit 3 ρ).card / 2))) := by
      have := hh.1.2.2 ρ hρ
      rw [hitN h hh.1.2.1] at this
      exact this
    rw [Odd.neg_pow hqodd, mul_pow, neg_inj]
    linear_combination (-(f ρ ^ (3 ^ ((orbit 3 ρ).card / 2)) * h (-ρ) ^ (3 ^ ((orbit 3 ρ).card / 2)))) * hXY +
      ((ω ^ ρ.val)⁻¹ ^ ((orbit 3 ρ).card * 3 ^ ((orbit 3 ρ).card / 2)) * h (-ρ) ^ (3 ^ ((orbit 3 ρ).card / 2))) * ef -
      (f ρ * nuData f (-ρ)) * eh2 + (f ρ * h (-ρ)) * hνν
  · -- injective
    simp only [Prod.mk.injEq] at heq
    obtain ⟨e1, e2⟩ := heq
    have e1' : h1 ρ = h1' ρ := (div_left_inj' hfρ).mp e1
    have e2' : h1 (-ρ) = h1' (-ρ) := mul_left_cancel₀ hfρ (neg_inj.mp e2)
    have hd := H29_block_sub hh1 hh1'
    have hd0 : (h1 - h1') ρ = 0 := by simp only [Pi.sub_apply, e1', sub_self]
    have hdn : (h1 - h1') (-ρ) = 0 := by simp only [Pi.sub_apply, e2', sub_self]
    have hdm : (h1 - h1') (ρ + half n) = 0 := H29_zero_orbit h2 hω1 hd.1 hnρ hdn _ hmemN
    exact sub_eq_zero.mp (H29_block_zero hev h2 h4 hω1 hν hρ hd hd0 hdm)
  · -- surjective
    obtain ⟨x, x'⟩ := p
    obtain ⟨hx, hx'⟩ := hp
    have hx1 : x ^ (3 ^ ((orbit 3 ρ).card / 2)) = x := hx
    have hx1' : x' ^ (3 ^ ((orbit 3 ρ).card / 2)) = x' := hx'
    have hc1 : (-x) ^ (3 ^ (orbit 3 ρ).card) = -x := H29_negpow hLev hx1
    have hc2 : (-x') ^ (3 ^ (orbit 3 (-ρ)).card) = -x' := by rw [hcardN]; exact H29_negpow hLev hx1'
    have hblk := H29_blockOf_neg hev ρ
    have hφρ : H29_Psi ρ (-x) ρ + H29_Psi (-ρ) (-x') ρ = x := by
      unfold H29_Psi
      rw [H29_P_self h3 hc1, H29_P_eq h3 hc1 hnegm, H29_P_zero _ nm1, H29_P_zero _ nm2, Odd.neg_pow hqodd, hx1]
      linear_combination (-x) * h30
    have hφn : H29_Psi ρ (-x) (-ρ) + H29_Psi (-ρ) (-x') (-ρ) = x' := by
      unfold H29_Psi
      rw [neg_neg, H29_P_zero _ nm3, H29_P_zero _ nm4, H29_P_self h3 hc2, H29_P_eq h3 hc2 hρm',
        Odd.neg_pow hqodd, hx1']
      linear_combination (-x') * h30
    refine ⟨fun k => f k * (H29_Psi ρ (-x) k + H29_Psi (-ρ) (-x') k),
      H29_mk_block _ hf0 hf3 hfn (fun k => ?_) (fun k => ?_) (fun k hk => ?_), ?_⟩
    · show H29_Psi ρ _ (3 * k) + H29_Psi (-ρ) _ (3 * k) = (H29_Psi ρ _ k + H29_Psi (-ρ) _ k) ^ 3
      rw [H29_Psi_mul3 hev h3 hc1, H29_Psi_mul3 hev h3 hc2, add_pow_char]
    · show H29_Psi ρ _ (-k) + H29_Psi (-ρ) _ (-k) = H29_Psi ρ _ (k + half n) + H29_Psi (-ρ) _ (k + half n)
      rw [H29_Psi_neg, H29_Psi_neg]
    · show H29_Psi ρ _ k + H29_Psi (-ρ) _ k = 0
      rw [H29_Psi_supp hev _ hk, H29_Psi_supp hev _ (by rw [hblk]; exact hk), add_zero]
    · show (f ρ * (H29_Psi ρ (-x) ρ + H29_Psi (-ρ) (-x') ρ) / f ρ,
        -(f ρ * (f (-ρ) * (H29_Psi ρ (-x) (-ρ) + H29_Psi (-ρ) (-x') (-ρ))))) = (x, x')
      rw [hφρ, hφn]
      refine Prod.ext ?_ ?_
      · show f ρ * x / f ρ = x
        field_simp
      · show -(f ρ * (f (-ρ) * x')) = x'
        linear_combination (-x') * hfn ρ hρ
  · -- T formulas
    have hTρ : Tsh h ρ = -(h (-ρ) * nuData f ρ) := by
      show h (ρ + half n) = _
      have := hh.1.2.2 ρ hρ
      linear_combination this
    have hTn : Tsh h (-ρ) = -(h ρ * nuData f (-ρ)) := by
      show h (-ρ + half n) = _
      have := hh.1.2.2 (-ρ) hnρ
      rw [neg_neg] at this
      linear_combination this
    have hfm : f (ρ + half n) * ((ω ^ ρ.val) ^ ((orbit 3 ρ).card * 3 ^ ((orbit 3 ρ).card / 2)) *
        f ρ ^ (3 ^ ((orbit 3 ρ).card / 2))) = -1 := by
      have := hfn (ρ + half n) hρmo
      rw [← H7_neg_add_half hev, hitR f hf3] at this
      exact this
    have hA'E : (ω ^ ρ.val) ^ ((orbit 3 ρ).card * 3 ^ ((orbit 3 ρ).card / 2)) * f ρ ^ (3 ^ ((orbit 3 ρ).card / 2)) * ((ω ^ ρ.val)⁻¹ ^ ((orbit 3 ρ).card * 3 ^ ((orbit 3 ρ).card / 2)) * (f ρ)⁻¹ ^ (3 ^ ((orbit 3 ρ).card / 2))) = 1 := by
      rw [show (ω ^ ρ.val) ^ ((orbit 3 ρ).card * 3 ^ ((orbit 3 ρ).card / 2)) * f ρ ^ (3 ^ ((orbit 3 ρ).card / 2)) * ((ω ^ ρ.val)⁻¹ ^ ((orbit 3 ρ).card * 3 ^ ((orbit 3 ρ).card / 2)) * (f ρ)⁻¹ ^ (3 ^ ((orbit 3 ρ).card / 2))) =
        (ω ^ ρ.val * (ω ^ ρ.val)⁻¹) ^ ((orbit 3 ρ).card * 3 ^ ((orbit 3 ρ).card / 2)) * (f ρ * (f ρ)⁻¹) ^ (3 ^ ((orbit 3 ρ).card / 2)) by ring,
        mul_inv_cancel₀ hX0, mul_inv_cancel₀ hfρ, one_pow, one_pow, one_mul]
    have hF' : f (ρ + half n) = -((ω ^ ρ.val)⁻¹ ^ ((orbit 3 ρ).card * 3 ^ ((orbit 3 ρ).card / 2)) * (f ρ)⁻¹ ^ (3 ^ ((orbit 3 ρ).card / 2))) := by
      linear_combination ((ω ^ ρ.val)⁻¹ ^ ((orbit 3 ρ).card * 3 ^ ((orbit 3 ρ).card / 2)) * (f ρ)⁻¹ ^ (3 ^ ((orbit 3 ρ).card / 2))) * hfm - f (ρ + half n) * hA'E
    have hfn' : f (-ρ) = -(f ρ)⁻¹ := by
      linear_combination (f ρ)⁻¹ * hfn ρ hρ - f (-ρ) * mul_inv_cancel₀ hfρ
    have hu : f ρ * (f ρ)⁻¹ = 1 := mul_inv_cancel₀ hfρ
    have huq : f ρ ^ (3 ^ ((orbit 3 ρ).card / 2)) * (f ρ)⁻¹ ^ (3 ^ ((orbit 3 ρ).card / 2)) = 1 := by rw [← mul_pow, mul_inv_cancel₀ hfρ, one_pow]
    have hδ : -((ω ^ ρ.val)⁻¹ ^ ((orbit 3 ρ).card * 3 ^ ((orbit 3 ρ).card / 2))) * (f ρ)⁻¹ ^ (1 + (3 ^ ((orbit 3 ρ).card / 2))) ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (inv_ne_zero hX0))) (pow_ne_zero _ (inv_ne_zero hfρ))
    have hB1 : Tsh h ρ / f ρ = (-((ω ^ ρ.val)⁻¹ ^ ((orbit 3 ρ).card * 3 ^ ((orbit 3 ρ).card / 2))) * (f ρ)⁻¹ ^ (1 + (3 ^ ((orbit 3 ρ).card / 2)))) * (-(f ρ * h (-ρ))) := by
      rw [hTρ]
      show -(h (-ρ) * (f ρ * f (ρ + half n))) / f ρ = _
      rw [hF', div_eq_mul_inv]
      ring
    have hB2 : -(f ρ * Tsh h (-ρ)) = (h ρ / f ρ) / (-((ω ^ ρ.val)⁻¹ ^ ((orbit 3 ρ).card * 3 ^ ((orbit 3 ρ).card / 2))) * (f ρ)⁻¹ ^ (1 + (3 ^ ((orbit 3 ρ).card / 2)))) := by
      rw [hTn, eq_div_iff hδ, show nuData f (-ρ) = f (-ρ) * f (-ρ + half n) from rfl, hfn', hitR f hf3]
      linear_combination (h ρ * (f ρ)⁻¹ * (f ρ ^ (3 ^ ((orbit 3 ρ).card / 2)) * (f ρ)⁻¹ ^ (3 ^ ((orbit 3 ρ).card / 2))) *
          ((ω ^ ρ.val) ^ ((orbit 3 ρ).card * 3 ^ ((orbit 3 ρ).card / 2)) * (ω ^ ρ.val)⁻¹ ^ ((orbit 3 ρ).card * 3 ^ ((orbit 3 ρ).card / 2)))) * hu +
        (h ρ * (f ρ)⁻¹ * ((ω ^ ρ.val) ^ ((orbit 3 ρ).card * 3 ^ ((orbit 3 ρ).card / 2)) * (ω ^ ρ.val)⁻¹ ^ ((orbit 3 ρ).card * 3 ^ ((orbit 3 ρ).card / 2)))) * huq + (h ρ * (f ρ)⁻¹) * hXY
    refine ⟨hB1, hB2, ?_⟩
    rw [hB1, hB2]
    linear_combination (h ρ / f ρ * -(f ρ * h (-ρ))) * mul_inv_cancel₀ hδ

end H29Parts

/-! ## 6. The row -/

/-- Row 18V(c-blocks) — Theorem 5.1(c), the block parameter spaces (s5_twonorms.tex:24-33, Table 1). -/
theorem thm_5_1_c_V_blocks_proved (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2) :
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
        (Tsh h ρ / topOf ω y ρ) * (-(topOf ω y ρ * Tsh h (-ρ))) = (h ρ / topOf ω y ρ) * (-(topOf ω y ρ * h (-ρ)))) := by
  intro ν
  have := H19_charP n (L := L)
  have h4 := H19_four_dvd hn ha
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hev : Even n := even_iff_two_dvd.mpr h2
  obtain ⟨hf0, hf3, hfn⟩ := H29_top hev h3 hω hy
  exact ⟨H29_part1 hn ha h3 ω ν, H29_part2 hn ha hω (H29_nu_half hev (topOf ω y)),
    H29_partA hn ha hodd h3 hω hf0 hf3 hfn, H29_partC hn ha hodd h3 hω hf0 hf3 hfn,
    H29_partB hn ha hodd h3 hω hf0 hf3 hfn⟩

end Xia.Proofs

#print axioms Xia.Proofs.thm_5_1_c_V_blocks_proved
