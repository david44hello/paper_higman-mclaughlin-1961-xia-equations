/- Xia/Proofs/Thm41Steps26.lean — proofs of the rows thm_4_1_step2, thm_4_1_step6 of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry
import Xia.Defs.Layer0

namespace Xia.Proofs

open Xia Finset

set_option linter.unusedSectionVars false

theorem H11_three_pow_mod8 (i : ℕ) : 3 ^ i % 8 = 1 ∨ 3 ^ i % 8 = 3 := by
  induction i with
  | zero => left; rfl
  | succ i ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h1 | h1 <;> rw [h1] <;> simp

/-! ## 1. Parity, the unit `3`, minimal periods of `k ↦ 3k` -/

section Basic

variable {n : ℕ} [NeZero n]

theorem H11_odd_iff (hn2 : 2 ∣ n) (k : ZMod n) : Odd k.val ↔ ZMod.castHom hn2 (ZMod 2) k = 1 := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_one_iff_odd]

theorem H11_odd_mul3 (hn2 : 2 ∣ n) {k : ZMod n} (hk : Odd k.val) : Odd (3 * k).val := by
  rw [H11_odd_iff hn2] at hk ⊢
  rw [map_mul, hk, mul_one, map_ofNat]
  decide

theorem H11_odd_neg (hn2 : 2 ∣ n) {k : ZMod n} (hk : Odd k.val) : Odd (-k).val := by
  rw [H11_odd_iff hn2] at hk ⊢
  rw [map_neg, hk]
  decide

theorem H11_pow_odd (hn2 : 2 ∣ n) (i : ℕ) {k : ZMod n} (hk : Odd k.val) : Odd ((3 : ZMod n) ^ i * k).val := by
  induction i with
  | zero => simpa using hk
  | succ i ih =>
    rw [show (3 : ZMod n) ^ (i + 1) * k = 3 * (3 ^ i * k) by ring]
    exact H11_odd_mul3 hn2 ih

theorem H11_orderOf_pos (h3 : ¬ 3 ∣ n) : 0 < orderOf (3 : ZMod n) := by
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have hu : ((ZMod.unitOfCoprime 3 hcop : (ZMod n)ˣ) : ZMod n) = 3 := by
    rw [ZMod.coe_unitOfCoprime, Nat.cast_ofNat]
  rw [← hu, orderOf_units]
  exact orderOf_pos _

/-- `3^i` has an inverse which is a power of `3`. -/
theorem H11_inv_pow (h3 : ¬ 3 ∣ n) (i : ℕ) : ∃ j : ℕ, (3 : ZMod n) ^ j * 3 ^ i = 1 := by
  refine ⟨(orderOf (3 : ZMod n) - 1) * i, ?_⟩
  have hN := H11_orderOf_pos (n := n) h3
  have he : (orderOf (3 : ZMod n) - 1) * i + i = orderOf (3 : ZMod n) * i := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hN]
  rw [← pow_add, he, pow_mul, pow_orderOf_eq_one, one_pow]

theorem H11_cancel (h3 : ¬ 3 ∣ n) {i : ℕ} {x y : ZMod n} (h : 3 ^ i * x = 3 ^ i * y) : x = y := by
  obtain ⟨j, hj⟩ := H11_inv_pow h3 i
  calc x = 3 ^ j * (3 ^ i * x) := by rw [← mul_assoc, hj, one_mul]
    _ = 3 ^ j * (3 ^ i * y) := by rw [h]
    _ = y := by rw [← mul_assoc, hj, one_mul]

/-- The minimal period of `k` under `k ↦ 3k` (= the length of the orbit of `k`). -/
noncomputable def H11_per (x : ZMod n) : ℕ := Function.minimalPeriod (fun y : ZMod n => 3 * y) x

theorem H11_iter (i : ℕ) (x : ZMod n) : (fun y : ZMod n => 3 * y)^[i] x = 3 ^ i * x :=
  congrFun (mul_left_iterate (3 : ZMod n) i) x

theorem H11_per_pos (h3 : ¬ 3 ∣ n) (x : ZMod n) : 0 < H11_per x := by
  apply Function.minimalPeriod_pos_of_mem_periodicPts
  refine Function.mk_mem_periodicPts (H11_orderOf_pos h3) ?_
  show (fun y : ZMod n => 3 * y)^[orderOf (3 : ZMod n)] x = x
  rw [H11_iter, pow_orderOf_eq_one, one_mul]

theorem H11_pow_per (x : ZMod n) : 3 ^ H11_per x * x = x := by
  rw [← H11_iter]
  exact Function.iterate_minimalPeriod

theorem H11_pow_mod (x : ZMod n) (i : ℕ) : 3 ^ (i % H11_per x) * x = 3 ^ i * x := by
  rw [← H11_iter, ← H11_iter]
  exact Function.iterate_mod_minimalPeriod_eq

theorem H11_per_dvd {x : ZMod n} {i : ℕ} (h : 3 ^ i * x = x) : H11_per x ∣ i := by
  apply Function.IsPeriodicPt.minimalPeriod_dvd
  show (fun y : ZMod n => 3 * y)^[i] x = x
  rw [H11_iter]
  exact h

theorem H11_inj {x : ZMod n} {i j : ℕ} (hi : i < H11_per x) (hj : j < H11_per x)
    (h : 3 ^ i * x = 3 ^ j * x) : i = j := by
  apply Function.iterate_injOn_Iio_minimalPeriod (f := fun y : ZMod n => 3 * y) (x := x) hi hj
  show (fun y : ZMod n => 3 * y)^[i] x = (fun y : ZMod n => 3 * y)^[j] x
  rw [H11_iter, H11_iter]
  exact h

theorem H11_pow_eq_iff (h3 : ¬ 3 ∣ n) (x : ZMod n) (i j : ℕ) :
    3 ^ i * x = 3 ^ j * x ↔ i % H11_per x = j % H11_per x := by
  constructor
  · intro h
    apply H11_inj (Nat.mod_lt _ (H11_per_pos h3 x)) (Nat.mod_lt _ (H11_per_pos h3 x))
    rw [H11_pow_mod, H11_pow_mod, h]
  · intro h
    rw [← H11_pow_mod x i, h, H11_pow_mod]

/-- Step 1 of the paper: for odd `k` (and `8 ∣ n`), `3^i k ≠ -k`. -/
theorem H11_no_neg (h8 : 8 ∣ n) {k : ZMod n} (hk : Odd k.val) (i : ℕ) : (3 : ZMod n) ^ i * k ≠ -k := by
  intro h
  have hz : (((3 ^ i + 1) * k.val : ℕ) : ZMod n) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val, add_mul, one_mul, h, neg_add_cancel]
  rw [ZMod.natCast_eq_zero_iff] at hz
  have h8' : 8 ∣ (3 ^ i + 1) * k.val := dvd_trans h8 hz
  have hcop : Nat.Coprime 8 k.val := by
    have : Nat.Coprime 2 k.val := Nat.coprime_two_left.mpr hk
    simpa using Nat.Coprime.pow_left 3 this
  have h8'' : 8 ∣ 3 ^ i + 1 := hcop.dvd_of_dvd_mul_right h8'
  have hmod := H11_three_pow_mod8 i
  omega

end Basic

/-! ## 2. Orbits and pairs `{O, O^{-1}}` -/

section Orbits

variable {n : ℕ} [NeZero n]

theorem H11_mem_orbit (j k : ZMod n) : j ∈ orbit 3 k ↔ ∃ i : ℕ, j = 3 ^ i * k := by
  simp [orbit]

theorem H11_mem_inv (j : ZMod n) (O : Finset (ZMod n)) : j ∈ inv O ↔ -j ∈ O := by
  simp only [inv, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [neg_neg]
  · intro h
    exact ⟨-j, h, neg_neg j⟩

theorem H11_inv_inv (O : Finset (ZMod n)) : inv (inv O) = O := by
  simp [inv, Finset.image_image]

theorem H11_inv_card (O : Finset (ZMod n)) : (inv O).card = O.card :=
  Finset.card_image_of_injective _ neg_injective

theorem H11_orbit_eq_of_mem (h3 : ¬ 3 ∣ n) {j k : ZMod n} (h : j ∈ orbit 3 k) : orbit 3 j = orbit 3 k := by
  rw [H11_mem_orbit] at h
  obtain ⟨i, rfl⟩ := h
  obtain ⟨w, hw⟩ := H11_inv_pow h3 i
  ext x
  simp only [H11_mem_orbit]
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨l + i, by ring⟩
  · rintro ⟨l, rfl⟩
    refine ⟨l + w, ?_⟩
    calc (3 : ZMod n) ^ l * k = 3 ^ l * (3 ^ w * 3 ^ i) * k := by rw [hw, mul_one]
      _ = 3 ^ (l + w) * (3 ^ i * k) := by ring

theorem H11_orbit_neg (k : ZMod n) : orbit 3 (-k) = inv (orbit 3 k) := by
  ext j
  rw [H11_mem_inv, H11_mem_orbit, H11_mem_orbit]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, by ring⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [← neg_neg j, hi]; ring⟩

theorem H11_orbit_eq_image (h3 : ¬ 3 ∣ n) (k : ZMod n) :
    orbit 3 k = (range (H11_per k)).image (fun i => (3 : ZMod n) ^ i * k) := by
  ext j
  rw [H11_mem_orbit, Finset.mem_image]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i % H11_per k, Finset.mem_range.mpr (Nat.mod_lt _ (H11_per_pos h3 k)), H11_pow_mod k i⟩
  · rintro ⟨i, -, rfl⟩
    exact ⟨i, rfl⟩

theorem H11_card_orbit (h3 : ¬ 3 ∣ n) (k : ZMod n) : (orbit 3 k).card = H11_per k := by
  rw [H11_orbit_eq_image h3, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  exact H11_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij

end Orbits

section Pairs

variable {n : ℕ} [NeZero n]

theorem H11_not_both (h8 : 8 ∣ n) (h3 : ¬ 3 ∣ n) {x ρ : ZMod n} (hx : Odd x.val) (h1 : x ∈ orbit 3 ρ)
    (h2 : -x ∈ orbit 3 ρ) : False := by
  rw [← H11_orbit_eq_of_mem h3 h1, H11_mem_orbit] at h2
  obtain ⟨i, hi⟩ := h2
  exact H11_no_neg h8 hx i hi.symm

theorem H11_disjoint (h8 : 8 ∣ n) (h3 : ¬ 3 ∣ n) {k : ZMod n} (hk : Odd k.val) :
    Disjoint (orbit 3 k) (inv (orbit 3 k)) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [H11_mem_inv] at hx'
  have hn2 : 2 ∣ n := dvd_trans (by norm_num) h8
  have hxodd : Odd x.val := by
    obtain ⟨i, rfl⟩ := (H11_mem_orbit _ _).mp hx
    exact H11_pow_odd hn2 i hk
  exact H11_not_both h8 h3 hxodd hx hx'

/-- The pair `{O, O^{-1}}` of the orbit of `k`. -/
noncomputable def H11_pairOf (k : ZMod n) : Finset (Finset (ZMod n)) := {orbit 3 k, inv (orbit 3 k)}

/-- The union `O ∪ O^{-1}` of a pair. -/
def H11_U (P : Finset (Finset (ZMod n))) : Finset (ZMod n) := P.biUnion id

theorem H11_U_pairOf (k : ZMod n) : H11_U (H11_pairOf k) = orbit 3 k ∪ inv (orbit 3 k) := by
  simp [H11_U, H11_pairOf, Finset.biUnion_insert]

theorem H11_mem_topPairs (P : Finset (Finset (ZMod n))) :
    P ∈ topPairs n 3 ↔ ∃ k : ZMod n, Odd k.val ∧ P = H11_pairOf k := by
  simp only [topPairs, topOrbits, topLayer, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    H11_pairOf]
  constructor
  · rintro ⟨O, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨orbit 3 k, ⟨k, hk, rfl⟩, rfl⟩

theorem H11_pairOf_neg (k : ZMod n) : H11_pairOf (-k) = H11_pairOf k := by
  simp only [H11_pairOf, H11_orbit_neg, H11_inv_inv]
  exact Finset.pair_comm _ _

theorem H11_pairOf_of_mem_orbit (h3 : ¬ 3 ∣ n) {j k : ZMod n} (h : j ∈ orbit 3 k) :
    H11_pairOf j = H11_pairOf k := by
  simp only [H11_pairOf, H11_orbit_eq_of_mem h3 h]

theorem H11_pairOf_eq (h3 : ¬ 3 ∣ n) {j k : ZMod n} (h : j ∈ H11_U (H11_pairOf k)) :
    H11_pairOf j = H11_pairOf k := by
  rw [H11_U_pairOf, Finset.mem_union] at h
  rcases h with h | h
  · exact H11_pairOf_of_mem_orbit h3 h
  · rw [H11_mem_inv] at h
    rw [← H11_pairOf_neg j]
    exact H11_pairOf_of_mem_orbit h3 h

theorem H11_pairOf_mul3 (h3 : ¬ 3 ∣ n) (k : ZMod n) : H11_pairOf (3 * k) = H11_pairOf k :=
  H11_pairOf_of_mem_orbit h3 ((H11_mem_orbit _ _).mpr ⟨1, by ring⟩)

theorem H11_mem_U_self (k : ZMod n) : k ∈ H11_U (H11_pairOf k) := by
  rw [H11_U_pairOf, Finset.mem_union, H11_mem_orbit]
  left
  exact ⟨0, by simp⟩

theorem H11_pairOf_mem (k : ZMod n) (hk : Odd k.val) : H11_pairOf k ∈ topPairs n 3 :=
  (H11_mem_topPairs _).mpr ⟨k, hk, rfl⟩

theorem H11_U_eq (h3 : ¬ 3 ∣ n) {P : Finset (Finset (ZMod n))} (hP : P ∈ topPairs n 3) {x : ZMod n}
    (hx : x ∈ H11_U P) : H11_pairOf x = P := by
  obtain ⟨k, hk, rfl⟩ := (H11_mem_topPairs P).mp hP
  exact H11_pairOf_eq h3 hx

theorem H11_odd_of_mem_U (hn2 : 2 ∣ n) {P : Finset (Finset (ZMod n))} (hP : P ∈ topPairs n 3) {x : ZMod n}
    (hx : x ∈ H11_U P) : Odd x.val := by
  obtain ⟨k, hk, rfl⟩ := (H11_mem_topPairs P).mp hP
  rw [H11_U_pairOf, Finset.mem_union, H11_mem_inv, H11_mem_orbit, H11_mem_orbit] at hx
  rcases hx with ⟨i, rfl⟩ | ⟨i, hi⟩
  · exact H11_pow_odd hn2 i hk
  · rw [← neg_neg x, hi]
    exact H11_odd_neg hn2 (H11_pow_odd hn2 i hk)

/-- Every `x` of a pair lies in the orbit of any `ρ` of the pair, or its negative does. -/
theorem H11_mem_class (h3 : ¬ 3 ∣ n) {P : Finset (Finset (ZMod n))} (hP : P ∈ topPairs n 3) {x ρ : ZMod n}
    (hx : x ∈ H11_U P) (hρ : ρ ∈ H11_U P) : x ∈ orbit 3 ρ ∨ -x ∈ orbit 3 ρ := by
  rw [← H11_U_eq h3 hP hρ, H11_U_pairOf, Finset.mem_union, H11_mem_inv] at hx
  exact hx

theorem H11_pairLen (h8 : 8 ∣ n) (h3 : ¬ 3 ∣ n) {k : ZMod n} (hk : Odd k.val) :
    pairLen (H11_pairOf k) = H11_per k := by
  have h := H11_U_pairOf k
  unfold H11_U at h
  unfold pairLen
  rw [h, Finset.card_union_of_disjoint (H11_disjoint h8 h3 hk), H11_inv_card, H11_card_orbit h3]
  omega

end Pairs

/-! ## 3. Propagation along an orbit; number of admissible values at a representative -/

section Propag

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

/-- Propagation of a value `t` at `ρ` along the orbit of `ρ` by `x ↦ A(3^i ρ) x^3`. -/
def H11_prop (A : ZMod n → L) (ρ : ZMod n) : ℕ → L → L
  | 0, t => t
  | i + 1, t => A (3 ^ i * ρ) * H11_prop A ρ i t ^ 3

theorem H11_prop_succ (A : ZMod n → L) (ρ : ZMod n) (i : ℕ) (t : L) :
    H11_prop A ρ (i + 1) t = A (3 ^ i * ρ) * H11_prop A ρ i t ^ 3 := rfl

theorem H11_prop_zero (A : ZMod n → L) (ρ : ZMod n) (t : L) : H11_prop A ρ 0 t = t := rfl

theorem H11_prop_add (A : ZMod n → L) (ρ : ZMod n) (t : L) (i j : ℕ) :
    H11_prop A ρ (i + j) t = H11_prop A (3 ^ i * ρ) j (H11_prop A ρ i t) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← add_assoc, H11_prop_succ, H11_prop_succ, ih,
      show (3 : ZMod n) ^ (i + j) * ρ = 3 ^ j * (3 ^ i * ρ) by ring]

theorem H11_prop_period (A : ZMod n → L) (ρ : ZMod n) (t : L) (M : ℕ) (hρ : 3 ^ M * ρ = ρ)
    (ht : H11_prop A ρ M t = t) (i : ℕ) : H11_prop A ρ i t = H11_prop A ρ (i % M) t := by
  have key : ∀ q r : ℕ, H11_prop A ρ (M * q + r) t = H11_prop A ρ r t := by
    intro q r
    induction q with
    | zero => simp
    | succ q ih =>
      rw [show M * (q + 1) + r = M + (M * q + r) by ring, H11_prop_add, hρ, ht, ih]
  conv_lhs => rw [← Nat.div_add_mod i M]
  exact key _ _

theorem H11_prop_ne (hn2 : 2 ∣ n) {A : ZMod n → L} (hA : ∀ k : ZMod n, Odd k.val → A k ≠ 0) {ρ : ZMod n}
    (hρ : Odd ρ.val) {t : L} (ht : t ≠ 0) (i : ℕ) : H11_prop A ρ i t ≠ 0 := by
  induction i with
  | zero => exact ht
  | succ i ih =>
    rw [H11_prop_succ]
    exact mul_ne_zero (hA _ (H11_pow_odd hn2 i hρ)) (pow_ne_zero _ ih)

theorem H11_prop_one (ρ : ZMod n) (t : L) (i : ℕ) : H11_prop (fun _ => (1 : L)) ρ i t = t ^ (3 ^ i) := by
  induction i with
  | zero => simp [H11_prop_zero]
  | succ i ih => rw [H11_prop_succ, ih, one_mul, ← pow_mul, ← pow_succ]

theorem H11_prop_form (hn2 : 2 ∣ n) {A : ZMod n → L} (hA : ∀ k : ZMod n, Odd k.val → A k ≠ 0) {ρ : ZMod n}
    (hρ : Odd ρ.val) (i : ℕ) : ∃ C : L, C ≠ 0 ∧ ∀ t, H11_prop A ρ i t = C * t ^ (3 ^ i) := by
  induction i with
  | zero => exact ⟨1, one_ne_zero, fun t => by simp [H11_prop_zero]⟩
  | succ i ih =>
    obtain ⟨C, hC, hf⟩ := ih
    refine ⟨A (3 ^ i * ρ) * C ^ 3, mul_ne_zero (hA _ (H11_pow_odd hn2 i hρ)) (pow_ne_zero _ hC), fun t => ?_⟩
    rw [H11_prop_succ, hf, show (3 : ℕ) ^ (i + 1) = 3 ^ i * 3 from pow_succ 3 i, pow_mul]
    ring

/-- `X^N = c` has exactly `N` roots when `N ≠ 0` in `L` and `c ≠ 0` (algebraically closed `L`). -/
theorem H11_card_roots [IsAlgClosed L] {N : ℕ} (hN : 0 < N) (hNL : (N : L) ≠ 0) {c : L} (hc : c ≠ 0) :
    Nat.card {t : L | t ^ N = c} = N := by
  have : NeZero (N : L) := ⟨hNL⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot L N
  classical
  have hset : {t : L | t ^ N = c} = ↑(Multiset.toFinset (Polynomial.nthRoots N c)) := by
    ext t
    simp [Polynomial.mem_nthRoots hN]
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    Multiset.toFinset_card_of_nodup (hζ.nthRoots_nodup hc), hζ.card_nthRoots,
    ite_eq_left (IsAlgClosed.exists_pow_nat_eq c hN)]

theorem H11_three_pow_sub_one_ne [CharP L 3] {M : ℕ} (hM : 0 < M) : ((3 ^ M - 1 : ℕ) : L) ≠ 0 := by
  rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num)), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  have h3 : (3 : L) = 0 := by
    have := CharP.cast_eq_zero L 3
    simpa using this
  rw [h3, zero_pow hM.ne', zero_sub]
  exact neg_ne_zero.mpr one_ne_zero

theorem H11_three_pow_sub_one_pos {M : ℕ} (hM : 0 < M) : 0 < 3 ^ M - 1 := by
  have : 3 ≤ 3 ^ M := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ M := Nat.pow_le_pow_right (by norm_num) hM
  omega

/-- The admissible values at a representative: `3^M - 1` of them. -/
theorem H11_card_rootsA [CharP L 3] [IsAlgClosed L] (hn2 : 2 ∣ n) {A : ZMod n → L}
    (hA : ∀ k : ZMod n, Odd k.val → A k ≠ 0) {ρ : ZMod n} (hρ : Odd ρ.val) {M : ℕ} (hM : 0 < M) :
    Nat.card {t : L | t ≠ 0 ∧ H11_prop A ρ M t = t} = 3 ^ M - 1 := by
  obtain ⟨C, hC, hf⟩ := H11_prop_form hn2 hA hρ M
  have hpos := H11_three_pow_sub_one_pos hM
  have hset : {t : L | t ≠ 0 ∧ H11_prop A ρ M t = t} = {t : L | t ^ (3 ^ M - 1) = C⁻¹} := by
    ext t
    simp only [Set.mem_ofPred_eq, hf]
    have hsplit : t ^ (3 ^ M) = t ^ (3 ^ M - 1) * t := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num))]
    constructor
    · rintro ⟨ht0, h⟩
      rw [hsplit] at h
      have h1 : C * t ^ (3 ^ M - 1) = 1 := by
        apply mul_right_cancel₀ ht0
        rw [one_mul, mul_assoc, h]
      exact eq_inv_of_mul_eq_one_right h1
    · intro h
      have ht0 : t ≠ 0 := by
        rintro rfl
        rw [zero_pow hpos.ne'] at h
        exact (inv_ne_zero hC) h.symm
      refine ⟨ht0, ?_⟩
      rw [hsplit, h, ← mul_assoc, mul_inv_cancel₀ hC, one_mul]
  rw [hset]
  exact H11_card_roots hpos (H11_three_pow_sub_one_ne hM) (inv_ne_zero hC)

end Propag

/-! ## 4. Generic top data: uniqueness, existence, count -/

section TopData

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

/-- Generic top data: `h(3k) = A(k) h(k)^3` and `h(k) h(-k) = B(k)` for odd `k`; `h = v` on even `k`. -/
def H11_D (A B : ZMod n → L) (v : L) : Set (ZMod n → L) :=
  {h | (∀ k : ZMod n, Odd k.val → h (3 * k) = A k * h k ^ 3 ∧ h k * h (-k) = B k) ∧
    ∀ k : ZMod n, Even k.val → h k = v}

theorem H11_data_prop (hn2 : 2 ∣ n) {A B : ZMod n → L} {v : L} {h : ZMod n → L} (hh : h ∈ H11_D A B v)
    {ρ : ZMod n} (hρ : Odd ρ.val) (i : ℕ) : h (3 ^ i * ρ) = H11_prop A ρ i (h ρ) := by
  induction i with
  | zero => simp [H11_prop_zero]
  | succ i ih =>
    rw [show (3 : ZMod n) ^ (i + 1) * ρ = 3 * (3 ^ i * ρ) by ring, (hh.1 _ (H11_pow_odd hn2 i hρ)).1, ih,
      H11_prop_succ]

theorem H11_data_ne {A B : ZMod n → L} (hB : ∀ k : ZMod n, Odd k.val → B k ≠ 0) {v : L} {h : ZMod n → L}
    (hh : h ∈ H11_D A B v) {k : ZMod n} (hk : Odd k.val) : h k ≠ 0 := by
  have := hB k hk
  rw [← (hh.1 k hk).2] at this
  exact left_ne_zero_of_mul this

theorem H11_unique (h8 : 8 ∣ n) (h3 : ¬ 3 ∣ n) {A B : ZMod n → L} {v : L}
    (hB : ∀ k : ZMod n, Odd k.val → B k ≠ 0) (rep : Finset (Finset (ZMod n)) → ZMod n)
    (hrep : ∀ P ∈ topPairs n 3, rep P ∈ H11_U P) {h h' : ZMod n → L} (hh : h ∈ H11_D A B v)
    (hh' : h' ∈ H11_D A B v) (heq : ∀ P ∈ topPairs n 3, h (rep P) = h' (rep P)) : h = h' := by
  have hn2 : 2 ∣ n := dvd_trans (by norm_num) h8
  have horb : ∀ k : ZMod n, Odd k.val → k ∈ orbit 3 (rep (H11_pairOf k)) → h k = h' k := by
    intro k hk hmem
    have hP := H11_pairOf_mem k hk
    have hρ : Odd (rep (H11_pairOf k)).val := H11_odd_of_mem_U hn2 hP (hrep _ hP)
    obtain ⟨i, hi⟩ := (H11_mem_orbit _ _).mp hmem
    rw [hi, H11_data_prop hn2 hh hρ, H11_data_prop hn2 hh' hρ, heq _ hP]
  funext k
  rcases Nat.even_or_odd k.val with hk | hk
  · rw [hh.2 k hk, hh'.2 k hk]
  · have hP := H11_pairOf_mem k hk
    rcases H11_mem_class h3 hP (H11_mem_U_self k) (hrep _ hP) with hm | hm
    · exact horb k hk hm
    · have hnk : Odd (-k).val := H11_odd_neg hn2 hk
      have e : h (-k) = h' (-k) := horb (-k) hnk (by rw [H11_pairOf_neg]; exact hm)
      have f1 := (hh.1 (-k) hnk).2
      have f2 := (hh'.1 (-k) hnk).2
      rw [neg_neg] at f1 f2
      have hne : h (-k) ≠ 0 := H11_data_ne hB hh hnk
      apply mul_left_cancel₀ hne
      rw [f1, e, f2]

theorem H11_eval_mem (h8 : 8 ∣ n) {A B : ZMod n → L} {v : L} (hB : ∀ k : ZMod n, Odd k.val → B k ≠ 0)
    {h : ZMod n → L} (hh : h ∈ H11_D A B v) {ρ : ZMod n} (hρ : Odd ρ.val) :
    h ρ ≠ 0 ∧ H11_prop A ρ (H11_per ρ) (h ρ) = h ρ := by
  have hn2 : 2 ∣ n := dvd_trans (by norm_num) h8
  refine ⟨H11_data_ne hB hh hρ, ?_⟩
  rw [← H11_data_prop hn2 hh hρ, H11_pow_per]

open Classical in
/-- The propagated value at `k` from the representative of its pair (0 if `k` is not in that orbit). -/
noncomputable def H11_g0 (A : ZMod n → L) (rep : Finset (Finset (ZMod n)) → ZMod n)
    (tt : Finset (Finset (ZMod n)) → L) (k : ZMod n) : L :=
  if hk : ∃ i : ℕ, k = 3 ^ i * rep (H11_pairOf k) then
    H11_prop A (rep (H11_pairOf k)) (Nat.find hk) (tt (H11_pairOf k)) else 0

open Classical in
/-- The top datum built from the values `tt P` at the representatives `rep P`. -/
noncomputable def H11_ext (A B : ZMod n → L) (v : L) (rep : Finset (Finset (ZMod n)) → ZMod n)
    (tt : Finset (Finset (ZMod n)) → L) (k : ZMod n) : L :=
  if Even k.val then v else
    if k ∈ orbit 3 (rep (H11_pairOf k)) then H11_g0 A rep tt k else B (-k) / H11_g0 A rep tt (-k)

theorem H11_g0_eq (h3 : ¬ 3 ∣ n) {A : ZMod n → L} {rep : Finset (Finset (ZMod n)) → ZMod n}
    {tt : Finset (Finset (ZMod n)) → L} {k : ZMod n} {i : ℕ} (hi : k = 3 ^ i * rep (H11_pairOf k))
    (ht : H11_prop A (rep (H11_pairOf k)) (H11_per (rep (H11_pairOf k))) (tt (H11_pairOf k)) =
      tt (H11_pairOf k)) :
    H11_g0 A rep tt k = H11_prop A (rep (H11_pairOf k)) i (tt (H11_pairOf k)) := by
  have hex : ∃ i : ℕ, k = 3 ^ i * rep (H11_pairOf k) := ⟨i, hi⟩
  rw [H11_g0, dite_eq_left hex,
    H11_prop_period A _ _ _ (H11_pow_per _) ht (Nat.find hex),
    H11_prop_period A _ _ _ (H11_pow_per _) ht i]
  congr 1
  exact (H11_pow_eq_iff h3 _ _ _).mp ((Nat.find_spec hex).symm.trans hi)

theorem H11_exist (h8 : 8 ∣ n) (h3 : ¬ 3 ∣ n) {A B : ZMod n → L} (v : L)
    (hA : ∀ k : ZMod n, Odd k.val → A k ≠ 0) (_hB : ∀ k : ZMod n, Odd k.val → B k ≠ 0)
    (hBneg : ∀ k : ZMod n, Odd k.val → B (-k) = B k)
    (hB3 : ∀ k : ZMod n, Odd k.val → B (3 * k) = A k * A (-k) * B k ^ 3)
    (rep : Finset (Finset (ZMod n)) → ZMod n) (hrep : ∀ P ∈ topPairs n 3, rep P ∈ H11_U P)
    (tt : Finset (Finset (ZMod n)) → L)
    (htt : ∀ P ∈ topPairs n 3, tt P ≠ 0 ∧ H11_prop A (rep P) (H11_per (rep P)) (tt P) = tt P) :
    H11_ext A B v rep tt ∈ H11_D A B v ∧ ∀ P ∈ topPairs n 3, H11_ext A B v rep tt (rep P) = tt P := by
  have hn2 : 2 ∣ n := dvd_trans (by norm_num) h8
  have vorb : ∀ P ∈ topPairs n 3, ∀ x : ZMod n, Odd x.val → H11_pairOf x = P → ∀ i : ℕ,
      x = 3 ^ i * rep P → H11_ext A B v rep tt x = H11_prop A (rep P) i (tt P) := by
    intro P hP x hx hxP i hi
    have hne : ¬ Even x.val := Nat.not_even_iff_odd.mpr hx
    have hmem : x ∈ orbit 3 (rep (H11_pairOf x)) := by
      rw [hxP, H11_mem_orbit]
      exact ⟨i, hi⟩
    have hi' : x = 3 ^ i * rep (H11_pairOf x) := by rw [hxP]; exact hi
    rw [H11_ext, ite_eq_right hne, ite_eq_left hmem, H11_g0_eq h3 hi' (by rw [hxP]; exact (htt P hP).2), hxP]
  have vinv : ∀ P ∈ topPairs n 3, ∀ x : ZMod n, Odd x.val → H11_pairOf x = P → ∀ i : ℕ,
      -x = 3 ^ i * rep P → H11_ext A B v rep tt x = B (-x) / H11_prop A (rep P) i (tt P) := by
    intro P hP x hx hxP i hi
    have hne : ¬ Even x.val := Nat.not_even_iff_odd.mpr hx
    have hnm : x ∉ orbit 3 (rep (H11_pairOf x)) := by
      rw [hxP]
      intro hmem
      exact H11_not_both h8 h3 hx hmem ((H11_mem_orbit _ _).mpr ⟨i, hi⟩)
    have hxP' : H11_pairOf (-x) = P := by rw [H11_pairOf_neg, hxP]
    have hi' : -x = 3 ^ i * rep (H11_pairOf (-x)) := by rw [hxP']; exact hi
    rw [H11_ext, ite_eq_right hne, ite_eq_right hnm, H11_g0_eq h3 hi' (by rw [hxP']; exact (htt P hP).2), hxP']
  have hD : H11_ext A B v rep tt ∈ H11_D A B v := by
    refine ⟨fun k hk => ?_, fun k hk => by rw [H11_ext, ite_eq_left hk]⟩
    have hP := H11_pairOf_mem k hk
    have h3k : Odd (3 * k).val := H11_odd_mul3 hn2 hk
    have hnk : Odd (-k).val := H11_odd_neg hn2 hk
    have eP3 : H11_pairOf (3 * k) = H11_pairOf k := H11_pairOf_mul3 h3 k
    have ePn : H11_pairOf (-k) = H11_pairOf k := H11_pairOf_neg k
    have hρ := hrep _ hP
    have hρodd : Odd (rep (H11_pairOf k)).val := H11_odd_of_mem_U hn2 hP hρ
    have ht0 := (htt _ hP).1
    rcases H11_mem_class h3 hP (H11_mem_U_self k) hρ with hm | hm
    · obtain ⟨i, hi⟩ := (H11_mem_orbit _ _).mp hm
      have hw := H11_prop_ne hn2 hA hρodd ht0 i
      have e1 := vorb _ hP k hk rfl i hi
      have e2 := vorb _ hP (3 * k) h3k eP3 (i + 1) (by rw [pow_succ', mul_assoc, ← hi])
      have e3 := vinv _ hP (-k) hnk ePn i (by rw [neg_neg]; exact hi)
      rw [neg_neg] at e3
      refine ⟨?_, ?_⟩
      · rw [e2, e1, H11_prop_succ, ← hi]
      · rw [e1, e3]
        field_simp
    · obtain ⟨i, hi⟩ := (H11_mem_orbit _ _).mp hm
      have hw := H11_prop_ne hn2 hA hρodd ht0 i
      have e1 := vinv _ hP k hk rfl i hi
      have e2 := vinv _ hP (3 * k) h3k eP3 (i + 1) (by rw [pow_succ', mul_assoc, ← hi]; ring)
      have e3 := vorb _ hP (-k) hnk ePn i hi
      refine ⟨?_, ?_⟩
      · rw [e2, e1, H11_prop_succ, ← hi, show -(3 * k) = 3 * -k by ring, hB3 (-k) hnk, neg_neg]
        have hAk := hA k hk
        have hAnk := hA (-k) hnk
        field_simp
      · rw [e1, e3, hBneg k hk]
        field_simp
  refine ⟨hD, fun P hP => ?_⟩
  have hx := hrep P hP
  have hxodd := H11_odd_of_mem_U hn2 hP hx
  exact (vorb P hP (rep P) hxodd (H11_U_eq h3 hP hx) 0 (by simp)).trans (H11_prop_zero _ _ _)

/-- A canonical representative of each pair. -/
noncomputable def H11_rep0 (P : Finset (Finset (ZMod n))) : ZMod n :=
  if h : (H11_U P).Nonempty then h.choose else 0

theorem H11_rep0_mem {P : Finset (Finset (ZMod n))} (hP : P ∈ topPairs n 3) : H11_rep0 P ∈ H11_U P := by
  obtain ⟨k, hk, rfl⟩ := (H11_mem_topPairs P).mp hP
  have hne : (H11_U (H11_pairOf k)).Nonempty := ⟨k, H11_mem_U_self k⟩
  rw [H11_rep0, dite_eq_left hne]
  exact hne.choose_spec

/-- The generic count: `|D(A,B,v)| = ∏_{pairs} (3^{L_i} - 1)`. -/
theorem H11_count (h8 : 8 ∣ n) (h3 : ¬ 3 ∣ n) [CharP L 3] [IsAlgClosed L] {A B : ZMod n → L} (v : L)
    (hA : ∀ k : ZMod n, Odd k.val → A k ≠ 0) (hB : ∀ k : ZMod n, Odd k.val → B k ≠ 0)
    (hBneg : ∀ k : ZMod n, Odd k.val → B (-k) = B k)
    (hB3 : ∀ k : ZMod n, Odd k.val → B (3 * k) = A k * A (-k) * B k ^ 3) :
    Nat.card (H11_D A B v) = pairProd n 3 := by
  classical
  have hn2 : 2 ∣ n := dvd_trans (by norm_num) h8
  let R : ↥(topPairs n 3) → Set L := fun P =>
    {t : L | t ≠ 0 ∧ H11_prop A (H11_rep0 P.1) (H11_per (H11_rep0 P.1)) t = t}
  have hrodd : ∀ P ∈ topPairs n 3, Odd (H11_rep0 P).val :=
    fun P hP => H11_odd_of_mem_U hn2 hP (H11_rep0_mem hP)
  let Φ : ↥(H11_D A B v) → ∀ P : ↥(topPairs n 3), ↥(R P) := fun h P =>
    ⟨h.1 (H11_rep0 P.1), H11_eval_mem h8 hB h.2 (hrodd P.1 P.2)⟩
  have hinj : Function.Injective Φ := by
    intro h1 h2 he
    apply Subtype.ext
    apply H11_unique h8 h3 hB H11_rep0 (fun P hP => H11_rep0_mem hP) h1.2 h2.2
    intro P hP
    exact congrArg (fun F => (F ⟨P, hP⟩).1) he
  have hsurj : Function.Surjective Φ := by
    intro φ
    let tt : Finset (Finset (ZMod n)) → L := fun Q => if hQ : Q ∈ topPairs n 3 then (φ ⟨Q, hQ⟩).1 else 0
    have htt : ∀ Q ∈ topPairs n 3,
        tt Q ≠ 0 ∧ H11_prop A (H11_rep0 Q) (H11_per (H11_rep0 Q)) (tt Q) = tt Q := by
      intro Q hQ
      have := (φ ⟨Q, hQ⟩).2
      simp only [tt, dite_eq_left hQ]
      exact this
    obtain ⟨hD, hval⟩ := H11_exist h8 h3 v hA hB hBneg hB3 H11_rep0 (fun P hP => H11_rep0_mem hP) tt htt
    refine ⟨⟨_, hD⟩, ?_⟩
    funext P
    apply Subtype.ext
    show H11_ext A B v H11_rep0 tt (H11_rep0 P.1) = (φ P).1
    rw [hval P.1 P.2]
    simp only [tt, dite_eq_left P.2]
  rw [Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩), Nat.card_pi, pairProd,
    ← Finset.prod_coe_sort (topPairs n 3)]
  refine Finset.prod_congr rfl (fun P _ => ?_)
  have hx := H11_rep0_mem P.2
  have hxodd := hrodd P.1 P.2
  rw [← H11_U_eq h3 P.2 hx, H11_pairLen h8 h3 hxodd]
  exact H11_card_rootsA hn2 hA hxodd (H11_per_pos h3 _)

end TopData

/-! ## 5. Step 2 -/

theorem H11_eight_dvd {n a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) : 8 ∣ n := by
  rw [hn]
  exact Dvd.dvd.mul_right (show 8 ∣ 2 ^ a from (show (8 : ℕ) = 2 ^ 3 by norm_num) ▸ pow_dvd_pow 2 ha) _

theorem H11_D0_eq {n : ℕ} [NeZero n] {L : Type*} [Field L] :
    (topData0 n 3 : Set (ZMod n → L)) = H11_D (fun _ => (1 : L)) (fun _ => 1) 1 := by
  ext h
  simp only [topData0, H11_D, Set.mem_ofPred_eq, Nat.cast_ofNat, one_mul]

theorem H11_T0_one {n : ℕ} [NeZero n] {L : Type*} [Field L] :
    (1 : ZMod n → L) ∈ (topData0 n 3 : Set (ZMod n → L)) := by
  rw [H11_D0_eq]
  exact ⟨fun k _ => by simp, fun k _ => rfl⟩

theorem H11_T0_mul {n : ℕ} [NeZero n] {L : Type*} [Field L] {l1 l2 : ZMod n → L}
    (hl1 : l1 ∈ (topData0 n 3 : Set (ZMod n → L))) (hl2 : l2 ∈ (topData0 n 3 : Set (ZMod n → L))) :
    l1 * l2 ∈ (topData0 n 3 : Set (ZMod n → L)) := by
  rw [H11_D0_eq] at hl1 hl2 ⊢
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun k hk => ?_⟩
  · simp only [Pi.mul_apply, (hl1.1 k hk).1, (hl2.1 k hk).1]
    ring
  · simp only [Pi.mul_apply]
    calc l1 k * l2 k * (l1 (-k) * l2 (-k)) = (l1 k * l1 (-k)) * (l2 k * l2 (-k)) := by ring
      _ = 1 := by rw [(hl1.1 k hk).2, (hl2.1 k hk).2, one_mul]
  · simp only [Pi.mul_apply, hl1.2 k hk, hl2.2 k hk, one_mul]

theorem H11_T0_inv {n : ℕ} [NeZero n] {L : Type*} [Field L] {l1 : ZMod n → L}
    (hl1 : l1 ∈ (topData0 n 3 : Set (ZMod n → L))) : l1⁻¹ ∈ (topData0 n 3 : Set (ZMod n → L)) := by
  rw [H11_D0_eq] at hl1 ⊢
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun k hk => ?_⟩
  · simp only [Pi.inv_apply, (hl1.1 k hk).1, one_mul, inv_pow]
  · simp only [Pi.inv_apply]
    rw [← mul_inv, (hl1.1 k hk).2, inv_one]
  · simp only [Pi.inv_apply, hl1.2 k hk, inv_one]

theorem H11_T0_pow {n : ℕ} [NeZero n] {L : Type*} [Field L] (hn2 : 2 ∣ n) {lam : ZMod n → L}
    (hl : lam ∈ (topData0 n 3 : Set (ZMod n → L))) {ρ : ZMod n} (hρ : Odd ρ.val) (i : ℕ) :
    lam (3 ^ i * ρ) = lam ρ ^ (3 ^ i) := by
  rw [H11_D0_eq] at hl
  rw [H11_data_prop hn2 hl hρ, H11_prop_one]

theorem H11_T0_neg {n : ℕ} [NeZero n] {L : Type*} [Field L] {lam : ZMod n → L}
    (hl : lam ∈ (topData0 n 3 : Set (ZMod n → L))) {ρ : ZMod n} (hρ : Odd ρ.val) : lam (-ρ) = (lam ρ)⁻¹ := by
  rw [H11_D0_eq] at hl
  exact eq_inv_of_mul_eq_one_right (hl.1 ρ hρ).2

/-- Row 14e — proof of Theorem 4.1, Step 2 (s4_normfree.tex:73-77). -/
theorem thm_4_1_step2_proved (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (_hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type*} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (hω : IsPrimitiveRoot ω n) :
    Nat.card (topData n 3 2 (1 : L) ω) = pairProd n 3 ∧ Nat.card (topData0 n 3 : Set (ZMod n → L)) = pairProd n 3 ∧
      (1 : ZMod n → L) ∈ (topData0 n 3 : Set (ZMod n → L)) ∧
      ∀ l1 ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ l2 ∈ (topData0 n 3 : Set (ZMod n → L)),
        l1 * l2 ∈ (topData0 n 3 : Set (ZMod n → L)) ∧ l1⁻¹ ∈ (topData0 n 3 : Set (ZMod n → L)) := by
  have h8 := H11_eight_dvd hn ha
  have hn2 : 2 ∣ n := dvd_trans (by norm_num) h8
  have hω0 : ω ≠ 0 := hω.ne_zero (NeZero.ne n)
  have hωn : ω ^ n = 1 := hω.pow_eq_one
  have eadd : ∀ x y : ZMod n, ω ^ (x + y).val = ω ^ x.val * ω ^ y.val := fun x y => by
    rw [ZMod.val_add, ← pow_eq_pow_mod _ hωn, pow_add]
  have einv : ∀ k : ZMod n, ω ^ (-k).val * ω ^ k.val = 1 := fun k => by
    rw [← eadd, neg_add_cancel, ZMod.val_zero, pow_zero]
  have e3 : ∀ k : ZMod n, ω ^ (3 * k).val = (ω ^ k.val) ^ 3 := fun k => by
    rw [show (3 : ZMod n) * k = k + k + k by ring, eadd, eadd]
    ring
  have en : ∀ k : ZMod n, (ω ^ k.val) ^ n = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, hωn, one_pow]
  have hA6 : ∀ k : ZMod n, (ω ^ k.val) ^ (((3 : ℕ) : ℤ) * 2) = (ω ^ k.val) ^ 6 := fun k => by
    rw [show ((3 : ℕ) : ℤ) * 2 = ((6 : ℕ) : ℤ) by norm_num, zpow_natCast]
  have hm : n = 2 * (n / 2) := by omega
  have eT : topData n 3 2 (1 : L) ω =
      H11_D (fun k => (ω ^ k.val) ^ (((3 : ℕ) : ℤ) * 2)) (fun k => 1 * (ω ^ k.val) ^ (n / 2)) 0 := by
    ext h
    simp only [topData, H11_D, Set.mem_ofPred_eq, Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eT]
    apply H11_count h8 h3 0
    · intro k _
      rw [hA6]
      exact pow_ne_zero _ (pow_ne_zero _ hω0)
    · intro k _
      exact mul_ne_zero one_ne_zero (pow_ne_zero _ (pow_ne_zero _ hω0))
    · intro k _
      simp only [one_mul]
      calc (ω ^ (-k).val) ^ (n / 2) = (ω ^ (-k).val) ^ (n / 2) * ((ω ^ k.val) ^ (n / 2)) ^ 2 := by
            rw [← pow_mul (ω ^ k.val) (n / 2) 2, mul_comm (n / 2) 2, ← hm, en, mul_one]
        _ = (ω ^ (-k).val * ω ^ k.val) ^ (n / 2) * (ω ^ k.val) ^ (n / 2) := by ring
        _ = (ω ^ k.val) ^ (n / 2) := by rw [einv, one_pow, one_mul]
    · intro k _
      simp only [hA6, one_mul, e3]
      have h6 : (ω ^ k.val) ^ 6 * (ω ^ (-k).val) ^ 6 = 1 := by rw [← mul_pow, mul_comm, einv, one_pow]
      rw [h6, one_mul]
      ring
  · rw [H11_D0_eq]
    apply H11_count h8 h3 1 <;> intros <;> simp
  · exact H11_T0_one
  · exact fun l1 hl1 l2 hl2 => ⟨H11_T0_mul hl1 hl2, H11_T0_inv hl1⟩

/-! ## 6. Layer 0: fibres of `ρ ↦ -ρ^{2^{a-1}}`, the group `G`, Step 6 -/

section Layer0

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

/-- `kk ρ := 2^{a-1} ρ + m` (exponent model); `ρ` lies in the fibre over `k` iff `kk ρ = k`. -/
def H11_kk (a : ℕ) (ρ : ZMod n) : ZMod n := (2 : ZMod n) ^ (a - 1) * ρ + half n

/-- The fibre of `Pmap` over `k`. -/
def H11_fib (a : ℕ) (k : ZMod n) : Finset (ZMod n) :=
  (topLayer n).filter (fun ρ => (2 ^ (a - 1) : ZMod n) * ρ = k + half n)

theorem H11_half_add (hn2 : 2 ∣ n) : half n + half n = (0 : ZMod n) := by
  unfold half
  rw [← Nat.cast_add]
  have : n / 2 + n / 2 = n := by omega
  rw [this, ZMod.natCast_self]

theorem H11_mem_fib (hn2 : 2 ∣ n) (a : ℕ) (k ρ : ZMod n) :
    ρ ∈ H11_fib a k ↔ Odd ρ.val ∧ H11_kk a ρ = k := by
  have hm := H11_half_add (n := n) hn2
  simp only [H11_fib, topLayer, Finset.mem_filter, Finset.mem_univ, true_and, H11_kk]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linear_combination h2 + hm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linear_combination h2 - hm⟩

theorem H11_kk_mul3 (hn2 : 2 ∣ n) (a : ℕ) (ρ : ZMod n) : H11_kk a (3 * ρ) = 3 * H11_kk a ρ := by
  have hm := H11_half_add (n := n) hn2
  unfold H11_kk
  linear_combination (-1 : ZMod n) * hm

theorem H11_kk_pow (hn2 : 2 ∣ n) (a i : ℕ) (ρ : ZMod n) : H11_kk a (3 ^ i * ρ) = 3 ^ i * H11_kk a ρ := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [show (3 : ZMod n) ^ (i + 1) * ρ = 3 * (3 ^ i * ρ) by ring, H11_kk_mul3 hn2, ih]
    ring

theorem H11_kk_neg (hn2 : 2 ∣ n) (a : ℕ) (ρ : ZMod n) : H11_kk a (-ρ) = -H11_kk a ρ := by
  have hm := H11_half_add (n := n) hn2
  unfold H11_kk
  linear_combination hm

theorem H11_dvd_val_iff {a : ℕ} (h2a : 2 ^ a ∣ n) (x : ZMod n) :
    2 ^ a ∣ x.val ↔ ZMod.castHom h2a (ZMod (2 ^ a)) x = 0 := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]

theorem H11_layer0_mul3 {a : ℕ} (h3 : ¬ 3 ∣ n) (h2a : 2 ^ a ∣ n) {k : ZMod n} (hk : k ∈ layer0' n a) :
    3 * k ∈ layer0' n a := by
  simp only [layer0', Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  refine ⟨?_, ?_⟩
  · rw [H11_dvd_val_iff h2a] at hk ⊢
    rw [map_mul, hk.1, mul_zero]
  · intro h0
    apply hk.2
    exact H11_cancel h3 (i := 1) (by rw [pow_one, h0, mul_zero])

theorem H11_layer0_pow {a : ℕ} (h3 : ¬ 3 ∣ n) (h2a : 2 ^ a ∣ n) (i : ℕ) {k : ZMod n} (hk : k ∈ layer0' n a) :
    3 ^ i * k ∈ layer0' n a := by
  induction i with
  | zero => simpa using hk
  | succ i ih =>
    rw [show (3 : ZMod n) ^ (i + 1) * k = 3 * (3 ^ i * k) by ring]
    exact H11_layer0_mul3 h3 h2a ih

theorem H11_layer0_neg {a : ℕ} (h2a : 2 ^ a ∣ n) {k : ZMod n} (hk : k ∈ layer0' n a) : -k ∈ layer0' n a := by
  simp only [layer0', Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  refine ⟨?_, neg_ne_zero.mpr hk.2⟩
  rw [H11_dvd_val_iff h2a] at hk ⊢
  rw [map_neg, hk.1, neg_zero]

theorem H11_layer0_ne_neg {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (hodd : Odd nodd) {k : ZMod n}
    (hk : k ∈ layer0' n a) : k ≠ -k := by
  simp only [layer0', Finset.mem_filter, Finset.mem_univ, true_and] at hk
  obtain ⟨⟨c, hc⟩, hk0⟩ := hk
  intro hkk
  apply hk0
  have h2k : ((2 * k.val : ℕ) : ZMod n) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    linear_combination hkk
  rw [ZMod.natCast_eq_zero_iff, hc, hn] at h2k
  have h1 : nodd ∣ 2 * c := by
    have h2a0 : 0 < 2 ^ a := by positivity
    rw [show 2 * (2 ^ a * c) = 2 ^ a * (2 * c) by ring] at h2k
    exact (Nat.mul_dvd_mul_iff_left h2a0).mp h2k
  have h2 : nodd ∣ c := (Nat.coprime_two_right.mpr hodd).dvd_of_dvd_mul_left h1
  have h3' : n ∣ k.val := by
    rw [hc, hn]
    exact Nat.mul_dvd_mul_left _ h2
  exact (ZMod.val_eq_zero k).mp (Nat.eq_zero_of_dvd_of_lt h3' (ZMod.val_lt k))

theorem H11_exists_rho {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) {k0 : ZMod n}
    (hk0 : k0 ∈ layer0' n a) : ∃ ρ0 : ZMod n, Odd ρ0.val ∧ H11_kk a ρ0 = k0 := by
  have h8 := H11_eight_dvd hn ha
  have hn2 : 2 ∣ n := dvd_trans (by norm_num) h8
  simp only [layer0', Finset.mem_filter, Finset.mem_univ, true_and] at hk0
  obtain ⟨⟨c, hc⟩, -⟩ := hk0
  refine ⟨((nodd + 2 * c : ℕ) : ZMod n), ?_, ?_⟩
  · rw [H11_odd_iff hn2, map_natCast, ZMod.natCast_eq_one_iff_odd]
    exact hodd.add_even (even_two_mul c)
  · have hP : 2 ^ a = 2 * 2 ^ (a - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hn' : n = 2 * 2 ^ (a - 1) * nodd := by rw [hn, hP]
    have hhalf : n / 2 = 2 ^ (a - 1) * nodd := by
      rw [hn', mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
    have hsum : 2 ^ (a - 1) * (nodd + 2 * c) + n / 2 = n + 2 ^ a * c := by
      rw [hhalf, hP, hn']
      ring
    have hcast : ((2 ^ (a - 1) * (nodd + 2 * c) + n / 2 : ℕ) : ZMod n) = ((2 ^ a * c : ℕ) : ZMod n) := by
      rw [hsum, Nat.cast_add, ZMod.natCast_self, zero_add]
    unfold H11_kk half
    rw [← ZMod.natCast_zmod_val k0, hc, ← hcast]
    push_cast
    ring

/-! ### The group `G` and the map `Π` -/

theorem H11_G_pow {a : ℕ} (h3 : ¬ 3 ∣ n) (h2a : 2 ^ a ∣ n) {g : ZMod n → L} (hg : g ∈ Ggrp n a 3) {k : ZMod n}
    (hk : k ∈ layer0' n a) (i : ℕ) : g (3 ^ i * k) = g k ^ (3 ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h := (hg.1 _ (H11_layer0_pow h3 h2a i hk)).1
    simp only [Nat.cast_ofNat] at h
    rw [show (3 : ZMod n) ^ (i + 1) * k = 3 * (3 ^ i * k) by ring, h, ih, ← pow_mul, ← pow_succ]

theorem H11_G_neg {a : ℕ} {g : ZMod n → L} (hg : g ∈ Ggrp n a 3) {k : ZMod n} (hk : k ∈ layer0' n a) :
    g (-k) = (g k)⁻¹ :=
  eq_inv_of_mul_eq_one_left (hg.1 k hk).2

theorem H11_G_ne {a : ℕ} {g : ZMod n → L} (hg : g ∈ Ggrp n a 3) (k : ZMod n) : g k ≠ 0 := by
  by_cases hk : k ∈ layer0' n a
  · exact right_ne_zero_of_mul_eq_one (hg.1 k hk).2
  · rw [hg.2 k hk]
    exact one_ne_zero

theorem H11_G_mul {a : ℕ} {g1 g2 : ZMod n → L} (hg1 : g1 ∈ Ggrp n a 3) (hg2 : g2 ∈ Ggrp n a 3) :
    g1 * g2 ∈ Ggrp n a 3 := by
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun k hk => ?_⟩
  · simp only [Pi.mul_apply, (hg1.1 k hk).1, (hg2.1 k hk).1, mul_pow]
  · simp only [Pi.mul_apply]
    calc g1 (-k) * g2 (-k) * (g1 k * g2 k) = (g1 (-k) * g1 k) * (g2 (-k) * g2 k) := by ring
      _ = 1 := by rw [(hg1.1 k hk).2, (hg2.1 k hk).2, one_mul]
  · simp only [Pi.mul_apply, hg1.2 k hk, hg2.2 k hk, one_mul]

theorem H11_G_inv {a : ℕ} {g : ZMod n → L} (hg : g ∈ Ggrp n a 3) : g⁻¹ ∈ Ggrp n a 3 := by
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun k hk => ?_⟩
  · simp only [Pi.inv_apply, (hg.1 k hk).1, inv_pow]
  · simp only [Pi.inv_apply]
    rw [← mul_inv, (hg.1 k hk).2, inv_one]
  · simp only [Pi.inv_apply, hg.2 k hk, inv_one]

theorem H11_Pmap_eq (a : ℕ) (lam : ZMod n → L) (k : ZMod n) :
    Pmap n a lam k = if k ∈ layer0' n a then ∏ ρ ∈ H11_fib a k, lam ρ else 1 := rfl

theorem H11_Pmap_one (a : ℕ) : Pmap n a (1 : ZMod n → L) = 1 := by
  funext k
  rw [H11_Pmap_eq]
  split_ifs <;> simp

theorem H11_Pmap_mul (a : ℕ) (l1 l2 : ZMod n → L) : Pmap n a (l1 * l2) = Pmap n a l1 * Pmap n a l2 := by
  funext k
  simp only [H11_Pmap_eq, Pi.mul_apply]
  split_ifs
  · exact Finset.prod_mul_distrib
  · simp

/-- Step 6, first claim: `P_λ ∈ G` for `λ ∈ 𝒟^0`. -/
theorem H11_Pmap_mem {a : ℕ} (h8 : 8 ∣ n) (h3 : ¬ 3 ∣ n) (h2a : 2 ^ a ∣ n) {lam : ZMod n → L}
    (hl : lam ∈ (topData0 n 3 : Set (ZMod n → L))) : Pmap n a lam ∈ Ggrp n a 3 := by
  have hn2 : 2 ∣ n := dvd_trans (by norm_num) h8
  obtain ⟨w, hw⟩ := H11_inv_pow h3 1
  rw [pow_one] at hw
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun k hk => ?_⟩
  · simp only [Nat.cast_ofNat]
    rw [H11_Pmap_eq, ite_eq_left (H11_layer0_mul3 h3 h2a hk), H11_Pmap_eq, ite_eq_left hk, ← Finset.prod_pow]
    symm
    apply Finset.prod_nbij' (fun ρ => 3 * ρ) (fun ρ => 3 ^ w * ρ)
    · intro ρ hρ
      rw [H11_mem_fib hn2] at hρ ⊢
      exact ⟨H11_odd_mul3 hn2 hρ.1, by rw [H11_kk_mul3 hn2, hρ.2]⟩
    · intro ρ hρ
      rw [H11_mem_fib hn2] at hρ ⊢
      refine ⟨H11_pow_odd hn2 w hρ.1, ?_⟩
      rw [H11_kk_pow hn2, hρ.2, ← mul_assoc, hw, one_mul]
    · intro ρ _
      rw [← mul_assoc, hw, one_mul]
    · intro ρ _
      rw [← mul_assoc, show (3 : ZMod n) * 3 ^ w = 1 by rw [mul_comm]; exact hw, one_mul]
    · intro ρ hρ
      rw [H11_mem_fib hn2] at hρ
      have := H11_T0_pow hn2 hl hρ.1 1
      rw [pow_one, pow_one] at this
      exact this.symm
  · rw [H11_Pmap_eq, ite_eq_left (H11_layer0_neg h2a hk), H11_Pmap_eq, ite_eq_left hk]
    have e : ∏ ρ ∈ H11_fib a (-k), lam ρ = ∏ ρ ∈ H11_fib a k, lam (-ρ) := by
      symm
      apply Finset.prod_nbij' (fun ρ => -ρ) (fun ρ => -ρ)
      · intro ρ hρ
        rw [H11_mem_fib hn2] at hρ ⊢
        exact ⟨H11_odd_neg hn2 hρ.1, by rw [H11_kk_neg hn2, hρ.2]⟩
      · intro ρ hρ
        rw [H11_mem_fib hn2] at hρ ⊢
        refine ⟨H11_odd_neg hn2 hρ.1, ?_⟩
        rw [H11_kk_neg hn2, hρ.2, neg_neg]
      · intro ρ _
        exact neg_neg ρ
      · intro ρ _
        exact neg_neg ρ
      · intro ρ _
        rfl
    rw [e, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro ρ hρ
    rw [H11_mem_fib hn2] at hρ
    rw [H11_T0_neg hl hρ.1, inv_mul_cancel₀]
    rw [H11_D0_eq] at hl
    exact H11_data_ne (fun _ _ => one_ne_zero) hl hρ.1
  · rw [H11_Pmap_eq, ite_eq_right hk]

end Layer0

/-! ## 7. Step 6, surjectivity: one top pair at a time -/

section Surj

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

/-- A homogeneous top datum equal to `t^{3^i}` on the orbit of `ρ0`, to `t^{-3^i}` on its inverse, and `1` elsewhere. -/
theorem H11_lam_of_t (h8 : 8 ∣ n) (h3 : ¬ 3 ∣ n) {ρ0 : ZMod n} (hρ0 : Odd ρ0.val) {t : L}
    (ht : t ^ (3 ^ H11_per ρ0 - 1) = 1) :
    ∃ lam ∈ (topData0 n 3 : Set (ZMod n → L)), (∀ i : ℕ, lam (3 ^ i * ρ0) = t ^ (3 ^ i)) ∧
      (∀ i : ℕ, lam (-(3 ^ i * ρ0)) = (t ^ (3 ^ i))⁻¹) ∧
      ∀ ρ : ZMod n, (∀ i : ℕ, ρ ≠ 3 ^ i * ρ0 ∧ ρ ≠ -(3 ^ i * ρ0)) → lam ρ = 1 := by
  classical
  have hn2 : 2 ∣ n := dvd_trans (by norm_num) h8
  have hP0mem : H11_pairOf ρ0 ∈ topPairs n 3 := H11_pairOf_mem ρ0 hρ0
  let rep : Finset (Finset (ZMod n)) → ZMod n := fun P => if P = H11_pairOf ρ0 then ρ0 else H11_rep0 P
  let tt : Finset (Finset (ZMod n)) → L := fun P => if P = H11_pairOf ρ0 then t else 1
  have hrep : ∀ P ∈ topPairs n 3, rep P ∈ H11_U P := by
    intro P hP
    by_cases h : P = H11_pairOf ρ0
    · have e : rep P = ρ0 := ite_eq_left h
      rw [e, h]
      exact H11_mem_U_self ρ0
    · have e : rep P = H11_rep0 P := ite_eq_right h
      rw [e]
      exact H11_rep0_mem hP
  have hpos := H11_three_pow_sub_one_pos (H11_per_pos h3 ρ0)
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_pow hpos.ne'] at ht
    exact zero_ne_one ht
  have htt : ∀ P ∈ topPairs n 3,
      tt P ≠ 0 ∧ H11_prop (fun _ => (1 : L)) (rep P) (H11_per (rep P)) (tt P) = tt P := by
    intro P _
    by_cases h : P = H11_pairOf ρ0
    · have e1 : tt P = t := ite_eq_left h
      have e2 : rep P = ρ0 := ite_eq_left h
      rw [e1, e2, H11_prop_one]
      refine ⟨ht0, ?_⟩
      rw [← Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num) : 1 ≤ 3 ^ H11_per ρ0), pow_succ, ht, one_mul]
    · have e1 : tt P = 1 := ite_eq_right h
      rw [e1, H11_prop_one, one_pow]
      exact ⟨one_ne_zero, rfl⟩
  obtain ⟨hD, hval⟩ := H11_exist h8 h3 (A := fun _ => (1 : L)) (B := fun _ => (1 : L)) 1
    (fun _ _ => one_ne_zero) (fun _ _ => one_ne_zero) (fun _ _ => rfl) (fun _ _ => by simp) rep hrep tt htt
  have hl : H11_ext (fun _ => (1 : L)) (fun _ => 1) 1 rep tt ∈ (topData0 n 3 : Set (ZMod n → L)) := by
    rw [H11_D0_eq]
    exact hD
  have hlam0 : H11_ext (fun _ => (1 : L)) (fun _ => 1) 1 rep tt ρ0 = t := by
    have := hval _ hP0mem
    have e2 : rep (H11_pairOf ρ0) = ρ0 := ite_eq_left rfl
    have e1 : tt (H11_pairOf ρ0) = t := ite_eq_left rfl
    rw [e2, e1] at this
    exact this
  refine ⟨_, hl, fun i => ?_, fun i => ?_, ?_⟩
  · rw [H11_T0_pow hn2 hl hρ0, hlam0]
  · rw [H11_T0_neg hl (H11_pow_odd hn2 i hρ0), H11_T0_pow hn2 hl hρ0, hlam0]
  · intro ρ hρ
    rcases Nat.even_or_odd ρ.val with he | ho
    · exact hD.2 ρ he
    · have hP := H11_pairOf_mem ρ ho
      have hne : H11_pairOf ρ ≠ H11_pairOf ρ0 := by
        intro heq
        have hmem := H11_mem_U_self ρ
        rw [heq, H11_U_pairOf, Finset.mem_union, H11_mem_inv, H11_mem_orbit, H11_mem_orbit] at hmem
        rcases hmem with ⟨i, hi⟩ | ⟨i, hi⟩
        · exact (hρ i).1 hi
        · exact (hρ i).2 (by rw [← hi, neg_neg])
      have e2 : rep (H11_pairOf ρ) = H11_rep0 (H11_pairOf ρ) := ite_eq_right hne
      have e1 : tt (H11_pairOf ρ) = 1 := ite_eq_right hne
      have hx := H11_rep0_mem hP
      have hxodd := H11_odd_of_mem_U hn2 hP hx
      have hlx : H11_ext (fun _ => (1 : L)) (fun _ => 1) 1 rep tt (H11_rep0 (H11_pairOf ρ)) = 1 := by
        have := hval _ hP
        rw [e2, e1] at this
        exact this
      rcases H11_mem_class h3 hP (H11_mem_U_self ρ) hx with hm | hm
      · obtain ⟨i, hi⟩ := (H11_mem_orbit _ _).mp hm
        rw [hi, H11_T0_pow hn2 hl hxodd, hlx, one_pow]
      · obtain ⟨i, hi⟩ := (H11_mem_orbit _ _).mp hm
        have := H11_T0_neg hl (H11_odd_neg hn2 ho)
        rw [neg_neg, hi, H11_T0_pow hn2 hl hxodd, hlx, one_pow, inv_one] at this
        exact this

theorem H11_geom {M ℓ : ℕ} (hℓM : ℓ ∣ M) :
    (∑ j ∈ range (M / ℓ), 3 ^ (j * ℓ)) * (3 ^ ℓ - 1) = 3 ^ M - 1 := by
  have h1 : 1 ≤ 3 ^ ℓ := Nat.one_le_pow _ _ (by norm_num)
  have key := geom_sum_mul_add (3 ^ ℓ - 1) (M / ℓ)
  rw [Nat.sub_add_cancel h1, ← pow_mul, Nat.mul_div_cancel' hℓM] at key
  have e : ∑ j ∈ range (M / ℓ), 3 ^ (j * ℓ) = ∑ i ∈ range (M / ℓ), (3 ^ ℓ) ^ i := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← pow_mul, mul_comm]
  rw [e, ← key, Nat.add_sub_cancel]

theorem H11_mul_lt {j ℓ M : ℕ} (hℓ : 0 < ℓ) (hℓM : ℓ ∣ M) (hj : j < M / ℓ) : j * ℓ < M := by
  have h1 : (j + 1) * ℓ ≤ M / ℓ * ℓ := Nat.mul_le_mul_right ℓ hj
  rw [Nat.div_mul_cancel hℓM, add_mul, one_mul] at h1
  exact lt_of_lt_of_le (Nat.lt_add_of_pos_right hℓ) h1

/-- The fibre over `k0` splits into the part in the orbit `O` of `ρ0` and the part in `O^{-1}` (λ = 1 elsewhere). -/
theorem H11_split {a : ℕ} (h8 : 8 ∣ n) (h3 : ¬ 3 ∣ n) {ρ0 k0 : ZMod n} (hk0 : k0 ∈ layer0' n a)
    {lam : ZMod n → L} (hl3 : ∀ ρ : ZMod n, (∀ i : ℕ, ρ ≠ 3 ^ i * ρ0 ∧ ρ ≠ -(3 ^ i * ρ0)) → lam ρ = 1) :
    Pmap n a lam k0 = (∏ ρ ∈ (H11_fib a k0).filter (fun ρ => ρ ∈ orbit 3 ρ0), lam ρ) *
      ∏ ρ ∈ (H11_fib a k0).filter (fun ρ => -ρ ∈ orbit 3 ρ0), lam ρ := by
  have hn2 : 2 ∣ n := dvd_trans (by norm_num) h8
  rw [H11_Pmap_eq, ite_eq_left hk0,
    ← Finset.prod_filter_mul_prod_filter_not (H11_fib a k0) (fun ρ => ρ ∈ orbit 3 ρ0)]
  congr 1
  symm
  apply Finset.prod_subset
  · intro ρ hρ
    rw [Finset.mem_filter] at hρ ⊢
    refine ⟨hρ.1, fun hO => H11_not_both h8 h3 ((H11_mem_fib hn2 a k0 ρ).mp hρ.1).1 hO hρ.2⟩
  · intro ρ hρ hnot
    rw [Finset.mem_filter] at hρ hnot
    apply hl3
    intro i
    constructor
    · intro h
      exact hρ.2 (by rw [h, H11_mem_orbit]; exact ⟨i, rfl⟩)
    · intro h
      exact hnot ⟨hρ.1, by rw [h, neg_neg, H11_mem_orbit]; exact ⟨i, rfl⟩⟩

/-- The orbit part of the fibre over `k0 = kk ρ0` contributes `t^E`, `E = ∑_{j < M/ℓ} 3^{jℓ}`. -/
theorem H11_S1 {a : ℕ} (h8 : 8 ∣ n) (h3 : ¬ 3 ∣ n) {ρ0 k0 : ZMod n} (hρ0 : Odd ρ0.val) (hkk : H11_kk a ρ0 = k0)
    (hℓM : H11_per k0 ∣ H11_per ρ0) {t : L} {lam : ZMod n → L}
    (hl1 : ∀ i : ℕ, lam (3 ^ i * ρ0) = t ^ (3 ^ i)) :
    ∏ ρ ∈ (H11_fib a k0).filter (fun ρ => ρ ∈ orbit 3 ρ0), lam ρ =
      t ^ (∑ j ∈ range (H11_per ρ0 / H11_per k0), 3 ^ (j * H11_per k0)) := by
  have hn2 : 2 ∣ n := dvd_trans (by norm_num) h8
  have hℓ := H11_per_pos h3 k0
  have hM := H11_per_pos h3 ρ0
  rw [← Finset.prod_pow_eq_pow_sum]
  symm
  apply Finset.prod_nbij (fun j => 3 ^ (j * H11_per k0) * ρ0)
  · intro j _
    rw [Finset.mem_filter, H11_mem_fib hn2]
    refine ⟨⟨H11_pow_odd hn2 _ hρ0, ?_⟩, (H11_mem_orbit _ _).mpr ⟨_, rfl⟩⟩
    rw [H11_kk_pow hn2, hkk, ← H11_pow_mod k0 (j * H11_per k0), Nat.mul_mod_left, pow_zero, one_mul]
  · intro j1 hj1 j2 hj2 he
    have h1 := H11_mul_lt hℓ hℓM (Finset.mem_range.mp (Finset.mem_coe.mp hj1))
    have h2 := H11_mul_lt hℓ hℓM (Finset.mem_range.mp (Finset.mem_coe.mp hj2))
    exact Nat.eq_of_mul_eq_mul_right hℓ (H11_inj h1 h2 he)
  · intro ρ hρ
    rw [Finset.mem_coe, Finset.mem_filter, H11_mem_fib hn2] at hρ
    obtain ⟨⟨_, hkρ⟩, hO⟩ := hρ
    obtain ⟨i, rfl⟩ := (H11_mem_orbit _ _).mp hO
    have hik : 3 ^ i * k0 = k0 := by rw [← hkk, ← H11_kk_pow hn2, hkρ, hkk]
    have hℓi : H11_per k0 ∣ i % H11_per ρ0 := (Nat.dvd_mod_iff hℓM).mpr (H11_per_dvd hik)
    refine ⟨i % H11_per ρ0 / H11_per k0, Finset.mem_coe.mpr (Finset.mem_range.mpr ?_), ?_⟩
    · apply Nat.lt_of_mul_lt_mul_right (a := H11_per k0)
      rw [Nat.div_mul_cancel hℓi, Nat.div_mul_cancel hℓM]
      exact Nat.mod_lt _ hM
    · show 3 ^ (i % H11_per ρ0 / H11_per k0 * H11_per k0) * ρ0 = 3 ^ i * ρ0
      rw [Nat.div_mul_cancel hℓi, H11_pow_mod]
  · intro j _
    exact (hl1 _).symm

/-- Case (i): no `i` with `3^i k0 = -k0`; then the inverse part is empty. -/
theorem H11_S2_i {a : ℕ} (hn2 : 2 ∣ n) {ρ0 k0 : ZMod n} (hkk : H11_kk a ρ0 = k0)
    (hcase : ∀ i : ℕ, 3 ^ i * k0 ≠ -k0) (lam : ZMod n → L) :
    ∏ ρ ∈ (H11_fib a k0).filter (fun ρ => -ρ ∈ orbit 3 ρ0), lam ρ = 1 := by
  apply Finset.prod_eq_one
  intro ρ hρ
  exfalso
  rw [Finset.mem_filter, H11_mem_fib hn2] at hρ
  obtain ⟨⟨_, hkρ⟩, hO⟩ := hρ
  obtain ⟨i, hi⟩ := (H11_mem_orbit _ _).mp hO
  apply hcase i
  rw [← hkk, ← H11_kk_pow hn2, ← hi, H11_kk_neg hn2, hkρ, hkk]

/-- Case (ii): `3^h k0 = -k0`; then `ρ ↦ -(3^h ρ)` carries the orbit part onto the inverse part. -/
theorem H11_S2_ii {a : ℕ} (h8 : 8 ∣ n) (h3 : ¬ 3 ∣ n) {ρ0 k0 : ZMod n} (_hkk : H11_kk a ρ0 = k0) {h : ℕ}
    (hh : 3 ^ h * k0 = -k0) {lam : ZMod n → L} (hl : lam ∈ (topData0 n 3 : Set (ZMod n → L))) :
    ∏ ρ ∈ (H11_fib a k0).filter (fun ρ => -ρ ∈ orbit 3 ρ0), lam ρ =
      ((∏ ρ ∈ (H11_fib a k0).filter (fun ρ => ρ ∈ orbit 3 ρ0), lam ρ) ^ (3 ^ h))⁻¹ := by
  have hn2 : 2 ∣ n := dvd_trans (by norm_num) h8
  obtain ⟨w, hw⟩ := H11_inv_pow h3 h
  rw [← Finset.prod_pow, ← Finset.prod_inv_distrib]
  symm
  apply Finset.prod_nbij' (fun ρ => -(3 ^ h * ρ)) (fun x => 3 ^ w * (-x))
  · intro ρ hρ
    rw [Finset.mem_filter, H11_mem_fib hn2] at hρ ⊢
    obtain ⟨⟨hoddρ, hkρ⟩, hO⟩ := hρ
    refine ⟨⟨H11_odd_neg hn2 (H11_pow_odd hn2 h hoddρ), ?_⟩, ?_⟩
    · rw [H11_kk_neg hn2, H11_kk_pow hn2, hkρ, hh, neg_neg]
    · rw [neg_neg]
      obtain ⟨i, rfl⟩ := (H11_mem_orbit _ _).mp hO
      exact (H11_mem_orbit _ _).mpr ⟨h + i, by ring⟩
  · intro x hx
    rw [Finset.mem_filter, H11_mem_fib hn2] at hx ⊢
    obtain ⟨⟨hoddx, hkx⟩, hO⟩ := hx
    refine ⟨⟨H11_pow_odd hn2 w (H11_odd_neg hn2 hoddx), ?_⟩, ?_⟩
    · rw [H11_kk_pow hn2, H11_kk_neg hn2, hkx, ← hh, ← mul_assoc, hw, one_mul]
    · obtain ⟨i, hi⟩ := (H11_mem_orbit _ _).mp hO
      rw [hi]
      exact (H11_mem_orbit _ _).mpr ⟨w + i, by ring⟩
  · intro ρ _
    simp only [neg_neg]
    rw [← mul_assoc, hw, one_mul]
  · intro x _
    rw [← mul_assoc, show (3 : ZMod n) ^ h * 3 ^ w = 1 by rw [mul_comm]; exact hw, one_mul, neg_neg]
  · intro ρ hρ
    rw [Finset.mem_filter, H11_mem_fib hn2] at hρ
    rw [H11_T0_neg hl (H11_pow_odd hn2 h hρ.1.1), H11_T0_pow hn2 hl hρ.1.1]

/-- Off the `⟨3,-1⟩`-orbit of `k0`, `P_λ = 1`. -/
theorem H11_support {a : ℕ} (hn2 : 2 ∣ n) {ρ0 k0 : ZMod n} (hkk : H11_kk a ρ0 = k0) {lam : ZMod n → L}
    (hl3 : ∀ ρ : ZMod n, (∀ i : ℕ, ρ ≠ 3 ^ i * ρ0 ∧ ρ ≠ -(3 ^ i * ρ0)) → lam ρ = 1) :
    ∀ k : ZMod n, (∀ i : ℕ, k ≠ 3 ^ i * k0 ∧ k ≠ -(3 ^ i * k0)) → Pmap n a lam k = 1 := by
  intro k hk
  rw [H11_Pmap_eq]
  split_ifs
  · apply Finset.prod_eq_one
    intro ρ hρ
    rw [H11_mem_fib hn2] at hρ
    apply hl3
    intro i
    constructor
    · intro he
      apply (hk i).1
      rw [← hρ.2, he, H11_kk_pow hn2, hkk]
    · intro he
      apply (hk i).2
      rw [← hρ.2, he, H11_kk_neg hn2, H11_kk_pow hn2, hkk]
  · rfl

theorem H11_sq_sub_one (X : ℕ) (hX : 1 ≤ X) : X * X - 1 = (X - 1) * (X + 1) := by
  obtain ⟨Y, rfl⟩ : ∃ Y, X = Y + 1 := ⟨X - 1, by omega⟩
  rw [Nat.add_sub_cancel, show (Y + 1) * (Y + 1) = Y * (Y + 1 + 1) + 1 by ring, Nat.add_sub_cancel]

/-- If the orbit of `k0 ∈ μ_{n_odd} ∖ {1}` is self-inverse, it is so at exactly half its length. -/
theorem H11_half_period {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n) {k0 : ZMod n}
    (hk0 : k0 ∈ layer0' n a) {h0 : ℕ} (hh0 : 3 ^ h0 * k0 = -k0) :
    ∃ h : ℕ, 3 ^ h * k0 = -k0 ∧ 0 < h ∧ 2 * h = H11_per k0 := by
  have hℓ := H11_per_pos h3 k0
  refine ⟨h0 % H11_per k0, by rw [H11_pow_mod, hh0], ?_⟩
  generalize hhdef : h0 % H11_per k0 = h
  have hh : 3 ^ h * k0 = -k0 := by rw [← hhdef, H11_pow_mod, hh0]
  have hlt : h < H11_per k0 := by rw [← hhdef]; exact Nat.mod_lt _ hℓ
  have hpos : 0 < h := by
    rcases Nat.eq_zero_or_pos h with h' | h'
    · rw [h', pow_zero, one_mul] at hh
      exact absurd hh (H11_layer0_ne_neg hn hodd hk0)
    · exact h'
  refine ⟨hpos, ?_⟩
  have hdvd : H11_per k0 ∣ 2 * h :=
    H11_per_dvd (by rw [two_mul, pow_add, mul_assoc, hh, mul_neg, hh, neg_neg])
  obtain ⟨c, hc⟩ := hdvd
  rcases c with _ | _ | c
  · rw [mul_zero] at hc
    omega
  · rw [zero_add, mul_one] at hc
    exact hc
  · have h1 : H11_per k0 * 2 ≤ H11_per k0 * (c + 1 + 1) := Nat.mul_le_mul_left _ (by omega)
    rw [← hc] at h1
    omega

/-- The elementary surjectivity: some `λ ∈ 𝒟^0` has `P_λ(k0) = γ` (any admissible `γ`) and `P_λ = 1` off the
`⟨3,-1⟩`-orbit of `k0`. -/
theorem H11_elem {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    [CharP L 3] [IsAlgClosed L] {k0 : ZMod n} (hk0 : k0 ∈ layer0' n a) {γ : L} (hγ0 : γ ≠ 0)
    (hγ1 : ∀ i : ℕ, 3 ^ i * k0 = k0 → γ ^ (3 ^ i) = γ)
    (hγ2 : ∀ i : ℕ, 3 ^ i * k0 = -k0 → γ ^ (3 ^ i) * γ = 1) :
    ∃ lam ∈ (topData0 n 3 : Set (ZMod n → L)), Pmap n a lam k0 = γ ∧
      ∀ k : ZMod n, (∀ i : ℕ, k ≠ 3 ^ i * k0 ∧ k ≠ -(3 ^ i * k0)) → Pmap n a lam k = 1 := by
  have h8 := H11_eight_dvd hn ha
  have hn2 : 2 ∣ n := dvd_trans (by norm_num) h8
  obtain ⟨ρ0, hρ0, hkk⟩ := H11_exists_rho hn ha hodd hk0
  have hMpos := H11_per_pos h3 ρ0
  have hℓM : H11_per k0 ∣ H11_per ρ0 :=
    H11_per_dvd (by rw [← hkk, ← H11_kk_pow hn2, H11_pow_per])
  have hE := H11_geom hℓM
  have hEpos : 0 < ∑ j ∈ range (H11_per ρ0 / H11_per k0), 3 ^ (j * H11_per k0) := by
    rcases Nat.eq_zero_or_pos (∑ j ∈ range (H11_per ρ0 / H11_per k0), 3 ^ (j * H11_per k0)) with h0 | h0
    · rw [h0, zero_mul] at hE
      have := H11_three_pow_sub_one_pos hMpos
      omega
    · exact h0
  by_cases hcase : ∃ i : ℕ, 3 ^ i * k0 = -k0
  · -- case (ii): the orbit of `k0` is self-inverse
    obtain ⟨h0, hh0⟩ := hcase
    obtain ⟨h, hh, hhpos, h2h⟩ := H11_half_period hn hodd h3 hk0 hh0
    have hγh := hγ2 h hh
    have hpos' := H11_three_pow_sub_one_pos hhpos
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq γ⁻¹ hpos'
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [zero_pow hpos'.ne'] at hs
      exact inv_ne_zero hγ0 hs.symm
    have hs1 : s ^ (3 ^ H11_per k0 - 1) = 1 := by
      have e : 3 ^ H11_per k0 - 1 = (3 ^ h - 1) * (3 ^ h + 1) := by
        rw [← h2h, two_mul, pow_add, H11_sq_sub_one _ (Nat.one_le_pow _ _ (by norm_num))]
      rw [e, pow_mul, hs, inv_pow, pow_succ, hγh, inv_one]
    obtain ⟨t, htE⟩ := IsAlgClosed.exists_pow_nat_eq s hEpos
    have ht : t ^ (3 ^ H11_per ρ0 - 1) = 1 := by rw [← hE, pow_mul, htE, hs1]
    obtain ⟨lam, hl, hl1, -, hl3⟩ := H11_lam_of_t h8 h3 hρ0 ht
    refine ⟨lam, hl, ?_, H11_support hn2 hkk hl3⟩
    rw [H11_split h8 h3 hk0 hl3, H11_S2_ii h8 h3 hkk hh hl, H11_S1 h8 h3 hρ0 hkk hℓM hl1, htE]
    have e : s ^ (3 ^ h) = γ⁻¹ * s := by
      rw [← hs, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num))]
    rw [e, mul_inv, inv_inv]
    field_simp
  · -- case (i): the orbit of `k0` is not self-inverse
    push Not at hcase
    have hγℓ : γ ^ (3 ^ H11_per k0 - 1) = 1 := by
      have h1 := hγ1 _ (H11_pow_per k0)
      have h2 : γ ^ (3 ^ H11_per k0 - 1) * γ = 1 * γ := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num)), h1, one_mul]
      exact mul_right_cancel₀ hγ0 h2
    obtain ⟨t, htE⟩ := IsAlgClosed.exists_pow_nat_eq γ hEpos
    have ht : t ^ (3 ^ H11_per ρ0 - 1) = 1 := by rw [← hE, pow_mul, htE, hγℓ]
    obtain ⟨lam, hl, hl1, -, hl3⟩ := H11_lam_of_t h8 h3 hρ0 ht
    refine ⟨lam, hl, ?_, H11_support hn2 hkk hl3⟩
    rw [H11_split h8 h3 hk0 hl3, H11_S2_i hn2 hkk hcase, H11_S1 h8 h3 hρ0 hkk hℓM hl1, htE, mul_one]

open Classical in
/-- Surjectivity of `Π` by induction on the support of `g`. -/
theorem H11_surj {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    [CharP L 3] [IsAlgClosed L] :
    ∀ N : ℕ, ∀ g : ZMod n → L, g ∈ Ggrp n a 3 → (univ.filter (fun k => g k ≠ 1)).card ≤ N →
      ∃ lam ∈ (topData0 n 3 : Set (ZMod n → L)), Pmap n a lam = g := by
  have h8 := H11_eight_dvd hn ha
  have h2a : 2 ^ a ∣ n := ⟨nodd, hn⟩
  intro N
  induction N with
  | zero =>
    intro g _ hcard
    refine ⟨1, H11_T0_one, ?_⟩
    rw [H11_Pmap_one]
    funext k
    by_contra hne
    have hk : k ∈ univ.filter (fun k => g k ≠ 1) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, fun h => hne h.symm⟩
    rw [Nat.le_zero, Finset.card_eq_zero] at hcard
    rw [hcard] at hk
    exact Finset.notMem_empty _ hk
  | succ N ih =>
    intro g hg hcard
    by_cases hall : ∀ k, g k = 1
    · exact ⟨1, H11_T0_one, by rw [H11_Pmap_one]; funext k; exact (hall k).symm⟩
    push Not at hall
    obtain ⟨k0, hk0⟩ := hall
    have hk0l : k0 ∈ layer0' n a := by
      by_contra h
      exact hk0 (hg.2 k0 h)
    obtain ⟨lB, hlB, hval, hsupp⟩ := H11_elem hn ha hodd h3 hk0l (H11_G_ne hg k0)
      (fun i hi => by rw [← H11_G_pow h3 h2a hg hk0l, hi])
      (fun i hi => by rw [← H11_G_pow h3 h2a hg hk0l, hi, H11_G_neg hg hk0l, inv_mul_cancel₀ (H11_G_ne hg k0)])
    have hpG : Pmap n a lB ∈ Ggrp n a 3 := H11_Pmap_mem h8 h3 h2a hlB
    have hg'G : g * (Pmap n a lB)⁻¹ ∈ Ggrp n a 3 := H11_G_mul hg (H11_G_inv hpG)
    have hg'k0 : (g * (Pmap n a lB)⁻¹) k0 = 1 := by
      rw [Pi.mul_apply, Pi.inv_apply, hval]
      exact mul_inv_cancel₀ (H11_G_ne hg k0)
    have hsub : univ.filter (fun k => (g * (Pmap n a lB)⁻¹) k ≠ 1) ⊂ univ.filter (fun k => g k ≠ 1) := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨k0, ?_, ?_⟩
        · rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hk0⟩
        · rw [Finset.mem_filter]
          exact fun h => h.2 hg'k0
      · intro k hk
        rw [Finset.mem_filter] at hk ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        by_cases horb : ∃ i : ℕ, k = 3 ^ i * k0 ∨ k = -(3 ^ i * k0)
        · exfalso
          obtain ⟨i, hi | hi⟩ := horb
          · apply hk.2
            rw [hi, H11_G_pow h3 h2a hg'G hk0l, hg'k0, one_pow]
          · apply hk.2
            rw [hi, H11_G_neg hg'G (H11_layer0_pow h3 h2a i hk0l), H11_G_pow h3 h2a hg'G hk0l, hg'k0,
              one_pow, inv_one]
        · push Not at horb
          have hp1 : Pmap n a lB k = 1 := hsupp k horb
          intro hgk
          apply hk.2
          rw [Pi.mul_apply, Pi.inv_apply, hp1, hgk, inv_one, mul_one]
    have hcard' := lt_of_lt_of_le (Finset.card_lt_card hsub) hcard
    obtain ⟨l', hl', hP'⟩ := ih _ hg'G (Nat.lt_succ_iff.mp hcard')
    refine ⟨l' * lB, H11_T0_mul hl' hlB, ?_⟩
    rw [H11_Pmap_mul, hP']
    funext k
    rw [Pi.mul_apply, Pi.mul_apply, Pi.inv_apply, mul_assoc, inv_mul_cancel₀ (H11_G_ne hpG k), mul_one]

end Surj

/-- Row 14h — proof of Theorem 4.1, Step 6 (s4_normfree.tex:116-132): `Π : 𝒟^0 → G`, `λ ↦ P_λ`, is a homomorphism onto `G`. -/
theorem thm_4_1_step6_proved (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type*} [Field L] [CharP L 3] [IsAlgClosed L] :
    (∀ lam ∈ (topData0 n 3 : Set (ZMod n → L)), Pmap n a lam ∈ (Ggrp n a 3 : Set (ZMod n → L))) ∧
    (∀ l1 ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ l2 ∈ (topData0 n 3 : Set (ZMod n → L)),
      Pmap n a (l1 * l2) = Pmap n a l1 * Pmap n a l2) ∧
    Set.SurjOn (Pmap n a) (topData0 n 3 : Set (ZMod n → L)) (Ggrp n a 3) := by
  have h8 := H11_eight_dvd hn ha
  have h2a : 2 ^ a ∣ n := ⟨nodd, hn⟩
  refine ⟨fun lam hl => H11_Pmap_mem h8 h3 h2a hl, fun l1 _ l2 _ => H11_Pmap_mul a l1 l2, ?_⟩
  intro g hg
  obtain ⟨lam, hl, he⟩ := H11_surj hn ha hodd h3 _ g hg le_rfl
  exact ⟨lam, hl, he⟩

#print axioms thm_4_1_step2_proved
#print axioms thm_4_1_step6_proved

end Xia.Proofs
