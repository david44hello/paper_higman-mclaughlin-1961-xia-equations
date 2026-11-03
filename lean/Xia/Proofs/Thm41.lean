/- Xia/Proofs/Thm41.lean — proofs of the rows thm_4_1_count, cor_4_2, thm_A, prop_4_3_even of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry
import Xia.Defs.Layer0
import Xia.Proofs.Thm31
import Xia.Proofs.Signs
import Xia.Proofs.Combinatorics
import Xia.Proofs.Sec22
import Xia.Proofs.FourierR

namespace Xia.Proofs

open Xia Finset

set_option linter.unusedSectionVars false

/-! ## 1. Arithmetic of `ZMod n`, `n = 2^a n_odd`: exact powers of two dividing `x.val` -/

section Arith

variable {n : ℕ} [NeZero n]

theorem H16_dvd_val_add {d : ℕ} (hd : d ∣ n) (x y : ZMod n) : d ∣ (x + y).val ↔ d ∣ x.val + y.val := by
  rw [ZMod.val_add]; exact Nat.dvd_mod_iff hd

theorem H16_dvd_val_mul {d : ℕ} (hd : d ∣ n) (x y : ZMod n) : d ∣ (x * y).val ↔ d ∣ x.val * y.val := by
  rw [ZMod.val_mul]; exact Nat.dvd_mod_iff hd

theorem H16_dvd_val_neg {d : ℕ} (hd : d ∣ n) (x : ZMod n) : d ∣ (-x).val ↔ d ∣ x.val := by
  have h0 : d ∣ x.val + (-x).val := by
    rw [← H16_dvd_val_add hd, add_neg_cancel, ZMod.val_zero]; exact dvd_zero d
  exact ⟨fun h => (Nat.dvd_add_iff_left h).mpr h0, fun h => (Nat.dvd_add_right h).mp h0⟩

theorem H16_val_two (h : 2 < n) : (2 : ZMod n).val = 2 := by
  rw [show (2 : ZMod n) = ((2 : ℕ) : ZMod n) by norm_num, ZMod.val_natCast, Nat.mod_eq_of_lt h]

theorem H16_val_three (h : 3 < n) : (3 : ZMod n).val = 3 := by
  rw [show (3 : ZMod n) = ((3 : ℕ) : ZMod n) by norm_num, ZMod.val_natCast, Nat.mod_eq_of_lt h]

/-- `2^m` divides `x.val` exactly. -/
def H16_ex (m : ℕ) (x : ZMod n) : Prop := 2 ^ m ∣ x.val ∧ ¬ 2 ^ (m + 1) ∣ x.val

variable {a nodd : ℕ}

theorem H16_pow_dvd (hn : n = 2 ^ a * nodd) {j : ℕ} (hj : j ≤ a) : 2 ^ j ∣ n := by
  rw [hn]; exact Dvd.dvd.mul_right (pow_dvd_pow 2 hj) _

theorem H16_half_eq (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) : n / 2 = 2 ^ (a - 1) * nodd := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  rw [hn, Nat.add_sub_cancel, pow_succ, mul_comm (2 ^ b) 2, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]

theorem H16_pow_dvd_half (hn : n = 2 ^ a * nodd) {j : ℕ} (hj : j + 1 ≤ a) : 2 ^ j ∣ n / 2 := by
  rw [H16_half_eq hn (by omega)]; exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _

theorem H16_n_ge (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) : 8 ≤ n := by
  have h8 : 2 ^ 3 ∣ n := H16_pow_dvd hn ha
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) h8

theorem H16_even (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) : Even n :=
  even_iff_two_dvd.mpr (dvd_trans (by norm_num : (2 : ℕ) ∣ 2 ^ 3) (H16_pow_dvd hn ha))

theorem H16_four_dvd (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) : 4 ∣ n :=
  (show (4 : ℕ) = 2 ^ 2 by norm_num) ▸ H16_pow_dvd hn (by omega)

theorem H16_dvd_three {j : ℕ} (hd : 2 ^ j ∣ n) (h3n : 3 < n) (x : ZMod n) :
    2 ^ j ∣ (3 * x).val ↔ 2 ^ j ∣ x.val := by
  rw [H16_dvd_val_mul hd, H16_val_three h3n]
  exact Nat.Coprime.dvd_mul_left (Nat.Coprime.pow_left j (by norm_num))

theorem H16_dvd_two_mul {j : ℕ} (hd : 2 ^ (j + 1) ∣ n) (h2n : 2 < n) (x : ZMod n) :
    2 ^ (j + 1) ∣ (2 * x).val ↔ 2 ^ j ∣ x.val := by
  rw [H16_dvd_val_mul hd, H16_val_two h2n, pow_succ', Nat.mul_dvd_mul_iff_left (by norm_num)]

theorem H16_dvd_add_half (hn : n = 2 ^ a * nodd) {j : ℕ} (hj : j + 1 ≤ a) (x : ZMod n) :
    2 ^ j ∣ (x + half n).val ↔ 2 ^ j ∣ x.val := by
  rw [H16_dvd_val_add (H16_pow_dvd hn (by omega)), H4_half_val n]
  exact (Nat.dvd_add_iff_left (H16_pow_dvd_half hn hj)).symm

theorem H16_ex_three (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) {m : ℕ} (hm : m + 1 ≤ a) (x : ZMod n) :
    H16_ex m (3 * x) ↔ H16_ex m x := by
  have h3n : 3 < n := by have := H16_n_ge hn ha; omega
  unfold H16_ex
  rw [H16_dvd_three (H16_pow_dvd hn (by omega)) h3n, H16_dvd_three (H16_pow_dvd hn hm) h3n]

theorem H16_ex_neg (hn : n = 2 ^ a * nodd) {m : ℕ} (hm : m + 1 ≤ a) (x : ZMod n) :
    H16_ex m (-x) ↔ H16_ex m x := by
  unfold H16_ex
  rw [H16_dvd_val_neg (H16_pow_dvd hn (by omega)), H16_dvd_val_neg (H16_pow_dvd hn hm)]

theorem H16_ex_two (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) {m : ℕ} (hm : m + 2 ≤ a) (x : ZMod n) :
    H16_ex (m + 1) (2 * x) ↔ H16_ex m x := by
  have h2n : 2 < n := by have := H16_n_ge hn ha; omega
  unfold H16_ex
  rw [H16_dvd_two_mul (H16_pow_dvd hn (by omega)) h2n, H16_dvd_two_mul (H16_pow_dvd hn (by omega)) h2n]

theorem H16_ex_add_half (hn : n = 2 ^ a * nodd) {m : ℕ} (hm : m + 2 ≤ a) (x : ZMod n) :
    H16_ex m (x + half n) ↔ H16_ex m x := by
  unfold H16_ex
  rw [H16_dvd_add_half hn (by omega), H16_dvd_add_half hn (by omega)]

theorem H16_pow_split (ha : 1 ≤ a) : (2 : ℕ) ^ a = 2 ^ (a - 1) * 2 := by
  rw [← pow_succ, Nat.sub_add_cancel ha]

/-- Layer `1` plus `n/2` lands in layer `0`. -/
theorem H16_top_add_half (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) (hodd : Odd nodd) (x : ZMod n)
    (hx : H16_ex (a - 1) x) : 2 ^ a ∣ (x + half n).val := by
  rw [H16_dvd_val_add (H16_pow_dvd hn le_rfl), H4_half_val n, H16_half_eq hn ha]
  obtain ⟨w, hw⟩ := hx.1
  have hw2 : ¬ 2 ∣ w := by
    intro h2; apply hx.2; rw [hw, Nat.sub_add_cancel ha, H16_pow_split ha]; exact Nat.mul_dvd_mul_left _ h2
  have hwo : Odd w := Nat.odd_iff.mpr (by omega)
  rw [hw, ← mul_add, H16_pow_split ha]
  exact Nat.mul_dvd_mul_left _ (Odd.add_odd hwo hodd).two_dvd

/-- Layer `0` plus `n/2` lands in layer `1`. -/
theorem H16_bot_add_half (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) (hodd : Odd nodd) (x : ZMod n)
    (hx : 2 ^ a ∣ x.val) : H16_ex (a - 1) (x + half n) := by
  unfold H16_ex
  rw [Nat.sub_add_cancel ha, H16_dvd_val_add (H16_pow_dvd hn (by omega)), H16_dvd_val_add (H16_pow_dvd hn le_rfl),
    H4_half_val n, H16_half_eq hn ha]
  obtain ⟨u, hu⟩ := hx
  rw [hu, H16_pow_split ha]
  refine ⟨⟨2 * u + nodd, by ring⟩, ?_⟩
  rw [show 2 ^ (a - 1) * 2 * u + 2 ^ (a - 1) * nodd = 2 ^ (a - 1) * (2 * u + nodd) by ring,
    Nat.mul_dvd_mul_iff_left (by positivity)]
  intro h; obtain ⟨c, hc⟩ := hodd; omega

theorem H16_bot_two_mul (hn : n = 2 ^ a * nodd) (_ha : 3 ≤ a) (x : ZMod n) (hx : 2 ^ a ∣ x.val) :
    2 ^ a ∣ (2 * x).val := by
  rw [H16_dvd_val_mul (H16_pow_dvd hn le_rfl)]; exact Dvd.dvd.mul_left hx _

theorem H16_top_two_mul (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (x : ZMod n) (hx : H16_ex (a - 1) x) :
    2 ^ a ∣ (2 * x).val := by
  have h2n : 2 < n := by have := H16_n_ge hn ha; omega
  have := H16_dvd_two_mul (j := a - 1) (by rw [Nat.sub_add_cancel (by omega)]; exact H16_pow_dvd hn le_rfl) h2n x
  rw [Nat.sub_add_cancel (by omega)] at this
  exact this.mpr hx.1

theorem H16_classify (x : ZMod n) : 2 ^ a ∣ x.val ∨ ∃ m, m < a ∧ H16_ex m x := by
  by_cases h : 2 ^ a ∣ x.val
  · exact Or.inl h
  · right
    have hx0 : x.val ≠ 0 := by intro h0; rw [h0] at h; exact h (dvd_zero _)
    refine ⟨padicValNat 2 x.val, ?_, pow_padicValNat_dvd, pow_succ_padicValNat_not_dvd hx0⟩
    by_contra hge; push Not at hge
    exact h ((pow_dvd_pow 2 hge).trans pow_padicValNat_dvd)

theorem H16_ex_padic {m : ℕ} (x : ZMod n) (hx : H16_ex m x) : padicValNat 2 x.val = m := by
  have hx0 : x.val ≠ 0 := by intro h0; exact hx.2 (by rw [h0]; exact dvd_zero _)
  have h1 := (padicValNat_dvd_iff_le hx0).mp hx.1
  have h2 : ¬ (m + 1 ≤ padicValNat 2 x.val) := fun h => hx.2 ((padicValNat_dvd_iff_le hx0).mpr h)
  omega

theorem H16_ex_zero_iff (x : ZMod n) : H16_ex 0 x ↔ Odd x.val := by
  unfold H16_ex
  rw [pow_zero, zero_add, pow_one, Nat.odd_iff]
  constructor
  · rintro ⟨-, h⟩; omega
  · intro h; exact ⟨one_dvd _, by omega⟩

theorem H16_two_mul_eq_iff (hev : Even n) (h3n : 3 ≤ n) (y x : ZMod n) :
    2 * y = 2 * x ↔ y = x ∨ y = x + half n := by
  constructor
  · intro h
    have h0 : 2 * (y - x) = 0 := by rw [mul_sub, h, sub_self]
    rcases H4_two_mul_eq_zero hev h3n _ h0 with h1 | h1
    · left; exact sub_eq_zero.mp h1
    · right; rw [← h1]; ring
  · rintro (rfl | rfl)
    · rfl
    · rw [mul_add, H4_two_mul_half hev, add_zero]

theorem H16_three_unit (h3 : ¬ 3 ∣ n) : IsUnit (3 : ZMod n) := by
  have hc : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have := (ZMod.isUnit_iff_coprime 3 n).mpr hc
  simpa using this

theorem H16_three_mul_ne (h3 : ¬ 3 ∣ n) {x : ZMod n} (hx : x ≠ 0) : 3 * x ≠ 0 := by
  intro h; exact hx ((H16_three_unit h3).mul_right_eq_zero.mp h)

theorem H16_three_half (hev : Even n) : 3 * half n = half n := by
  rw [show (3 : ZMod n) * half n = 2 * half n + half n by ring, H4_two_mul_half hev, zero_add]

theorem H16_mem_layer0 {x : ZMod n} : x ∈ layer0' n a ↔ 2 ^ a ∣ x.val ∧ x ≠ 0 := by
  simp [layer0']

end Arith

/-! ## 2. The descent products `D_m(k) = ∏_{ρ ∈ 𝓛_a, 2^m ρ = k} λ(ρ)` (eq:descent with `S = 1`) -/

section Build

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

/-- `D_m(k) := ∏_{ρ ∈ 𝓛_a, ρ^{2^m} = ξ} λ(ρ)` (exponent model). -/
noncomputable def H16_D (lam : ZMod n → L) (m : ℕ) (k : ZMod n) : L :=
  ∏ ρ ∈ (topLayer n).filter (fun ρ => (2 ^ m : ZMod n) * ρ = k), lam ρ

theorem H16_D_split (hev : Even n) (h3n : 3 ≤ n) (lam : ZMod n → L) (m : ℕ) (x : ZMod n) :
    H16_D lam (m + 1) (2 * x) = H16_D lam m x * H16_D lam m (x + half n) := by
  unfold H16_D
  have hdisj : Disjoint ((topLayer n).filter (fun ρ => (2 ^ m : ZMod n) * ρ = x))
      ((topLayer n).filter (fun ρ => (2 ^ m : ZMod n) * ρ = x + half n)) := by
    rw [Finset.disjoint_filter]
    intro ρ _ h1 h2
    exact H4_half_ne_zero (n := n) (by omega) (by linear_combination h1 - h2)
  rw [← Finset.prod_union hdisj, ← Finset.filter_or]
  refine Finset.prod_congr (Finset.filter_congr (fun ρ _ => ?_)) (fun _ _ => rfl)
  rw [pow_succ', mul_assoc]
  exact H16_two_mul_eq_iff hev h3n _ _

theorem H16_D_zero (lam : ZMod n → L) (k : ZMod n) (hk : Odd k.val) : H16_D lam 0 k = lam k := by
  unfold H16_D
  have : (topLayer n).filter (fun ρ => (2 ^ 0 : ZMod n) * ρ = k) = {k} := by
    ext ρ
    simp only [topLayer, Finset.mem_filter, Finset.mem_univ, true_and, pow_zero, one_mul, Finset.mem_singleton]
    constructor
    · rintro ⟨-, rfl⟩; rfl
    · rintro rfl; exact ⟨hk, rfl⟩
  rw [this, Finset.prod_singleton]

variable (a : ℕ) in
/-- The candidate `ŷ` (with `S = 1`): `f` on layer `0` (multiples of `2^a`), the descent product elsewhere. -/
noncomputable def H16_build (lam f : ZMod n → L) (k : ZMod n) : L :=
  if 2 ^ a ∣ k.val then f k else H16_D lam (padicValNat 2 k.val) k

variable {a nodd : ℕ}

theorem H16_build_ex (lam f : ZMod n → L) {m : ℕ} (hm : m < a) {x : ZMod n} (hx : H16_ex m x) :
    H16_build a lam f x = H16_D lam m x := by
  unfold H16_build
  rw [ite_eq_right, H16_ex_padic x hx]
  intro h; exact hx.2 ((pow_dvd_pow 2 (by omega : m + 1 ≤ a)).trans h)

theorem H16_build_bot (lam f : ZMod n → L) {x : ZMod n} (hx : 2 ^ a ∣ x.val) : H16_build a lam f x = f x := by
  unfold H16_build; rw [ite_eq_left hx]

theorem H16_build_odd (lam f : ZMod n → L) (ha : 1 ≤ a) {x : ZMod n} (hx : Odd x.val) :
    H16_build a lam f x = lam x := by
  rw [H16_build_ex lam f (by omega : 0 < a) ((H16_ex_zero_iff x).mpr hx), H16_D_zero lam x hx]

theorem H16_c3 (ω : L) (σ : ℤ) (h : ZMod n → L) (k : ZMod n) :
    (h (((3 : ℕ) : ZMod n) * k) = (ω ^ k.val) ^ (((3 : ℕ) : ℤ) * σ) * h k ^ 3) ↔
      h (3 * k) = (ω ^ k.val) ^ ((3 : ℤ) * σ) * h k ^ 3 := by
  simp only [Nat.cast_ofNat]

/-- Step 3 (one layer down): `B(2x) = B(x) B(x + m)` above layer `1`. -/
theorem H16_build_R (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (lam f : ZMod n → L) :
    ∀ m, m + 2 ≤ a → ∀ x : ZMod n, H16_ex m x →
      H16_build a lam f (2 * x) = H16_build a lam f x * H16_build a lam f (x + half n) := by
  intro m hm x hx
  have h3n : 3 ≤ n := by have := H16_n_ge hn ha; omega
  rw [H16_build_ex lam f (by omega : m + 1 < a) ((H16_ex_two hn ha hm x).mpr hx),
    H16_D_split (H16_even hn ha) h3n, H16_build_ex lam f (by omega) hx,
    H16_build_ex lam f (by omega) ((H16_ex_add_half hn hm x).mpr hx)]

theorem H16_not_odd_of_ex (_hn : n = 2 ^ a * nodd) {m : ℕ} {k : ZMod n} (hk : H16_ex (m + 1) k) : ¬ Odd k.val := by
  intro ho
  have : 2 ∣ k.val := dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero m)) hk.1
  exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr this)

theorem H16_wh (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) {ω : L} (hω : IsPrimitiveRoot ω n) (x : ZMod n) :
    ω ^ (x + half n).val = -ω ^ x.val := by
  have h2n : 2 ≤ n := by have := H16_n_ge hn ha; omega
  rw [H4_pow_val_add hω.pow_eq_one, H4_pow_val_half hω (H16_even hn ha) h2n, mul_neg_one]

theorem H16_w2 {ω : L} (hω : IsPrimitiveRoot ω n) (x : ZMod n) : ω ^ (2 * x).val = ω ^ x.val * ω ^ x.val := by
  rw [two_mul, H4_pow_val_add hω.pow_eq_one]

theorem H16_half_even (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) : Even (n / 2) := by
  have := H16_four_dvd hn ha; exact ⟨n / 4, by omega⟩

/-- (F3) on the layers `a, a-1, …, 1` (any shift: only (F3) of the top data is used). -/
theorem H16_mid3 (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) {ω : L} (hω : IsPrimitiveRoot ω n) {σ : ℤ}
    (lam f : ZMod n → L) (hlam : lam ∈ topData n 3 σ (1 : L) ω) :
    ∀ m, m + 1 ≤ a → ∀ x : ZMod n, H16_ex m x →
      H16_build a lam f x * H16_build a lam f (-x) = (ω ^ x.val) ^ (n / 2) := by
  have hev := H16_even hn ha
  intro m
  induction m with
  | zero =>
    intro _ x hx
    have hxo : Odd x.val := (H16_ex_zero_iff x).mp hx
    have hno : Odd (-x).val := (H16_ex_zero_iff _).mp ((H16_ex_neg hn (by omega) x).mpr hx)
    rw [H16_build_odd lam f (by omega) hxo, H16_build_odd lam f (by omega) hno, (hlam.1 x hxo).2, one_mul]
  | succ m ih =>
    intro hm k hk
    obtain ⟨x, rfl⟩ : ∃ x : ZMod n, 2 * x = k := ⟨_, H4_two_mul_hf k (H16_not_odd_of_ex hn hk)⟩
    have hx : H16_ex m x := (H16_ex_two hn ha (by omega) x).mp hk
    have hxh : H16_ex m (x + half n) := (H16_ex_add_half hn (by omega) x).mpr hx
    have i1 := ih (by omega) x hx
    have i2 := ih (by omega) (x + half n) hxh
    rw [H16_wh hn ha hω, Even.neg_pow (H16_half_even hn ha)] at i2
    rw [show -(2 * x) = 2 * (-x) by ring, H16_build_R hn ha lam f m (by omega) x hx,
      H16_build_R hn ha lam f m (by omega) (-x) ((H16_ex_neg hn (by omega) x).mpr hx),
      show -x + half n = -(x + half n) by rw [neg_add, H4_neg_half hev], H16_w2 hω, mul_pow]
    linear_combination (H16_build a lam f (x + half n) * H16_build a lam f (-(x + half n))) * i1 +
      (ω ^ x.val) ^ (n / 2) * i2

/-- (F1_σ) on the layers `a, a-1, …, 1`, for an even shift `σ`. -/
theorem H16_mid1 (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) {ω : L} (hω : IsPrimitiveRoot ω n) {σ : ℤ} (hσ : Even σ)
    (lam f : ZMod n → L) (hlam : lam ∈ topData n 3 σ (1 : L) ω) :
    ∀ m, m + 1 ≤ a → ∀ x : ZMod n, H16_ex m x →
      H16_build a lam f (3 * x) = (ω ^ x.val) ^ ((3 : ℤ) * σ) * H16_build a lam f x ^ 3 := by
  have hev := H16_even hn ha
  have h3σ : Even ((3 : ℤ) * σ) := hσ.mul_left 3
  intro m
  induction m with
  | zero =>
    intro _ x hx
    have hxo : Odd x.val := (H16_ex_zero_iff x).mp hx
    have h3o : Odd (3 * x).val := (H16_ex_zero_iff _).mp ((H16_ex_three hn ha (by omega) x).mpr hx)
    rw [H16_build_odd lam f (by omega) hxo, H16_build_odd lam f (by omega) h3o]
    exact (H16_c3 ω σ lam x).mp (hlam.1 x hxo).1
  | succ m ih =>
    intro hm k hk
    obtain ⟨x, rfl⟩ : ∃ x : ZMod n, 2 * x = k := ⟨_, H4_two_mul_hf k (H16_not_odd_of_ex hn hk)⟩
    have hx : H16_ex m x := (H16_ex_two hn ha (by omega) x).mp hk
    have hxh : H16_ex m (x + half n) := (H16_ex_add_half hn (by omega) x).mpr hx
    have hx3 : H16_ex m (3 * x) := (H16_ex_three hn ha (by omega) x).mpr hx
    rw [show (3 : ZMod n) * (2 * x) = 2 * (3 * x) by ring, H16_build_R hn ha lam f m (by omega) (3 * x) hx3,
      H16_build_R hn ha lam f m (by omega) x hx,
      show 3 * x + half n = 3 * (x + half n) by rw [mul_add, H16_three_half hev],
      ih (by omega) x hx, ih (by omega) (x + half n) hxh, H16_wh hn ha hω, Even.neg_zpow h3σ, H16_w2 hω,
      mul_zpow]
    ring

/-- `ŷ(-1) = 1` (exponent model `n/2`), from (F3) at `n/4` (Step 3 of Thm 4.1 with `S = 1`). -/
theorem H16_build_half (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) {ω : L} (hω : IsPrimitiveRoot ω n)
    {σ : ℤ} (lam f : ZMod n → L) (hlam : lam ∈ topData n 3 σ (1 : L) ω) : H16_build a lam f (half n) = 1 := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 3 := ⟨a - 3, by omega⟩
  have hc : n = 8 * (2 ^ b * nodd) := by rw [hn]; ring
  set c := 2 ^ b * nodd with hcdef
  have hcpos : 0 < c := by
    have := NeZero.pos n; omega
  set q : ZMod n := ((n / 4 : ℕ) : ZMod n) with hq
  have hqv : q.val = n / 4 := by rw [hq, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hq4 : n / 4 = 2 ^ (b + 1) * nodd := by
    have : 2 ^ (b + 1) * nodd = 2 * c := by rw [hcdef]; ring
    omega
  have hex : H16_ex (b + 3 - 2) q := by
    rw [show b + 3 - 2 = b + 1 by omega]
    refine ⟨by rw [hqv, hq4]; exact Dvd.dvd.mul_right dvd_rfl _, ?_⟩
    rw [hqv, hq4, pow_succ 2 (b + 1), Nat.mul_dvd_mul_iff_left (by positivity)]
    intro h; obtain ⟨d, hd⟩ := hodd; omega
  have h2q : 2 * q = half n := by
    rw [hq]; unfold half
    rw [show (2 : ZMod n) = ((2 : ℕ) : ZMod n) by norm_num, ← Nat.cast_mul]
    congr 1; omega
  have hqh : q + half n = -q := by
    apply eq_neg_of_add_eq_zero_left
    rw [show q + half n + q = 2 * q + half n by ring, h2q, H4_half_add_half (H16_even hn ha)]
  rw [← h2q, H16_build_R hn ha lam f (b + 3 - 2) (by omega) q hex, hqh,
    H16_mid3 hn ha hω lam f hlam (b + 3 - 2) (by omega) q hex, hqv, ← pow_mul,
    show n / 4 * (n / 2) = n * c by rw [hc]; rw [show 8 * c / 4 = 2 * c by omega, show 8 * c / 2 = 4 * c by omega]; ring,
    pow_mul, hω.pow_eq_one, one_pow]

/-- (F1_σ), (F3) on layer `0` (multiples of `2^a`), from `f ∈ G'_σ` (and `f(1) = 1`). -/
theorem H16_bot_F (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (_h3 : ¬ 3 ∣ n) {ω : L} {σ : ℤ} (lam f : ZMod n → L)
    (hf : f ∈ Gprime n a 3 σ (1 : L) ω) (x : ZMod n) (hx : 2 ^ a ∣ x.val) :
    H16_build a lam f (3 * x) = (ω ^ x.val) ^ ((3 : ℤ) * σ) * H16_build a lam f x ^ 3 ∧
      H16_build a lam f x * H16_build a lam f (-x) = (ω ^ x.val) ^ (n / 2) := by
  have h3n : 3 < n := by have := H16_n_ge hn ha; omega
  have h3x : 2 ^ a ∣ (3 * x).val := (H16_dvd_three (H16_pow_dvd hn le_rfl) h3n x).mpr hx
  have hnx : 2 ^ a ∣ (-x).val := (H16_dvd_val_neg (H16_pow_dvd hn le_rfl) x).mpr hx
  rw [H16_build_bot lam f hx, H16_build_bot lam f h3x, H16_build_bot lam f hnx]
  by_cases hx0 : x = 0
  · subst hx0
    have hf0 : f 0 = 1 := hf.2 0 (by simp [H16_mem_layer0])
    simp [hf0]
  · have hmem : x ∈ layer0' n a := H16_mem_layer0.mpr ⟨hx, hx0⟩
    obtain ⟨e2, e3⟩ := hf.1 x hmem
    exact ⟨(H16_c3 ω σ f x).mp e2, by rw [e3, one_mul]⟩

theorem H16_F13 (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (h3 : ¬ 3 ∣ n) {ω : L} (hω : IsPrimitiveRoot ω n)
    {σ : ℤ} (hσ : Even σ) (lam f : ZMod n → L) (hlam : lam ∈ topData n 3 σ (1 : L) ω)
    (hf : f ∈ Gprime n a 3 σ (1 : L) ω) (x : ZMod n) :
    H16_build a lam f (3 * x) = (ω ^ x.val) ^ ((3 : ℤ) * σ) * H16_build a lam f x ^ 3 ∧
      H16_build a lam f x * H16_build a lam f (-x) = (ω ^ x.val) ^ (n / 2) := by
  rcases H16_classify (a := a) x with hx | ⟨m, hm, hx⟩
  · exact H16_bot_F hn ha h3 lam f hf x hx
  · exact ⟨H16_mid1 hn ha hω hσ lam f hlam m (by omega) x hx, H16_mid3 hn ha hω lam f hlam m (by omega) x hx⟩

theorem H16_Pmap_eq (lam : ZMod n → L) {k : ZMod n} (hk : k ∈ layer0' n a) :
    Pmap n a lam k = H16_D lam (a - 1) (k + half n) := by
  unfold Pmap H16_D; rw [ite_eq_left hk]

/-- (F4) everywhere, given (E1) `f(α^2) = P_λ(α) f(α)` on `μ_{n_odd} ∖ {1}` and `f(1) = 1`. -/
theorem H16_F4 (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) {ω : L} (hω : IsPrimitiveRoot ω n)
    {σ : ℤ} (lam f : ZMod n → L) (hlam : lam ∈ topData n 3 σ (1 : L) ω) (hf0 : f 0 = 1)
    (hE1 : ∀ k ∈ layer0' n a, f (2 * k) = Pmap n a lam k * f k) (x : ZMod n) :
    H16_build a lam f x * H16_build a lam f (x + half n) =
      H16_build a lam f (half n) * H16_build a lam f (2 * x) := by
  have hev := H16_even hn ha
  have hhalf := H16_build_half hn ha hodd hω lam f hlam
  rw [hhalf, one_mul]
  rcases H16_classify (a := a) x with hx | ⟨m, hm, hx⟩
  · rw [H16_build_bot lam f (H16_bot_two_mul hn ha x hx), H16_build_bot lam f hx]
    by_cases hx0 : x = 0
    · subst hx0; rw [zero_add, hhalf, mul_zero, hf0, mul_one]
    · rw [hE1 x (H16_mem_layer0.mpr ⟨hx, hx0⟩), H16_Pmap_eq lam (H16_mem_layer0.mpr ⟨hx, hx0⟩),
        ← H16_build_ex lam f (by omega : a - 1 < a) (H16_bot_add_half hn (by omega) hodd x hx)]
      ring
  · by_cases hm2 : m + 2 ≤ a
    · exact (H16_build_R hn ha lam f m hm2 x hx).symm
    · obtain rfl : m = a - 1 := by omega
      have hα : 2 ^ a ∣ (x + half n).val := H16_top_add_half hn (by omega) hodd x hx
      have hxα : x + half n + half n = x := by rw [add_assoc, H4_half_add_half hev, add_zero]
      have h2 : 2 * (x + half n) = 2 * x := by rw [mul_add, H4_two_mul_half hev, add_zero]
      by_cases hα0 : x + half n = 0
      · have hxh : x = half n := by
          rw [← hxα, hα0, zero_add]
        have hB0 : H16_build a lam f 0 = 1 := by rw [H16_build_bot (x := 0) lam f (by simp), hf0]
        rw [hα0, hB0, mul_one, hxh, H4_two_mul_half hev, hB0, hhalf]
      · have hmem : x + half n ∈ layer0' n a := H16_mem_layer0.mpr ⟨hα, hα0⟩
        rw [← h2, H16_build_bot lam f (H16_bot_two_mul hn ha _ hα), H16_build_bot lam f hα, hE1 _ hmem,
          H16_Pmap_eq lam hmem, hxα, H16_build_ex lam f (by omega) hx]

/-- `P_λ` of top data with shift `σ` is in `G'_σ` (laws of `P` inherited from layer `1`). -/
theorem H16_Pmap_mem (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n) {ω : L}
    (hω : IsPrimitiveRoot ω n) {σ : ℤ} (hσ : Even σ) (lam : ZMod n → L) (hlam : lam ∈ topData n 3 σ (1 : L) ω) :
    Pmap n a lam ∈ Gprime n a 3 σ (1 : L) ω := by
  have hev := H16_even hn ha
  have h3n : 3 < n := by have := H16_n_ge hn ha; omega
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · obtain ⟨hk', hk0⟩ := H16_mem_layer0.mp hk
    have h3k : 3 * k ∈ layer0' n a :=
      H16_mem_layer0.mpr ⟨(H16_dvd_three (H16_pow_dvd hn le_rfl) h3n k).mpr hk', H16_three_mul_ne h3 hk0⟩
    have hnk : -k ∈ layer0' n a :=
      H16_mem_layer0.mpr ⟨(H16_dvd_val_neg (H16_pow_dvd hn le_rfl) k).mpr hk', neg_ne_zero.mpr hk0⟩
    have hkh : H16_ex (a - 1) (k + half n) := H16_bot_add_half hn (by omega) hodd k hk'
    have e1 : Pmap n a lam k = H16_build a lam 1 (k + half n) := by
      rw [H16_Pmap_eq lam hk, H16_build_ex lam 1 (by omega) hkh]
    have e3 : Pmap n a lam (3 * k) = H16_build a lam 1 (3 * (k + half n)) := by
      rw [H16_Pmap_eq lam h3k, show (3 : ZMod n) * (k + half n) = 3 * k + half n by
        rw [mul_add, H16_three_half hev],
        H16_build_ex lam 1 (by omega) (H16_bot_add_half hn (by omega) hodd _ (H16_mem_layer0.mp h3k).1)]
    have en : Pmap n a lam (-k) = H16_build a lam 1 (-(k + half n)) := by
      rw [H16_Pmap_eq lam hnk, show -(k + half n) = -k + half n by rw [neg_add, H4_neg_half hev],
        H16_build_ex lam 1 (by omega) (H16_bot_add_half hn (by omega) hodd _ (H16_mem_layer0.mp hnk).1)]
    have f1 := H16_mid1 hn ha hω hσ lam 1 hlam (a - 1) (by omega) (k + half n) hkh
    have f3 := H16_mid3 hn ha hω lam 1 hlam (a - 1) (by omega) (k + half n) hkh
    refine ⟨(H16_c3 ω σ (Pmap n a lam) k).mpr ?_, ?_⟩
    · rw [e3, e1, f1, H16_wh hn ha hω, Even.neg_zpow (hσ.mul_left 3)]
    · rw [e1, en, f3, H16_wh hn ha hω, one_mul, Even.neg_pow (H16_half_even hn ha)]
  · unfold Pmap; rw [ite_eq_right hk]

theorem H16_Pmap_mul (l1 l2 : ZMod n → L) : Pmap n a (l1 * l2) = Pmap n a l1 * Pmap n a l2 := by
  funext k
  simp only [Pmap, Pi.mul_apply]
  split_ifs
  · exact Finset.prod_mul_distrib
  · ring

theorem H16_topData_mul {ω : L} {σ : ℤ} (mu lam : ZMod n → L) (hmu : mu ∈ (topData0 n 3 : Set (ZMod n → L)))
    (hlam : lam ∈ topData n 3 σ (1 : L) ω) : mu * lam ∈ topData n 3 σ (1 : L) ω := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · obtain ⟨m1, m3⟩ := hmu.1 k hk
    obtain ⟨l1, l3⟩ := hlam.1 k hk
    simp only [Pi.mul_apply]
    constructor
    · rw [m1, l1]; ring
    · calc mu k * lam k * (mu (-k) * lam (-k)) = (mu k * mu (-k)) * (lam k * lam (-k)) := by ring
        _ = _ := by rw [m3, l3, one_mul, one_mul]
  · simp only [Pi.mul_apply]; rw [hlam.2 k hk, mul_zero]

theorem H16_Gprime_ne_zero {ω : L} (hω : IsPrimitiveRoot ω n) {σ : ℤ} {f : ZMod n → L}
    (hf : f ∈ Gprime n a 3 σ (1 : L) ω) (k : ZMod n) : f k ≠ 0 := by
  by_cases hk : k ∈ layer0' n a
  · intro h0
    have := (hf.1 k hk).2
    rw [h0, zero_mul, one_mul] at this
    exact pow_ne_zero _ (pow_ne_zero _ (hω.ne_zero (NeZero.ne n))) this.symm
  · rw [hf.2 k hk]; exact one_ne_zero

/-- EXISTENCE (the last paragraph of Step 7), for an even shift `σ`: top data with `P ∈ (τ f_0/f_0)(τ-1)G` exist, and
then the layers below are filled by the descent (`S = 1`) and by `f_0`; the result satisfies (F1_σ), (F3), (F4). -/
theorem H16_exists_F (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n) {ω : L}
    (hω : IsPrimitiveRoot ω n) {σ : ℤ} (hσ : Even σ) (hD : (topData n 3 σ (1 : L) ω).Nonempty)
    (hG'ne : (Gprime n a 3 σ (1 : L) ω).Nonempty)
    (hquot : ∀ f ∈ Gprime n a 3 σ (1 : L) ω, ∀ f' ∈ Gprime n a 3 σ (1 : L) ω,
      f' / f ∈ (Ggrp n a 3 : Set (ZMod n → L)))
    (hτf : ∀ f ∈ Gprime n a 3 σ (1 : L) ω, tauG n a f / f ∈ Gprime n a 3 σ (1 : L) ω)
    (hsurj : Set.SurjOn (Pmap n a) (topData0 n 3 : Set (ZMod n → L)) (Ggrp n a 3)) :
    ∃ h : ZMod n → L, F1 3 σ ω h ∧ F3 ω h ∧ F4 h := by
  obtain ⟨lam0, hlam0⟩ := hD
  obtain ⟨f0, hf0⟩ := hG'ne
  have hP0 := H16_Pmap_mem hn ha hodd h3 hω hσ lam0 hlam0
  obtain ⟨mu, hmu, hmuP⟩ := hsurj (hquot _ hP0 _ (hτf f0 hf0))
  have hlam := H16_topData_mul mu lam0 hmu hlam0
  have hE1 : ∀ k ∈ layer0' n a, f0 (2 * k) = Pmap n a (mu * lam0) k * f0 k := by
    intro k hk
    rw [H16_Pmap_mul, Pi.mul_apply, hmuP, Pi.div_apply, Pi.div_apply,
      div_mul_cancel₀ _ (H16_Gprime_ne_zero hω hP0 k), div_mul_cancel₀ _ (H16_Gprime_ne_zero hω hf0 k)]
    unfold tauG; rw [ite_eq_left hk]
  have hf00 : f0 0 = 1 := hf0.2 0 (by simp [H16_mem_layer0])
  refine ⟨H16_build a (mu * lam0) f0, fun k => (H16_c3 ω σ _ k).mpr ?_, fun k => ?_, fun k => ?_⟩
  · exact (H16_F13 hn ha h3 hω hσ _ f0 hlam hf0 k).1
  · exact (H16_F13 hn ha h3 hω hσ _ f0 hlam hf0 k).2
  · exact H16_F4 hn ha hodd hω _ f0 hlam hf00 hE1 k

end Build

/-! ## 2b. Shift `0`: explicit top data `χ = ±1` on the classes `±⟨3⟩` of `(ℤ/2^a)^×`, and a shift-0 solution -/

section Shift0

variable {n : ℕ} [NeZero n] {L : Type*} [Field L] {a nodd : ℕ}

variable (L) in
/-- `χ(k) = 1` if `k ≡ 1, 3 (mod 8)`, `χ(k) = -1` if `k ≡ 5, 7 (mod 8)`, `χ(k) = 0` for even `k`. -/
noncomputable def H16_chi (k : ZMod n) : L :=
  if k.val % 2 = 1 then (if k.val % 8 = 1 ∨ k.val % 8 = 3 then 1 else -1) else 0

theorem H16_val3_mod8 (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (k : ZMod n) : (3 * k).val % 8 = 3 * k.val % 8 := by
  have h3n : 3 < n := by have := H16_n_ge hn ha; omega
  have h8 : 8 ∣ n := (show (8 : ℕ) = 2 ^ 3 by norm_num) ▸ H16_pow_dvd hn ha
  rw [ZMod.val_mul, H16_val_three h3n, Nat.mod_mod_of_dvd _ h8]

theorem H16_valneg_mod8 (hn : n = 2 ^ a * nodd) (_ha : 3 ≤ a) (k : ZMod n) (hk : k ≠ 0) :
    (-k).val + k.val = n := by
  rw [ZMod.neg_val, ite_eq_right hk]; have := ZMod.val_lt k; omega

theorem H16_chi_top (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) {ω : L} (hω : IsPrimitiveRoot ω n) :
    H16_chi L ∈ topData n 3 0 (1 : L) ω := by
  have h8 : 8 ∣ n := (show (8 : ℕ) = 2 ^ 3 by norm_num) ▸ H16_pow_dvd hn ha
  have hev := H16_even hn ha
  have h2n : 2 ≤ n := by have := H16_n_ge hn ha; omega
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · have hk2 : k.val % 2 = 1 := Nat.odd_iff.mp hk
    have hk0 : k ≠ 0 := by intro h; rw [h, ZMod.val_zero] at hk2; omega
    have h3v := H16_val3_mod8 hn ha k
    have hnv := H16_valneg_mod8 hn ha k hk0
    simp only [Nat.cast_ofNat, mul_zero, zpow_zero, one_mul]
    have e3 : H16_chi L (3 * k) = H16_chi L k := by
      unfold H16_chi
      rw [ite_eq_left (by omega), ite_eq_left hk2]
      by_cases hc : k.val % 8 = 1 ∨ k.val % 8 = 3
      · rw [ite_eq_left hc, ite_eq_left (by omega)]
      · rw [ite_eq_right hc, ite_eq_right (by omega)]
    have en : H16_chi L (-k) = -H16_chi L k := by
      unfold H16_chi
      rw [ite_eq_left (by omega), ite_eq_left hk2]
      by_cases hc : k.val % 8 = 1 ∨ k.val % 8 = 3
      · rw [ite_eq_left hc, ite_eq_right (by omega)]
      · rw [ite_eq_right hc, ite_eq_left (by omega), neg_neg]
    have hpm : H16_chi L k = 1 ∨ H16_chi L k = -1 := by
      unfold H16_chi; rw [ite_eq_left hk2]; split_ifs <;> simp
    have hwk : (ω ^ k.val) ^ (n / 2) = -1 := by
      rw [← pow_mul, mul_comm, pow_mul, H4_pow_half hω hev h2n, Odd.neg_one_pow hk]
    refine ⟨?_, ?_⟩
    · rw [e3]; rcases hpm with h | h <;> rw [h] <;> ring
    · rw [en, hwk]; rcases hpm with h | h <;> rw [h] <;> ring
  · unfold H16_chi; rw [ite_eq_right (by have := Nat.even_iff.mp hk; omega)]

theorem H16_w_layer0 (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) {ω : L} (hω : IsPrimitiveRoot ω n) (k : ZMod n)
    (hk : 2 ^ a ∣ k.val) : (ω ^ k.val) ^ (n / 2) = 1 := by
  obtain ⟨u, hu⟩ := hk
  rw [← pow_mul, hu, H16_half_eq hn (by omega),
    show 2 ^ a * u * (2 ^ (a - 1) * nodd) = n * (2 ^ (a - 1) * u) by rw [hn]; ring, pow_mul, hω.pow_eq_one, one_pow]

theorem H16_Gprime0_sub (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) {ω : L} (hω : IsPrimitiveRoot ω n) {g : ZMod n → L}
    (hg : g ∈ Gprime n a 3 0 (1 : L) ω) : g ∈ (Ggrp n a 3 : Set (ZMod n → L)) := by
  refine ⟨fun k hk => ?_, hg.2⟩
  obtain ⟨e2, e3⟩ := hg.1 k hk
  refine ⟨by rw [e2, mul_zero, zpow_zero, one_mul], ?_⟩
  rw [mul_comm, e3, one_mul, H16_w_layer0 hn ha hω k (H16_mem_layer0.mp hk).1]

theorem H16_one_Gprime0 (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) {ω : L} (hω : IsPrimitiveRoot ω n) :
    (1 : ZMod n → L) ∈ Gprime n a 3 0 (1 : L) ω := by
  refine ⟨fun k hk => ?_, fun k _ => rfl⟩
  simp only [Pi.one_apply, mul_zero, zpow_zero, one_pow, mul_one, one_mul]
  exact ⟨trivial, (H16_w_layer0 hn ha hω k (H16_mem_layer0.mp hk).1).symm⟩

/-- A solution of the Fourier laws with shift `0` (top data `μ χ`, `f = 1`, `μ ∈ 𝒟^0` with `P_μ = P_χ^{-1}`). -/
theorem H16_shift0 (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n) {ω : L}
    (hω : IsPrimitiveRoot ω n)
    (hGinv : ∀ g ∈ (Ggrp n a 3 : Set (ZMod n → L)), g⁻¹ ∈ (Ggrp n a 3 : Set (ZMod n → L)))
    (hsurj : Set.SurjOn (Pmap n a) (topData0 n 3 : Set (ZMod n → L)) (Ggrp n a 3)) :
    ∃ g : ZMod n → L, F1 3 0 ω g ∧ F3 ω g ∧ F4 g := by
  have hχ := H16_chi_top hn ha hω
  have hP := H16_Pmap_mem hn ha hodd h3 hω (⟨0, by norm_num⟩ : Even (0 : ℤ)) (H16_chi L) hχ
  obtain ⟨mu, hmu, hmuP⟩ := hsurj (hGinv _ (H16_Gprime0_sub hn ha hω hP))
  have hlam := H16_topData_mul mu (H16_chi L) hmu hχ
  have hf1 := H16_one_Gprime0 hn ha hω
  have hE1 : ∀ k ∈ layer0' n a, (1 : ZMod n → L) (2 * k) = Pmap n a (mu * H16_chi L) k * (1 : ZMod n → L) k := by
    intro k _
    rw [H16_Pmap_mul, Pi.mul_apply, hmuP, Pi.inv_apply, inv_mul_cancel₀ (H16_Gprime_ne_zero hω hP k)]
    simp
  refine ⟨H16_build a (mu * H16_chi L) 1, fun k => (H16_c3 ω 0 _ k).mpr ?_, fun k => ?_, fun k => ?_⟩
  · exact (H16_F13 hn ha h3 hω (⟨0, by norm_num⟩ : Even (0 : ℤ)) _ 1 hlam hf1 k).1
  · exact (H16_F13 hn ha h3 hω (⟨0, by norm_num⟩ : Even (0 : ℤ)) _ 1 hlam hf1 k).2
  · exact H16_F4 hn ha hodd hω _ 1 hlam rfl hE1 k

/-- Products: `h^j g^{j+1}` with `h` of shift `2` and `g` of shift `0` has shift `2j` (and (F3), (F4)). -/
theorem H16_prod_sol {ω : L} (hω : IsPrimitiveRoot ω n) (hev : Even n) (j : ℕ) (h g : ZMod n → L)
    (hh : F1 3 2 ω h ∧ F3 ω h ∧ F4 h) (hg : F1 3 0 ω g ∧ F3 ω g ∧ F4 g) :
    F1 3 ((j + j : ℕ) : ℤ) ω (fun k => h k ^ j * g k ^ (j + 1)) ∧ F3 ω (fun k => h k ^ j * g k ^ (j + 1)) ∧
      F4 (fun k => h k ^ j * g k ^ (j + 1)) := by
  obtain ⟨h1, h3, h4⟩ := hh
  obtain ⟨g1, g3, g4⟩ := hg
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_⟩
  · show h (((3 : ℕ) : ZMod n) * k) ^ j * g (((3 : ℕ) : ZMod n) * k) ^ (j + 1) =
      (ω ^ k.val) ^ (((3 : ℕ) : ℤ) * ((j + j : ℕ) : ℤ)) * (h k ^ j * g k ^ (j + 1)) ^ 3
    rw [h1 k, g1 k, mul_zero, zpow_zero, one_mul,
      show ((3 : ℕ) : ℤ) * 2 = ((6 : ℕ) : ℤ) by norm_num,
      show ((3 : ℕ) : ℤ) * ((j + j : ℕ) : ℤ) = ((6 * j : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast]
    ring
  · show h k ^ j * g k ^ (j + 1) * (h (-k) ^ j * g (-k) ^ (j + 1)) = (ω ^ k.val) ^ (n / 2)
    have hV : (ω ^ k.val) ^ (n / 2) * (ω ^ k.val) ^ (n / 2) = 1 := by
      rw [← pow_add, show n / 2 + n / 2 = n by obtain ⟨r, hr⟩ := hev; omega, ← pow_mul, mul_comm, pow_mul,
        hω.pow_eq_one, one_pow]
    calc h k ^ j * g k ^ (j + 1) * (h (-k) ^ j * g (-k) ^ (j + 1))
        = (h k * h (-k)) ^ j * (g k * g (-k)) ^ (j + 1) := by ring
      _ = ((ω ^ k.val) ^ (n / 2) * (ω ^ k.val) ^ (n / 2)) ^ j * (ω ^ k.val) ^ (n / 2) := by rw [h3, g3]; ring
      _ = (ω ^ k.val) ^ (n / 2) := by rw [hV, one_pow, one_mul]
  · show h k ^ j * g k ^ (j + 1) * (h (k + half n) ^ j * g (k + half n) ^ (j + 1)) =
      h (half n) ^ j * g (half n) ^ (j + 1) * (h (2 * k) ^ j * g (2 * k) ^ (j + 1))
    calc h k ^ j * g k ^ (j + 1) * (h (k + half n) ^ j * g (k + half n) ^ (j + 1))
        = (h k * h (k + half n)) ^ j * (g k * g (k + half n)) ^ (j + 1) := by ring
      _ = _ := by rw [h4 k, g4 k]; ring

end Shift0

/-! ## 2c. Fourier form with shift `σ` (as Prop 2.4, via the general lemmas of FourierR.lean) and the torsor count -/

section SigmaFourier

variable {n : ℕ} [NeZero n]

theorem H16_NF_iff {K : Type*} [Field K] [CharP K 3] {ω : K} (hω : IsPrimitiveRoot ω n) (hn : Even n) (h3 : 3 ≤ n)
    (hnK : (n : K) ≠ 0) (h2K : (2 : K) ≠ 0) (hrn : IsUnit ((3 : ℕ) : ZMod n)) (σ : ℤ) (Y : ZMod n → K) :
    NormFreeEqs σ Y ↔ F1 3 σ ω (dft ω Y) ∧ F3 ω (dft ω Y) ∧ F4 (dft ω Y) := by
  have hF3 : (L3 0 Y ∧ R Y (half n) = 1) ↔ F3 ω (dft ω Y) := by
    rw [H20_L3R_iff hω hnK hn Y 0 1]
    unfold F3
    simp only [zero_mul, ite_self, zero_add, sub_zero, one_mul]
  unfold NormFreeEqs
  rw [H20_L1_iff_F1 3 hω hnK hrn σ Y, H20_L4_iff_F4 hω hnK hn h3 h2K Y, ← hF3]
  tauto

theorem H16_NF_map {F K : Type*} [CommRing F] [CommRing K] (f : F →+* K) (hf : Function.Injective f) (σ : ℤ)
    (y : ZMod n → F) : NormFreeEqs σ y ↔ NormFreeEqs σ (fun t => f (y t)) := by
  have hsgn : ∀ t : ZMod n, f (sgn t) = sgn t := by intro t; simp [sgn]
  have eS : S (fun t => f (y t)) = f (S y) := by simp [S, map_sum, map_mul, hsgn]
  have e1 : ∀ s : ZMod n, f (y (s + σ)) = f (y s) ^ 3 ↔ y (s + σ) = y s ^ 3 := by
    intro s; rw [← map_pow, hf.eq_iff]
  have e3 : ∀ s : ZMod n, (∑ t, f (y t) * f (y (s + t)) = 0) ↔ ∑ t, y t * y (s + t) = 0 := by
    intro s
    rw [show ∑ t, f (y t) * f (y (s + t)) = f (∑ t, y t * y (s + t)) by simp [map_sum, map_mul]]
    exact map_eq_zero_iff f hf
  have eRm : R (fun t => f (y t)) (half n) = 1 ↔ R y (half n) = 1 := by
    rw [show R (fun t => f (y t)) (half n) = f (R y (half n)) by simp [R, map_sum, map_mul], ← map_one f,
      hf.eq_iff]
  have e4 : ∀ s : ZMod n, (∑ t, sgn t * f (y t) * f (y (2 * s - t)) =
      (f (y s) + f (y (s + half n))) * S (fun t => f (y t))) ↔
      ∑ t, sgn t * y t * y (2 * s - t) = (y s + y (s + half n)) * S y := by
    intro s
    rw [eS, ← hf.eq_iff]; simp [map_sum, map_mul, hsgn]
  unfold NormFreeEqs L1 L3 L4
  simp only [e1, e3, eRm, e4]

/-- Proposition 2.4 with shift `σ` (s4_normfree.tex:146-147): for `σ ∣ n`, `y ↦ ŷ` is a bijection from the norm-free
system with shift `σ` over `F_{3^{n/σ}}` onto the functions with (F1_σ), (F3), (F4). -/
theorem H16_fourier_sigma (h4 : 4 ∣ n) (h3 : ¬ 3 ∣ n) (σ : ℕ) (hσ : σ ∣ n) {L : Type*} [Field L]
    [Algebra (GaloisField 3 (n / σ)) L] (ω : L) (hω : IsPrimitiveRoot ω n) :
    Set.BijOn (dftA ω) (NFSet n σ) {h | F1 3 (σ : ℤ) ω h ∧ F3 ω h ∧ F4 h} := by
  have hn2 : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h4)
  have h3n : 3 ≤ n := le_trans (by norm_num) (Nat.le_of_dvd (NeZero.pos n) h4)
  have hσ0 : 0 < σ := Nat.pos_of_ne_zero (by rintro rfl; exact NeZero.ne n (zero_dvd_iff.mp hσ))
  have hN : n / σ ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (NeZero.pos n) hσ) hσ0).ne'
  have hcard : Nat.card (GaloisField 3 (n / σ)) = 3 ^ (n / σ) := GaloisField.card 3 (n / σ) hN
  have hper : ((n / σ : ℕ) : ZMod n) * ((σ : ℤ) : ZMod n) = 0 := by
    rw [Int.cast_natCast, ← Nat.cast_mul, Nat.div_mul_cancel hσ, ZMod.natCast_self]
  have hinj : Function.Injective (algebraMap (GaloisField 3 (n / σ)) L) :=
    RingHom.injective (algebraMap (GaloisField 3 (n / σ)) L)
  have : CharP L 3 := charP_of_injective_algebraMap hinj 3
  have hnL : (n : L) ≠ 0 := by rw [Ne, CharP.cast_eq_zero_iff L 3]; exact h3
  have h2L : (2 : L) ≠ 0 := by
    have h2' : ((2 : ℕ) : L) ≠ 0 := by rw [Ne, CharP.cast_eq_zero_iff L 3]; omega
    exact_mod_cast h2'
  have hunit : IsUnit ((3 : ℕ) : ZMod n) := (ZMod.isUnit_prime_iff_not_dvd Nat.prime_three).mpr h3
  have hcore := fun (Y : ZMod n → L) => H16_NF_iff hω hn2 h3n hnL h2L hunit (σ : ℤ) Y
  have hmap := fun (y : ZMod n → GaloisField 3 (n / σ)) =>
    H16_NF_map (algebraMap (GaloisField 3 (n / σ)) L) hinj (σ : ℤ) y
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    exact (hcore _).mp ((hmap y).mp hy)
  · intro y1 _ y2 _ h12
    have h12' : dft ω (fun t => algebraMap _ L (y1 t)) = dft ω (fun t => algebraMap _ L (y2 t)) := h12
    have hY := H20_dft_inj hω hnL h12'
    funext t
    exact hinj (congrFun hY t)
  · intro h hh
    have hdY : dft ω (H20_idft ω h) = h := H20_dft_idft hω hnL h
    have hNY : NormFreeEqs (σ : ℤ) (H20_idft ω h) := (hcore _).mpr (by rw [hdY]; exact hh)
    have hfix : ∀ s : ZMod n, H20_idft ω h s ^ Nat.card (GaloisField 3 (n / σ)) = H20_idft ω h s := by
      intro s
      rw [hcard, ← H20_L1_iter 3 (σ : ℤ) _ hNY.1 (n / σ) s, hper, add_zero]
    choose y hy using fun s => H20_mem_range (H20_idft ω h s) (hfix s)
    have hYy : (fun t => algebraMap _ L (y t)) = H20_idft ω h := funext hy
    refine ⟨y, ?_, ?_⟩
    · show NormFreeEqs (σ : ℤ) y
      rw [hmap y, hYy]; exact hNY
    · show dft ω (fun t => algebraMap _ L (y t)) = h
      rw [hYy, hdY]

/-- The solutions of (F1_σ), (F3), (F4) form a `K_n`-torsor: if there is one, there are `|K_n|`. -/
theorem H16_torsor {L : Type*} [Field L] {ω : L} (hω : IsPrimitiveRoot ω n) (σ : ℤ) (H0 : ZMod n → L)
    (hH0 : F1 3 σ ω H0 ∧ F3 ω H0 ∧ F4 H0) :
    Nat.card {h : ZMod n → L // F1 3 σ ω h ∧ F3 ω h ∧ F4 h} =
      Nat.card {lam : ZMod n → L // (∀ k, lam (3 * k) = lam k ^ 3) ∧ (∀ k, lam k * lam (-k) = 1) ∧
        ∀ k, lam k * lam (k + half n) = lam (half n) * lam (2 * k)} := by
  obtain ⟨a1, a3, a4⟩ := hH0
  have hW : ∀ k : ZMod n, ω ^ k.val ≠ 0 := fun k => pow_ne_zero _ (hω.ne_zero (NeZero.ne n))
  have hne : ∀ k, H0 k ≠ 0 := by
    intro k h0; have := a3 k; rw [h0, zero_mul] at this
    exact pow_ne_zero _ (hW k) this.symm
  have hmul : ∀ l : ZMod n → L, ((∀ k, l (3 * k) = l k ^ 3) ∧ (∀ k, l k * l (-k) = 1) ∧
      ∀ k, l k * l (k + half n) = l (half n) * l (2 * k)) →
      F1 3 σ ω (fun k => l k * H0 k) ∧ F3 ω (fun k => l k * H0 k) ∧ F4 (fun k => l k * H0 k) := by
    rintro l ⟨l3, linv, l4⟩
    refine ⟨fun k => (H16_c3 ω σ (fun k => l k * H0 k) k).mpr ?_, fun k => ?_, fun k => ?_⟩
    · show l (3 * k) * H0 (3 * k) = (ω ^ k.val) ^ ((3 : ℤ) * σ) * (l k * H0 k) ^ 3
      rw [l3 k, (H16_c3 ω σ H0 k).mp (a1 k)]; ring
    · show l k * H0 k * (l (-k) * H0 (-k)) = (ω ^ k.val) ^ (n / 2)
      calc l k * H0 k * (l (-k) * H0 (-k)) = (l k * l (-k)) * (H0 k * H0 (-k)) := by ring
        _ = _ := by rw [linv k, a3 k, one_mul]
    · show l k * H0 k * (l (k + half n) * H0 (k + half n)) = l (half n) * H0 (half n) * (l (2 * k) * H0 (2 * k))
      calc l k * H0 k * (l (k + half n) * H0 (k + half n))
          = (l k * l (k + half n)) * (H0 k * H0 (k + half n)) := by ring
        _ = _ := by rw [l4 k, a4 k]; ring
  have hdiv : ∀ h : ZMod n → L, (F1 3 σ ω h ∧ F3 ω h ∧ F4 h) →
      (∀ k, (fun k => h k / H0 k) (3 * k) = (fun k => h k / H0 k) k ^ 3) ∧
      (∀ k, (fun k => h k / H0 k) k * (fun k => h k / H0 k) (-k) = 1) ∧
      ∀ k, (fun k => h k / H0 k) k * (fun k => h k / H0 k) (k + half n) =
        (fun k => h k / H0 k) (half n) * (fun k => h k / H0 k) (2 * k) := by
    rintro h ⟨b1, b3, b4⟩
    refine ⟨fun k => ?_, fun k => ?_, fun k => ?_⟩
    · show h (3 * k) / H0 (3 * k) = (h k / H0 k) ^ 3
      rw [(H16_c3 ω σ h k).mp (b1 k), (H16_c3 ω σ H0 k).mp (a1 k), div_pow,
        mul_div_mul_left _ _ (zpow_ne_zero _ (hW k))]
    · show h k / H0 k * (h (-k) / H0 (-k)) = 1
      rw [div_mul_div_comm, b3 k, a3 k, div_self (pow_ne_zero _ (hW k))]
    · show h k / H0 k * (h (k + half n) / H0 (k + half n)) = h (half n) / H0 (half n) * (h (2 * k) / H0 (2 * k))
      rw [div_mul_div_comm, div_mul_div_comm, b4 k, a4 k]
  symm
  exact Nat.card_congr
    { toFun := fun l => ⟨fun k => l.1 k * H0 k, hmul l.1 l.2⟩
      invFun := fun h => ⟨fun k => h.1 k / H0 k, hdiv h.1 h.2⟩
      left_inv := fun l => Subtype.ext (funext fun k => mul_div_cancel_right₀ _ (hne k))
      right_inv := fun h => Subtype.ext (funext fun k => div_mul_cancel₀ _ (hne k)) }

end SigmaFourier

/-! ## 3. Counting glue: positivity of `∏ (3^{L_i}-1)` and the form `4 Q ∏ (1 - 3^{-L_i})` -/

section Count

variable {n : ℕ} [NeZero n]

theorem H16_pairProd_pos {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) : 0 < pairProd n 3 := by
  have hev := H16_even hn ha
  have h4 := H16_four_dvd hn ha
  have h3n : 3 ≤ n := by have := H16_n_ge hn ha; omega
  unfold pairProd
  refine Finset.prod_pos (fun P hP => ?_)
  obtain ⟨O, hO, rfl⟩ := Finset.mem_image.mp hP
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hO
  have hko : Odd k.val := (Finset.mem_filter.mp hk).2
  have hne : k ≠ -k := by
    intro h
    have h2 : 2 * k = 0 := by rw [two_mul]; nth_rewrite 2 [h]; exact add_neg_cancel k
    rcases H4_two_mul_eq_zero hev h3n k h2 with h0 | h0
    · rw [h0, ZMod.val_zero] at hko; obtain ⟨c, hc⟩ := hko; omega
    · rw [h0, H4_half_val n] at hko; obtain ⟨c, hc⟩ := hko; omega
  have hsub : ({k, -k} : Finset (ZMod n)) ⊆
      ({orbit 3 k, inv (orbit 3 k)} : Finset (Finset (ZMod n))).biUnion id := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rw [Finset.mem_biUnion]
    rcases hz with h | h
    · rw [h]; exact ⟨orbit 3 k, Finset.mem_insert_self _ _, H6_self_mem 3 k⟩
    · rw [h]
      exact ⟨inv (orbit 3 k), Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
        Finset.mem_image_of_mem _ (H6_self_mem 3 k)⟩
  have hc : 2 ≤ (({orbit 3 k, inv (orbit 3 k)} : Finset (Finset (ZMod n))).biUnion id).card := by
    calc 2 = ({k, -k} : Finset (ZMod n)).card := (Finset.card_pair hne).symm
      _ ≤ _ := Finset.card_le_card hsub
  have hL : 1 ≤ pairLen ({orbit 3 k, inv (orbit 3 k)} : Finset (Finset (ZMod n))) := by
    unfold pairLen; omega
  have : 3 ≤ 3 ^ pairLen ({orbit 3 k, inv (orbit 3 k)} : Finset (Finset (ZMod n))) := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hL
  omega

theorem H16_rat {ι : Type*} (s : Finset ι) (len : ι → ℕ) (N : ℕ) (hsum : ∑ P ∈ s, len P = N) :
    ((4 * ∏ P ∈ s, (3 ^ len P - 1) : ℕ) : ℚ) = 4 * 3 ^ N * ∏ P ∈ s, (1 - (3 : ℚ) ^ (-(len P : ℤ))) := by
  subst hsum
  simp only [Nat.cast_mul, Nat.cast_prod, Nat.cast_ofNat]
  rw [mul_assoc, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl (fun P _ => ?_)
  rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num)), Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat, mul_sub, mul_one,
    zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ (by norm_num))]

/-- From `|NF(n)| = 4 ∏ (3^{L_i}-1)` to the full printed conclusion of Theorem 4.1 (pure glue, with row 14a proved). -/
theorem H16_count_glue (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n) (hcard : Nat.card (NFSet n 2) = 4 * pairProd n 3) :
    Nat.card (NFSet n 2) = 4 * pairProd n 3 ∧ (NFSet n 2).Nonempty ∧
      (Nat.card (NFSet n 2) : ℚ) = 4 * 3 ^ (n / 4) * ∏ P ∈ topPairs n 3, (1 - (3 : ℚ) ^ (-(pairLen P : ℤ))) := by
  refine ⟨hcard, ?_, ?_⟩
  · have hc : 0 < Nat.card (NFSet n 2) := by
      rw [hcard]; exact Nat.mul_pos (by norm_num) (H16_pairProd_pos hn ha)
    exact Set.nonempty_coe_sort.mp (Nat.card_pos_iff.mp hc).1
  · rw [hcard]
    exact H16_rat _ pairLen _ (thm_4_1_pairs_proved n a nodd hn ha hodd h3).2

end Count

/-! ## 4. The targets -/

/-- Row 14b — Theorem 4.1 (s4_normfree.tex:16-21), PROVED GIVEN the rows prop_2_4_bij (4a), thm_4_1_step2 (14e),
thm_4_1_step5 (14g), thm_4_1_step6 (14h), thm_4_1_step7 (14i), each as an exact instance (`L` ranges over `Type`).
Also used (already proved, imported): sec_4_1_homog (`sec_4_1_homog_of_proved` given 4a), thm_4_1_pairs,
thm_3_1_step3. -/
theorem thm_4_1_count_of (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n)
    (hP24 : ∀ (_hev : Even n) {L : Type} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L)
      (_hω : IsPrimitiveRoot ω n), Set.BijOn (dftA ω) (NFSet n 2) {h | F1 3 2 ω h ∧ F3 ω h ∧ F4 h})
    (hS2 : ∀ {L : Type} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (_hω : IsPrimitiveRoot ω n),
      Nat.card (topData n 3 2 (1 : L) ω) = pairProd n 3 ∧ Nat.card (topData0 n 3 : Set (ZMod n → L)) = pairProd n 3 ∧
        (1 : ZMod n → L) ∈ (topData0 n 3 : Set (ZMod n → L)) ∧
        ∀ l1 ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ l2 ∈ (topData0 n 3 : Set (ZMod n → L)),
          l1 * l2 ∈ (topData0 n 3 : Set (ZMod n → L)) ∧ l1⁻¹ ∈ (topData0 n 3 : Set (ZMod n → L)))
    (hS5 : ∀ {L : Type} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (_hω : IsPrimitiveRoot ω n),
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
            Nat.card {g : ZMod n → L // g ∈ G ∧ τ g = g}))
    (hS6 : ∀ {L : Type} [Field L] [CharP L 3] [IsAlgClosed L],
      (∀ lam ∈ (topData0 n 3 : Set (ZMod n → L)), Pmap n a lam ∈ (Ggrp n a 3 : Set (ZMod n → L))) ∧
      (∀ l1 ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ l2 ∈ (topData0 n 3 : Set (ZMod n → L)),
        Pmap n a (l1 * l2) = Pmap n a l1 * Pmap n a l2) ∧
      Set.SurjOn (Pmap n a) (topData0 n 3 : Set (ZMod n → L)) (Ggrp n a 3))
    (hS7 : ∀ {L : Type} [Field L] [CharP L 3] [IsAlgClosed L],
      Nat.card ((fun g => tauG n a g / g) '' (Ggrp n a 3 : Set (ZMod n → L))) *
          Nat.card {g : ZMod n → L // g ∈ (Ggrp n a 3 : Set (ZMod n → L)) ∧ tauG n a g = g} =
        Nat.card (Ggrp n a 3 : Set (ZMod n → L)) ∧
      Nat.card {lam : ZMod n → L // (∀ k, lam (3 * k) = lam k ^ 3) ∧ (∀ k, lam k * lam (-k) = 1) ∧
        ∀ k, lam k * lam (k + half n) = lam (half n) * lam (2 * k)} = 4 * pairProd n 3) :
    Nat.card (NFSet n 2) = 4 * pairProd n 3 ∧ (NFSet n 2).Nonempty ∧
      (Nat.card (NFSet n 2) : ℚ) = 4 * 3 ^ (n / 4) * ∏ P ∈ topPairs n 3, (1 - (3 : ℚ) ^ (-(pairLen P : ℤ))) := by
  have hev : Even n := H16_even hn ha
  obtain ⟨ω, hω⟩ : ∃ ω : AlgebraicClosure (GaloisField 3 (n / 2)), IsPrimitiveRoot ω n := by
    have : NeZero ((n : ℕ) : AlgebraicClosure (GaloisField 3 (n / 2))) :=
      ⟨by rw [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure (GaloisField 3 (n / 2))) 3]; exact h3⟩
    exact HasEnoughRootsOfUnity.exists_isPrimitiveRoot _ n
  have hBij := hP24 hev ω hω
  have hH := sec_4_1_homog_of_proved n hev h3 ω hω hBij
  have hD : (topData n 3 2 (1 : AlgebraicClosure (GaloisField 3 (n / 2))) ω).Nonempty := by
    have hc : Nat.card (topData n 3 2 (1 : AlgebraicClosure (GaloisField 3 (n / 2))) ω) ≠ 0 := by
      rw [(hS2 ω hω).1]; exact (H16_pairProd_pos hn ha).ne'
    exact Set.nonempty_coe_sort.mp (Nat.card_ne_zero.mp hc).1
  obtain ⟨-, hG'ne, hquot, -, hτf, -⟩ := hS5 ω hω
  obtain ⟨-, -, hsurj⟩ := hS6 (L := AlgebraicClosure (GaloisField 3 (n / 2)))
  obtain ⟨h, hh⟩ := H16_exists_F hn ha hodd h3 hω even_two hD hG'ne hquot hτf hsurj
  obtain ⟨y, hy, -⟩ := hBij.surjOn hh
  have hcard : Nat.card (NFSet n 2) = 4 * pairProd n 3 :=
    (hH.2.2.1 ⟨y, hy⟩).trans (hS7 (L := AlgebraicClosure (GaloisField 3 (n / 2)))).2
  exact H16_count_glue n a nodd hn ha hodd h3 hcard

/-- Row 15 — Corollary 4.2 (s4_normfree.tex:26-29), PROVED GIVEN row 14b (thm_4_1_count, for every factorisation
`n = 2^a n_odd`); uses row 3d (sec_2_2_xia_eq). -/
theorem cor_4_2_of (n : ℕ) [NeZero n] (hn : n % 24 = 8)
    (hThm41 : ∀ (a nodd : ℕ), n = 2 ^ a * nodd → 3 ≤ a → Odd nodd → ¬ 3 ∣ n →
      Nat.card (NFSet n 2) = 4 * pairProd n 3 ∧ (NFSet n 2).Nonempty ∧
        (Nat.card (NFSet n 2) : ℚ) = 4 * 3 ^ (n / 4) * ∏ P ∈ topPairs n 3, (1 - (3 : ℚ) ^ (-(pairLen P : ℤ)))) :
    ((XiaSet n 2).Nonempty ↔ ∃ y ∈ NFSet n 2, Nm n (y 0) = -1 ∧ Nm n (y 1) = -1) ∧ (NFSet n 2).Nonempty := by
  refine ⟨?_, ?_⟩
  · rw [(sec_2_2_xia_eq_proved n hn).2]; rfl
  · obtain ⟨a, nodd, hodd, hfac⟩ := Nat.exists_eq_two_pow_mul_odd (NeZero.ne n)
    have ha : 3 ≤ a := by
      have h8' : 8 ∣ n := by omega
      have h8 : 2 ^ 3 ∣ 2 ^ a * nodd := by rw [← hfac]; exact h8'
      have hcop : Nat.Coprime (2 ^ 3) nodd := Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hodd)
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right h8)
    exact (hThm41 a nodd hfac ha hodd (by omega)).2.1

/-- Theorem A (P10s_main.tex:138-146), PROVED GIVEN row 16a (prop_4_3_even, for every even divisor `σ`); uses row 16b
(prop_4_3_odd) and row 27 (xia_sub_nf). -/
theorem thm_A_of (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    (hP43e : ∀ σ : ℕ, σ ∣ n → Even σ → Nat.card (NFSet n σ) = 4 * pairProd n 3) :
    (∀ σ : ℕ, σ ∣ n → Even σ → Nat.card (NFSet n σ) = 4 * pairProd n 3 ∧ (NFSet n σ).Nonempty) ∧
      (∀ σ : ℕ, σ ∣ n → Odd σ → NFSet n σ = ∅) ∧
      (n % 24 = 8 → ∀ σ : ℕ, σ ∣ n → XiaSet n σ ⊆ NFSet n σ) := by
  refine ⟨fun σ hσ he => ⟨hP43e σ hσ he, ?_⟩, fun σ hσ ho => prop_4_3_odd_proved n a nodd hn ha hodd h3 σ hσ ho,
    fun h24 σ hσ => xia_sub_nf_proved n h24 σ hσ⟩
  have hc : 0 < Nat.card (NFSet n σ) := by
    rw [hP43e σ hσ he]; exact Nat.mul_pos (by norm_num) (H16_pairProd_pos hn ha)
  exact Set.nonempty_coe_sort.mp (Nat.card_pos_iff.mp hc).1

/-- Row 16a — Proposition 4.3, even part (s4_normfree.tex:141-143), PROVED GIVEN the rows thm_4_1_step2 (14e),
thm_4_1_step5 (14g), thm_4_1_step6 (14h), thm_4_1_step7 (14i) (exact instances, `L` over `Type`). Route: in
`L = \bar F_3 ⊇ F_{3^{n/σ}}`, a shift-2 solution `h` (Steps 2, 5, 6 + descent) and an explicit shift-0 solution `g`
(top data `χ = ±1` on the classes `±⟨3⟩ mod 2^a`, corrected by Step 6) give the shift-`σ` solution `h^{σ/2} g^{σ/2+1}`;
the solutions of (F1_σ), (F3), (F4) are then a `K_n`-torsor, and `|K_n| = 4 ∏ (3^{L_i}-1)` (Step 7); the Fourier
form with shift `σ` (Prop 2.4 with `σ`, built here from the general lemmas of FourierR.lean) transports this to `y`. -/
theorem prop_4_3_even_of (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n) (σ : ℕ) (hσ : σ ∣ n) (hσe : Even σ)
    (hS2 : ∀ {L : Type} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (_hω : IsPrimitiveRoot ω n),
      Nat.card (topData n 3 2 (1 : L) ω) = pairProd n 3 ∧ Nat.card (topData0 n 3 : Set (ZMod n → L)) = pairProd n 3 ∧
        (1 : ZMod n → L) ∈ (topData0 n 3 : Set (ZMod n → L)) ∧
        ∀ l1 ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ l2 ∈ (topData0 n 3 : Set (ZMod n → L)),
          l1 * l2 ∈ (topData0 n 3 : Set (ZMod n → L)) ∧ l1⁻¹ ∈ (topData0 n 3 : Set (ZMod n → L)))
    (hS5 : ∀ {L : Type} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (_hω : IsPrimitiveRoot ω n),
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
            Nat.card {g : ZMod n → L // g ∈ G ∧ τ g = g}))
    (hS6 : ∀ {L : Type} [Field L] [CharP L 3] [IsAlgClosed L],
      (∀ lam ∈ (topData0 n 3 : Set (ZMod n → L)), Pmap n a lam ∈ (Ggrp n a 3 : Set (ZMod n → L))) ∧
      (∀ l1 ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ l2 ∈ (topData0 n 3 : Set (ZMod n → L)),
        Pmap n a (l1 * l2) = Pmap n a l1 * Pmap n a l2) ∧
      Set.SurjOn (Pmap n a) (topData0 n 3 : Set (ZMod n → L)) (Ggrp n a 3))
    (hS7 : ∀ {L : Type} [Field L] [CharP L 3] [IsAlgClosed L],
      Nat.card ((fun g => tauG n a g / g) '' (Ggrp n a 3 : Set (ZMod n → L))) *
          Nat.card {g : ZMod n → L // g ∈ (Ggrp n a 3 : Set (ZMod n → L)) ∧ tauG n a g = g} =
        Nat.card (Ggrp n a 3 : Set (ZMod n → L)) ∧
      Nat.card {lam : ZMod n → L // (∀ k, lam (3 * k) = lam k ^ 3) ∧ (∀ k, lam k * lam (-k) = 1) ∧
        ∀ k, lam k * lam (k + half n) = lam (half n) * lam (2 * k)} = 4 * pairProd n 3) :
    Nat.card (NFSet n σ) = 4 * pairProd n 3 := by
  obtain ⟨ω, hω⟩ : ∃ ω : AlgebraicClosure (GaloisField 3 (n / σ)), IsPrimitiveRoot ω n := by
    have : NeZero ((n : ℕ) : AlgebraicClosure (GaloisField 3 (n / σ))) :=
      ⟨by rw [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure (GaloisField 3 (n / σ))) 3]; exact h3⟩
    exact HasEnoughRootsOfUnity.exists_isPrimitiveRoot _ n
  have hD : (topData n 3 2 (1 : AlgebraicClosure (GaloisField 3 (n / σ))) ω).Nonempty := by
    have hc : Nat.card (topData n 3 2 (1 : AlgebraicClosure (GaloisField 3 (n / σ))) ω) ≠ 0 := by
      rw [(hS2 ω hω).1]; exact (H16_pairProd_pos hn ha).ne'
    exact Set.nonempty_coe_sort.mp (Nat.card_ne_zero.mp hc).1
  obtain ⟨hG5, hG'ne, hquot, -, hτf, -⟩ := hS5 ω hω
  obtain ⟨-, -, hsurj⟩ := hS6 (L := AlgebraicClosure (GaloisField 3 (n / σ)))
  obtain ⟨h, hh⟩ := H16_exists_F hn ha hodd h3 hω even_two hD hG'ne hquot hτf hsurj
  obtain ⟨g, hg⟩ := H16_shift0 hn ha hodd h3 hω (fun g hg => (hG5.2.2.1 g hg g hg).2) hsurj
  obtain ⟨j, rfl⟩ := hσe
  have hH := H16_prod_sol hω (H16_even hn ha) j h g hh hg
  have hB := H16_fourier_sigma (H16_four_dvd hn ha) h3 (j + j) hσ ω hω
  calc Nat.card (NFSet n (j + j))
      = Nat.card {h : ZMod n → AlgebraicClosure (GaloisField 3 (n / (j + j))) //
          F1 3 ((j + j : ℕ) : ℤ) ω h ∧ F3 ω h ∧ F4 h} := Nat.card_congr (hB.equiv _)
    _ = _ := H16_torsor hω _ _ hH
    _ = 4 * pairProd n 3 := (hS7 (L := AlgebraicClosure (GaloisField 3 (n / (j + j))))).2

/-- Row 14b — Theorem 4.1, second route: PROVED GIVEN only the four step rows 14e, 14g, 14h, 14i (no Prop 2.4
hypothesis: the Fourier form is rebuilt inside `prop_4_3_even_of` at `σ = 2`). -/
theorem thm_4_1_count_of_steps (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n)
    (hS2 : ∀ {L : Type} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (_hω : IsPrimitiveRoot ω n),
      Nat.card (topData n 3 2 (1 : L) ω) = pairProd n 3 ∧ Nat.card (topData0 n 3 : Set (ZMod n → L)) = pairProd n 3 ∧
        (1 : ZMod n → L) ∈ (topData0 n 3 : Set (ZMod n → L)) ∧
        ∀ l1 ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ l2 ∈ (topData0 n 3 : Set (ZMod n → L)),
          l1 * l2 ∈ (topData0 n 3 : Set (ZMod n → L)) ∧ l1⁻¹ ∈ (topData0 n 3 : Set (ZMod n → L)))
    (hS5 : ∀ {L : Type} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (_hω : IsPrimitiveRoot ω n),
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
            Nat.card {g : ZMod n → L // g ∈ G ∧ τ g = g}))
    (hS6 : ∀ {L : Type} [Field L] [CharP L 3] [IsAlgClosed L],
      (∀ lam ∈ (topData0 n 3 : Set (ZMod n → L)), Pmap n a lam ∈ (Ggrp n a 3 : Set (ZMod n → L))) ∧
      (∀ l1 ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ l2 ∈ (topData0 n 3 : Set (ZMod n → L)),
        Pmap n a (l1 * l2) = Pmap n a l1 * Pmap n a l2) ∧
      Set.SurjOn (Pmap n a) (topData0 n 3 : Set (ZMod n → L)) (Ggrp n a 3))
    (hS7 : ∀ {L : Type} [Field L] [CharP L 3] [IsAlgClosed L],
      Nat.card ((fun g => tauG n a g / g) '' (Ggrp n a 3 : Set (ZMod n → L))) *
          Nat.card {g : ZMod n → L // g ∈ (Ggrp n a 3 : Set (ZMod n → L)) ∧ tauG n a g = g} =
        Nat.card (Ggrp n a 3 : Set (ZMod n → L)) ∧
      Nat.card {lam : ZMod n → L // (∀ k, lam (3 * k) = lam k ^ 3) ∧ (∀ k, lam k * lam (-k) = 1) ∧
        ∀ k, lam k * lam (k + half n) = lam (half n) * lam (2 * k)} = 4 * pairProd n 3) :
    Nat.card (NFSet n 2) = 4 * pairProd n 3 ∧ (NFSet n 2).Nonempty ∧
      (Nat.card (NFSet n 2) : ℚ) = 4 * 3 ^ (n / 4) * ∏ P ∈ topPairs n 3, (1 - (3 : ℚ) ^ (-(pairLen P : ℤ))) :=
  H16_count_glue n a nodd hn ha hodd h3
    (prop_4_3_even_of n a nodd hn ha hodd h3 2 (even_iff_two_dvd.mp (H16_even hn ha)) even_two hS2 hS5 hS6 hS7)

/-- Theorem A, second route: PROVED GIVEN only the four step rows 14e, 14g, 14h, 14i. -/
theorem thm_A_of_steps (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n)
    (hS2 : ∀ {L : Type} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (_hω : IsPrimitiveRoot ω n),
      Nat.card (topData n 3 2 (1 : L) ω) = pairProd n 3 ∧ Nat.card (topData0 n 3 : Set (ZMod n → L)) = pairProd n 3 ∧
        (1 : ZMod n → L) ∈ (topData0 n 3 : Set (ZMod n → L)) ∧
        ∀ l1 ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ l2 ∈ (topData0 n 3 : Set (ZMod n → L)),
          l1 * l2 ∈ (topData0 n 3 : Set (ZMod n → L)) ∧ l1⁻¹ ∈ (topData0 n 3 : Set (ZMod n → L)))
    (hS5 : ∀ {L : Type} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (_hω : IsPrimitiveRoot ω n),
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
            Nat.card {g : ZMod n → L // g ∈ G ∧ τ g = g}))
    (hS6 : ∀ {L : Type} [Field L] [CharP L 3] [IsAlgClosed L],
      (∀ lam ∈ (topData0 n 3 : Set (ZMod n → L)), Pmap n a lam ∈ (Ggrp n a 3 : Set (ZMod n → L))) ∧
      (∀ l1 ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ l2 ∈ (topData0 n 3 : Set (ZMod n → L)),
        Pmap n a (l1 * l2) = Pmap n a l1 * Pmap n a l2) ∧
      Set.SurjOn (Pmap n a) (topData0 n 3 : Set (ZMod n → L)) (Ggrp n a 3))
    (hS7 : ∀ {L : Type} [Field L] [CharP L 3] [IsAlgClosed L],
      Nat.card ((fun g => tauG n a g / g) '' (Ggrp n a 3 : Set (ZMod n → L))) *
          Nat.card {g : ZMod n → L // g ∈ (Ggrp n a 3 : Set (ZMod n → L)) ∧ tauG n a g = g} =
        Nat.card (Ggrp n a 3 : Set (ZMod n → L)) ∧
      Nat.card {lam : ZMod n → L // (∀ k, lam (3 * k) = lam k ^ 3) ∧ (∀ k, lam k * lam (-k) = 1) ∧
        ∀ k, lam k * lam (k + half n) = lam (half n) * lam (2 * k)} = 4 * pairProd n 3) :
    (∀ σ : ℕ, σ ∣ n → Even σ → Nat.card (NFSet n σ) = 4 * pairProd n 3 ∧ (NFSet n σ).Nonempty) ∧
      (∀ σ : ℕ, σ ∣ n → Odd σ → NFSet n σ = ∅) ∧
      (n % 24 = 8 → ∀ σ : ℕ, σ ∣ n → XiaSet n σ ⊆ NFSet n σ) :=
  thm_A_of n a nodd hn ha hodd h3 (fun σ hσ he => prop_4_3_even_of n a nodd hn ha hodd h3 σ hσ he hS2 hS5 hS6 hS7)

/-! ## 5. Link checks: the rows as local hypotheses (statement text extracted verbatim from Statements.lean v0.71,
`Type*` → `Type`), and the link terms. These `example`s add no declarations. -/

section LinkCheck

set_option linter.unusedVariables false

example
  (row_thm_4_1_step2 : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (hω : IsPrimitiveRoot ω n),
    Nat.card (topData n 3 2 (1 : L) ω) = pairProd n 3 ∧ Nat.card (topData0 n 3 : Set (ZMod n → L)) = pairProd n 3 ∧
      (1 : ZMod n → L) ∈ (topData0 n 3 : Set (ZMod n → L)) ∧
      ∀ l1 ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ l2 ∈ (topData0 n 3 : Set (ZMod n → L)),
        l1 * l2 ∈ (topData0 n 3 : Set (ZMod n → L)) ∧ l1⁻¹ ∈ (topData0 n 3 : Set (ZMod n → L)))
  (row_thm_4_1_step5 : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (hω : IsPrimitiveRoot ω n),
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
          Nat.card {g : ZMod n → L // g ∈ G ∧ τ g = g}))
  (row_thm_4_1_step6 : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type} [Field L] [CharP L 3] [IsAlgClosed L],
    (∀ lam ∈ (topData0 n 3 : Set (ZMod n → L)), Pmap n a lam ∈ (Ggrp n a 3 : Set (ZMod n → L))) ∧
    (∀ l1 ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ l2 ∈ (topData0 n 3 : Set (ZMod n → L)),
      Pmap n a (l1 * l2) = Pmap n a l1 * Pmap n a l2) ∧
    Set.SurjOn (Pmap n a) (topData0 n 3 : Set (ZMod n → L)) (Ggrp n a 3))
  (row_thm_4_1_step7 : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type} [Field L] [CharP L 3] [IsAlgClosed L],
    Nat.card ((fun g => tauG n a g / g) '' (Ggrp n a 3 : Set (ZMod n → L))) *
        Nat.card {g : ZMod n → L // g ∈ (Ggrp n a 3 : Set (ZMod n → L)) ∧ tauG n a g = g} =
      Nat.card (Ggrp n a 3 : Set (ZMod n → L)) ∧
    Nat.card {lam : ZMod n → L // (∀ k, lam (3 * k) = lam k ^ 3) ∧ (∀ k, lam k * lam (-k) = 1) ∧
      ∀ k, lam k * lam (k + half n) = lam (half n) * lam (2 * k)} = 4 * pairProd n 3)
  (row_prop_2_4_bij : ∀ (n : ℕ) [NeZero n] (hn : Even n) (h3 : ¬ 3 ∣ n) {L : Type} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n),
    Set.BijOn (dftA ω) (NFSet n 2) {h | F1 3 2 ω h ∧ F3 ω h ∧ F4 h})
  (row_thm_4_1_count : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n),
    Nat.card (NFSet n 2) = 4 * pairProd n 3 ∧ (NFSet n 2).Nonempty ∧
      (Nat.card (NFSet n 2) : ℚ) = 4 * 3 ^ (n / 4) * ∏ P ∈ topPairs n 3, (1 - (3 : ℚ) ^ (-(pairLen P : ℤ))))
  (row_prop_4_3_even : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    (σ : ℕ) (hσ : σ ∣ n) (hσe : Even σ),
    Nat.card (NFSet n σ) = 4 * pairProd n 3) :
    ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n), Nat.card (NFSet n 2) = 4 * pairProd n 3 ∧ (NFSet n 2).Nonempty ∧
      (Nat.card (NFSet n 2) : ℚ) = 4 * 3 ^ (n / 4) * ∏ P ∈ topPairs n 3, (1 - (3 : ℚ) ^ (-(pairLen P : ℤ))) :=
  fun n a nodd _ hn ha hodd h3 => thm_4_1_count_of n a nodd hn ha hodd h3 (fun hev => row_prop_2_4_bij n hev h3)
    (row_thm_4_1_step2 n a nodd hn ha hodd h3) (row_thm_4_1_step5 n a nodd hn ha hodd h3)
    (row_thm_4_1_step6 n a nodd hn ha hodd h3) (row_thm_4_1_step7 n a nodd hn ha hodd h3)

example
  (row_thm_4_1_step2 : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (hω : IsPrimitiveRoot ω n),
    Nat.card (topData n 3 2 (1 : L) ω) = pairProd n 3 ∧ Nat.card (topData0 n 3 : Set (ZMod n → L)) = pairProd n 3 ∧
      (1 : ZMod n → L) ∈ (topData0 n 3 : Set (ZMod n → L)) ∧
      ∀ l1 ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ l2 ∈ (topData0 n 3 : Set (ZMod n → L)),
        l1 * l2 ∈ (topData0 n 3 : Set (ZMod n → L)) ∧ l1⁻¹ ∈ (topData0 n 3 : Set (ZMod n → L)))
  (row_thm_4_1_step5 : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (hω : IsPrimitiveRoot ω n),
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
          Nat.card {g : ZMod n → L // g ∈ G ∧ τ g = g}))
  (row_thm_4_1_step6 : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type} [Field L] [CharP L 3] [IsAlgClosed L],
    (∀ lam ∈ (topData0 n 3 : Set (ZMod n → L)), Pmap n a lam ∈ (Ggrp n a 3 : Set (ZMod n → L))) ∧
    (∀ l1 ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ l2 ∈ (topData0 n 3 : Set (ZMod n → L)),
      Pmap n a (l1 * l2) = Pmap n a l1 * Pmap n a l2) ∧
    Set.SurjOn (Pmap n a) (topData0 n 3 : Set (ZMod n → L)) (Ggrp n a 3))
  (row_thm_4_1_step7 : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type} [Field L] [CharP L 3] [IsAlgClosed L],
    Nat.card ((fun g => tauG n a g / g) '' (Ggrp n a 3 : Set (ZMod n → L))) *
        Nat.card {g : ZMod n → L // g ∈ (Ggrp n a 3 : Set (ZMod n → L)) ∧ tauG n a g = g} =
      Nat.card (Ggrp n a 3 : Set (ZMod n → L)) ∧
    Nat.card {lam : ZMod n → L // (∀ k, lam (3 * k) = lam k ^ 3) ∧ (∀ k, lam k * lam (-k) = 1) ∧
      ∀ k, lam k * lam (k + half n) = lam (half n) * lam (2 * k)} = 4 * pairProd n 3)
  (row_prop_2_4_bij : ∀ (n : ℕ) [NeZero n] (hn : Even n) (h3 : ¬ 3 ∣ n) {L : Type} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n),
    Set.BijOn (dftA ω) (NFSet n 2) {h | F1 3 2 ω h ∧ F3 ω h ∧ F4 h})
  (row_thm_4_1_count : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n),
    Nat.card (NFSet n 2) = 4 * pairProd n 3 ∧ (NFSet n 2).Nonempty ∧
      (Nat.card (NFSet n 2) : ℚ) = 4 * 3 ^ (n / 4) * ∏ P ∈ topPairs n 3, (1 - (3 : ℚ) ^ (-(pairLen P : ℤ))))
  (row_prop_4_3_even : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    (σ : ℕ) (hσ : σ ∣ n) (hσe : Even σ),
    Nat.card (NFSet n σ) = 4 * pairProd n 3) :
    ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n), Nat.card (NFSet n 2) = 4 * pairProd n 3 ∧ (NFSet n 2).Nonempty ∧
      (Nat.card (NFSet n 2) : ℚ) = 4 * 3 ^ (n / 4) * ∏ P ∈ topPairs n 3, (1 - (3 : ℚ) ^ (-(pairLen P : ℤ))) :=
  fun n a nodd _ hn ha hodd h3 => thm_4_1_count_of_steps n a nodd hn ha hodd h3
    (row_thm_4_1_step2 n a nodd hn ha hodd h3) (row_thm_4_1_step5 n a nodd hn ha hodd h3)
    (row_thm_4_1_step6 n a nodd hn ha hodd h3) (row_thm_4_1_step7 n a nodd hn ha hodd h3)

example
  (row_thm_4_1_step2 : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (hω : IsPrimitiveRoot ω n),
    Nat.card (topData n 3 2 (1 : L) ω) = pairProd n 3 ∧ Nat.card (topData0 n 3 : Set (ZMod n → L)) = pairProd n 3 ∧
      (1 : ZMod n → L) ∈ (topData0 n 3 : Set (ZMod n → L)) ∧
      ∀ l1 ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ l2 ∈ (topData0 n 3 : Set (ZMod n → L)),
        l1 * l2 ∈ (topData0 n 3 : Set (ZMod n → L)) ∧ l1⁻¹ ∈ (topData0 n 3 : Set (ZMod n → L)))
  (row_thm_4_1_step5 : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (hω : IsPrimitiveRoot ω n),
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
          Nat.card {g : ZMod n → L // g ∈ G ∧ τ g = g}))
  (row_thm_4_1_step6 : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type} [Field L] [CharP L 3] [IsAlgClosed L],
    (∀ lam ∈ (topData0 n 3 : Set (ZMod n → L)), Pmap n a lam ∈ (Ggrp n a 3 : Set (ZMod n → L))) ∧
    (∀ l1 ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ l2 ∈ (topData0 n 3 : Set (ZMod n → L)),
      Pmap n a (l1 * l2) = Pmap n a l1 * Pmap n a l2) ∧
    Set.SurjOn (Pmap n a) (topData0 n 3 : Set (ZMod n → L)) (Ggrp n a 3))
  (row_thm_4_1_step7 : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type} [Field L] [CharP L 3] [IsAlgClosed L],
    Nat.card ((fun g => tauG n a g / g) '' (Ggrp n a 3 : Set (ZMod n → L))) *
        Nat.card {g : ZMod n → L // g ∈ (Ggrp n a 3 : Set (ZMod n → L)) ∧ tauG n a g = g} =
      Nat.card (Ggrp n a 3 : Set (ZMod n → L)) ∧
    Nat.card {lam : ZMod n → L // (∀ k, lam (3 * k) = lam k ^ 3) ∧ (∀ k, lam k * lam (-k) = 1) ∧
      ∀ k, lam k * lam (k + half n) = lam (half n) * lam (2 * k)} = 4 * pairProd n 3)
  (row_prop_2_4_bij : ∀ (n : ℕ) [NeZero n] (hn : Even n) (h3 : ¬ 3 ∣ n) {L : Type} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n),
    Set.BijOn (dftA ω) (NFSet n 2) {h | F1 3 2 ω h ∧ F3 ω h ∧ F4 h})
  (row_thm_4_1_count : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n),
    Nat.card (NFSet n 2) = 4 * pairProd n 3 ∧ (NFSet n 2).Nonempty ∧
      (Nat.card (NFSet n 2) : ℚ) = 4 * 3 ^ (n / 4) * ∏ P ∈ topPairs n 3, (1 - (3 : ℚ) ^ (-(pairLen P : ℤ))))
  (row_prop_4_3_even : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    (σ : ℕ) (hσ : σ ∣ n) (hσe : Even σ),
    Nat.card (NFSet n σ) = 4 * pairProd n 3) :
    ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    (σ : ℕ) (hσ : σ ∣ n) (hσe : Even σ), Nat.card (NFSet n σ) = 4 * pairProd n 3 :=
  fun n a nodd _ hn ha hodd h3 σ hσ hσe => prop_4_3_even_of n a nodd hn ha hodd h3 σ hσ hσe
    (row_thm_4_1_step2 n a nodd hn ha hodd h3) (row_thm_4_1_step5 n a nodd hn ha hodd h3)
    (row_thm_4_1_step6 n a nodd hn ha hodd h3) (row_thm_4_1_step7 n a nodd hn ha hodd h3)

example
  (row_thm_4_1_step2 : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (hω : IsPrimitiveRoot ω n),
    Nat.card (topData n 3 2 (1 : L) ω) = pairProd n 3 ∧ Nat.card (topData0 n 3 : Set (ZMod n → L)) = pairProd n 3 ∧
      (1 : ZMod n → L) ∈ (topData0 n 3 : Set (ZMod n → L)) ∧
      ∀ l1 ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ l2 ∈ (topData0 n 3 : Set (ZMod n → L)),
        l1 * l2 ∈ (topData0 n 3 : Set (ZMod n → L)) ∧ l1⁻¹ ∈ (topData0 n 3 : Set (ZMod n → L)))
  (row_thm_4_1_step5 : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (hω : IsPrimitiveRoot ω n),
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
          Nat.card {g : ZMod n → L // g ∈ G ∧ τ g = g}))
  (row_thm_4_1_step6 : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type} [Field L] [CharP L 3] [IsAlgClosed L],
    (∀ lam ∈ (topData0 n 3 : Set (ZMod n → L)), Pmap n a lam ∈ (Ggrp n a 3 : Set (ZMod n → L))) ∧
    (∀ l1 ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ l2 ∈ (topData0 n 3 : Set (ZMod n → L)),
      Pmap n a (l1 * l2) = Pmap n a l1 * Pmap n a l2) ∧
    Set.SurjOn (Pmap n a) (topData0 n 3 : Set (ZMod n → L)) (Ggrp n a 3))
  (row_thm_4_1_step7 : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type} [Field L] [CharP L 3] [IsAlgClosed L],
    Nat.card ((fun g => tauG n a g / g) '' (Ggrp n a 3 : Set (ZMod n → L))) *
        Nat.card {g : ZMod n → L // g ∈ (Ggrp n a 3 : Set (ZMod n → L)) ∧ tauG n a g = g} =
      Nat.card (Ggrp n a 3 : Set (ZMod n → L)) ∧
    Nat.card {lam : ZMod n → L // (∀ k, lam (3 * k) = lam k ^ 3) ∧ (∀ k, lam k * lam (-k) = 1) ∧
      ∀ k, lam k * lam (k + half n) = lam (half n) * lam (2 * k)} = 4 * pairProd n 3)
  (row_prop_2_4_bij : ∀ (n : ℕ) [NeZero n] (hn : Even n) (h3 : ¬ 3 ∣ n) {L : Type} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n),
    Set.BijOn (dftA ω) (NFSet n 2) {h | F1 3 2 ω h ∧ F3 ω h ∧ F4 h})
  (row_thm_4_1_count : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n),
    Nat.card (NFSet n 2) = 4 * pairProd n 3 ∧ (NFSet n 2).Nonempty ∧
      (Nat.card (NFSet n 2) : ℚ) = 4 * 3 ^ (n / 4) * ∏ P ∈ topPairs n 3, (1 - (3 : ℚ) ^ (-(pairLen P : ℤ))))
  (row_prop_4_3_even : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    (σ : ℕ) (hσ : σ ∣ n) (hσe : Even σ),
    Nat.card (NFSet n σ) = 4 * pairProd n 3) :
    ∀ (n : ℕ) [NeZero n] (hn : n % 24 = 8), ((XiaSet n 2).Nonempty ↔ ∃ y ∈ NFSet n 2, Nm n (y 0) = -1 ∧ Nm n (y 1) = -1) ∧ (NFSet n 2).Nonempty :=
  fun n _ hn => cor_4_2_of n hn (fun a nodd h1 h2 h4 h5 => row_thm_4_1_count n a nodd h1 h2 h4 h5)

example
  (row_thm_4_1_step2 : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (hω : IsPrimitiveRoot ω n),
    Nat.card (topData n 3 2 (1 : L) ω) = pairProd n 3 ∧ Nat.card (topData0 n 3 : Set (ZMod n → L)) = pairProd n 3 ∧
      (1 : ZMod n → L) ∈ (topData0 n 3 : Set (ZMod n → L)) ∧
      ∀ l1 ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ l2 ∈ (topData0 n 3 : Set (ZMod n → L)),
        l1 * l2 ∈ (topData0 n 3 : Set (ZMod n → L)) ∧ l1⁻¹ ∈ (topData0 n 3 : Set (ZMod n → L)))
  (row_thm_4_1_step5 : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (hω : IsPrimitiveRoot ω n),
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
          Nat.card {g : ZMod n → L // g ∈ G ∧ τ g = g}))
  (row_thm_4_1_step6 : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type} [Field L] [CharP L 3] [IsAlgClosed L],
    (∀ lam ∈ (topData0 n 3 : Set (ZMod n → L)), Pmap n a lam ∈ (Ggrp n a 3 : Set (ZMod n → L))) ∧
    (∀ l1 ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ l2 ∈ (topData0 n 3 : Set (ZMod n → L)),
      Pmap n a (l1 * l2) = Pmap n a l1 * Pmap n a l2) ∧
    Set.SurjOn (Pmap n a) (topData0 n 3 : Set (ZMod n → L)) (Ggrp n a 3))
  (row_thm_4_1_step7 : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type} [Field L] [CharP L 3] [IsAlgClosed L],
    Nat.card ((fun g => tauG n a g / g) '' (Ggrp n a 3 : Set (ZMod n → L))) *
        Nat.card {g : ZMod n → L // g ∈ (Ggrp n a 3 : Set (ZMod n → L)) ∧ tauG n a g = g} =
      Nat.card (Ggrp n a 3 : Set (ZMod n → L)) ∧
    Nat.card {lam : ZMod n → L // (∀ k, lam (3 * k) = lam k ^ 3) ∧ (∀ k, lam k * lam (-k) = 1) ∧
      ∀ k, lam k * lam (k + half n) = lam (half n) * lam (2 * k)} = 4 * pairProd n 3)
  (row_prop_2_4_bij : ∀ (n : ℕ) [NeZero n] (hn : Even n) (h3 : ¬ 3 ∣ n) {L : Type} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n),
    Set.BijOn (dftA ω) (NFSet n 2) {h | F1 3 2 ω h ∧ F3 ω h ∧ F4 h})
  (row_thm_4_1_count : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n),
    Nat.card (NFSet n 2) = 4 * pairProd n 3 ∧ (NFSet n 2).Nonempty ∧
      (Nat.card (NFSet n 2) : ℚ) = 4 * 3 ^ (n / 4) * ∏ P ∈ topPairs n 3, (1 - (3 : ℚ) ^ (-(pairLen P : ℤ))))
  (row_prop_4_3_even : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    (σ : ℕ) (hσ : σ ∣ n) (hσe : Even σ),
    Nat.card (NFSet n σ) = 4 * pairProd n 3) :
    ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n), (∀ σ : ℕ, σ ∣ n → Even σ → Nat.card (NFSet n σ) = 4 * pairProd n 3 ∧ (NFSet n σ).Nonempty) ∧
      (∀ σ : ℕ, σ ∣ n → Odd σ → NFSet n σ = ∅) ∧
      (n % 24 = 8 → ∀ σ : ℕ, σ ∣ n → XiaSet n σ ⊆ NFSet n σ) :=
  fun n a nodd _ hn ha hodd h3 => thm_A_of n a nodd hn ha hodd h3
    (fun σ hσ he => row_prop_4_3_even n a nodd hn ha hodd h3 σ hσ he)

example
  (row_thm_4_1_step2 : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (hω : IsPrimitiveRoot ω n),
    Nat.card (topData n 3 2 (1 : L) ω) = pairProd n 3 ∧ Nat.card (topData0 n 3 : Set (ZMod n → L)) = pairProd n 3 ∧
      (1 : ZMod n → L) ∈ (topData0 n 3 : Set (ZMod n → L)) ∧
      ∀ l1 ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ l2 ∈ (topData0 n 3 : Set (ZMod n → L)),
        l1 * l2 ∈ (topData0 n 3 : Set (ZMod n → L)) ∧ l1⁻¹ ∈ (topData0 n 3 : Set (ZMod n → L)))
  (row_thm_4_1_step5 : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (hω : IsPrimitiveRoot ω n),
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
          Nat.card {g : ZMod n → L // g ∈ G ∧ τ g = g}))
  (row_thm_4_1_step6 : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type} [Field L] [CharP L 3] [IsAlgClosed L],
    (∀ lam ∈ (topData0 n 3 : Set (ZMod n → L)), Pmap n a lam ∈ (Ggrp n a 3 : Set (ZMod n → L))) ∧
    (∀ l1 ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ l2 ∈ (topData0 n 3 : Set (ZMod n → L)),
      Pmap n a (l1 * l2) = Pmap n a l1 * Pmap n a l2) ∧
    Set.SurjOn (Pmap n a) (topData0 n 3 : Set (ZMod n → L)) (Ggrp n a 3))
  (row_thm_4_1_step7 : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type} [Field L] [CharP L 3] [IsAlgClosed L],
    Nat.card ((fun g => tauG n a g / g) '' (Ggrp n a 3 : Set (ZMod n → L))) *
        Nat.card {g : ZMod n → L // g ∈ (Ggrp n a 3 : Set (ZMod n → L)) ∧ tauG n a g = g} =
      Nat.card (Ggrp n a 3 : Set (ZMod n → L)) ∧
    Nat.card {lam : ZMod n → L // (∀ k, lam (3 * k) = lam k ^ 3) ∧ (∀ k, lam k * lam (-k) = 1) ∧
      ∀ k, lam k * lam (k + half n) = lam (half n) * lam (2 * k)} = 4 * pairProd n 3)
  (row_prop_2_4_bij : ∀ (n : ℕ) [NeZero n] (hn : Even n) (h3 : ¬ 3 ∣ n) {L : Type} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n),
    Set.BijOn (dftA ω) (NFSet n 2) {h | F1 3 2 ω h ∧ F3 ω h ∧ F4 h})
  (row_thm_4_1_count : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n),
    Nat.card (NFSet n 2) = 4 * pairProd n 3 ∧ (NFSet n 2).Nonempty ∧
      (Nat.card (NFSet n 2) : ℚ) = 4 * 3 ^ (n / 4) * ∏ P ∈ topPairs n 3, (1 - (3 : ℚ) ^ (-(pairLen P : ℤ))))
  (row_prop_4_3_even : ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    (σ : ℕ) (hσ : σ ∣ n) (hσe : Even σ),
    Nat.card (NFSet n σ) = 4 * pairProd n 3) :
    ∀ (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n), (∀ σ : ℕ, σ ∣ n → Even σ → Nat.card (NFSet n σ) = 4 * pairProd n 3 ∧ (NFSet n σ).Nonempty) ∧
      (∀ σ : ℕ, σ ∣ n → Odd σ → NFSet n σ = ∅) ∧
      (n % 24 = 8 → ∀ σ : ℕ, σ ∣ n → XiaSet n σ ⊆ NFSet n σ) :=
  fun n a nodd _ hn ha hodd h3 => thm_A_of_steps n a nodd hn ha hodd h3
    (row_thm_4_1_step2 n a nodd hn ha hodd h3) (row_thm_4_1_step5 n a nodd hn ha hodd h3)
    (row_thm_4_1_step6 n a nodd hn ha hodd h3) (row_thm_4_1_step7 n a nodd hn ha hodd h3)

end LinkCheck

end Xia.Proofs

#print axioms Xia.Proofs.thm_4_1_count_of
#print axioms Xia.Proofs.thm_4_1_count_of_steps
#print axioms Xia.Proofs.cor_4_2_of
#print axioms Xia.Proofs.prop_4_3_even_of
#print axioms Xia.Proofs.thm_A_of
#print axioms Xia.Proofs.thm_A_of_steps
