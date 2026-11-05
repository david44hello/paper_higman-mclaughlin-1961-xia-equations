/- Xia/Proofs/Thm64.lean — proofs of the rows thm_6_4_step3b, prop_6_6_ii, thm_6_4_step2, thm_6_4_step45, thm_6_4_ii, cor_6_5_solvable of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import Xia.Defs.Layer0
import Xia.Proofs.Coverage
import Xia.Proofs.Combinatorics
import Xia.Proofs.Signs

namespace Xia.Proofs

open Xia Finset

set_option linter.unusedSectionVars false

/-! ## Arithmetic on `ℤ/n`, `n = 2^a n_odd`: divisibility of representatives by powers of 2 -/

section Arith

variable {n : ℕ} [NeZero n]

theorem H15_dvd_cast {j : ℕ} (hj : 2 ^ j ∣ n) (x : ZMod n) :
    2 ^ j ∣ x.val ↔ ZMod.castHom hj (ZMod (2 ^ j)) x = 0 := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]

theorem H15_dvd_mul_odd {j : ℕ} (hj : 2 ^ j ∣ n) {r : ℕ} (hr : Odd r) (x : ZMod n) :
    2 ^ j ∣ ((r : ZMod n) * x).val ↔ 2 ^ j ∣ x.val := by
  rw [H15_dvd_cast hj, H15_dvd_cast hj, map_mul, map_natCast]
  have hu : IsUnit (r : ZMod (2 ^ j)) :=
    (ZMod.isUnit_iff_coprime r (2 ^ j)).mpr (Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hr))
  exact hu.mul_right_eq_zero

theorem H15_dvd_neg {j : ℕ} (hj : 2 ^ j ∣ n) (x : ZMod n) : 2 ^ j ∣ (-x).val ↔ 2 ^ j ∣ x.val := by
  rw [H15_dvd_cast hj, H15_dvd_cast hj, map_neg, neg_eq_zero]

theorem H15_dvd_add_half {j : ℕ} (hj : 2 ^ j ∣ n) (hj2 : 2 ^ j ∣ n / 2) (x : ZMod n) :
    2 ^ j ∣ (x + half n).val ↔ 2 ^ j ∣ x.val := by
  rw [H15_dvd_cast hj, H15_dvd_cast hj, map_add]
  have : ZMod.castHom hj (ZMod (2 ^ j)) (half n) = 0 := by
    unfold half
    rw [map_natCast, ZMod.natCast_eq_zero_iff]
    exact hj2
  rw [this, add_zero]

theorem H15_dvd_two_mul {j : ℕ} (hj : 2 ^ (j + 1) ∣ n) (x : ZMod n) :
    2 ^ (j + 1) ∣ (2 * x).val ↔ 2 ^ j ∣ x.val := by
  rw [two_mul, ZMod.val_add, Nat.dvd_mod_iff hj, ← two_mul, pow_succ', Nat.mul_dvd_mul_iff_left (by norm_num)]

theorem H15_half_ne_zero (h2 : 2 ≤ n) : (half n : ZMod n) ≠ 0 := by
  intro h
  have := congrArg ZMod.val h
  rw [H7_half_val, ZMod.val_zero] at this
  omega

theorem H15_two_mul_eq_zero (hev : Even n) (x : ZMod n) : 2 * x = 0 ↔ x = 0 ∨ x = half n := by
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    rw [two_mul, ZMod.val_add, ZMod.val_zero] at hv
    have hlt := ZMod.val_lt x
    have h2 : n % 2 = 0 := Nat.even_iff.mp hev
    obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hv
    have hc2 : c < 2 := by
      by_contra hcon
      have := Nat.mul_le_mul_left n (not_lt.mp hcon)
      omega
    interval_cases c
    · left
      exact (ZMod.val_eq_zero x).mp (by omega)
    · right
      apply ZMod.val_injective
      rw [H7_half_val]
      omega
  · rintro (rfl | rfl)
    · ring
    · rw [two_mul, H7_two_half hev]

theorem H15_vk_iff {x : ℕ} (hx : x ≠ 0) (v : ℕ) :
    padicValNat 2 x = v ↔ 2 ^ v ∣ x ∧ ¬ 2 ^ (v + 1) ∣ x := by
  rw [padicValNat_dvd_iff_le hx, padicValNat_dvd_iff_le hx]
  omega

theorem H15_vk_transfer {x y : ℕ} (J : ℕ) (hT : ∀ j ≤ J, 2 ^ j ∣ y ↔ 2 ^ j ∣ x) (hx : x ≠ 0)
    (hv : padicValNat 2 x < J) : y ≠ 0 ∧ padicValNat 2 y = padicValNat 2 x := by
  have h1 := (H15_vk_iff hx (padicValNat 2 x)).mp rfl
  have hy1 : 2 ^ padicValNat 2 x ∣ y := (hT _ hv.le).mpr h1.1
  have hy2 : ¬ 2 ^ (padicValNat 2 x + 1) ∣ y := fun h => h1.2 ((hT _ hv).mp h)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy2 (dvd_zero _)
  exact ⟨hy0, (H15_vk_iff hy0 _).mpr ⟨hy1, hy2⟩⟩

theorem H15_vk_lt {a x : ℕ} (hx : ¬ 2 ^ a ∣ x) : x ≠ 0 ∧ padicValNat 2 x < a := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (dvd_zero _)
  refine ⟨hx0, ?_⟩
  by_contra h
  exact hx ((padicValNat_dvd_iff_le hx0).mpr (not_lt.mp h))

theorem H15_pow_sub_one {a : ℕ} (ha : 1 ≤ a) : 2 ^ a = 2 * 2 ^ (a - 1) := by
  rw [← pow_succ']
  congr 1
  omega

theorem H15_half_eq {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) : n / 2 = 2 ^ (a - 1) * nodd := by
  rw [hn, H15_pow_sub_one ha, mul_assoc]
  exact Nat.mul_div_cancel_left _ two_pos

theorem H15_dvd_n {a nodd j : ℕ} (hn : n = 2 ^ a * nodd) (hj : j ≤ a) : 2 ^ j ∣ n := by
  rw [hn]
  exact Dvd.dvd.mul_right (pow_dvd_pow 2 hj) _

theorem H15_dvd_half {a nodd j : ℕ} (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) (hj : j ≤ a - 1) : 2 ^ j ∣ n / 2 := by
  rw [H15_half_eq hn ha]
  exact Dvd.dvd.mul_right (pow_dvd_pow 2 hj) _

theorem H15_not_dvd_half {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) (hodd : Odd nodd) :
    ¬ 2 ^ a ∣ n / 2 := by
  rw [H15_half_eq hn ha, H15_pow_sub_one ha]
  intro h
  rw [mul_comm 2] at h
  exact (Nat.not_even_iff_odd.mpr hodd)
    (even_iff_two_dvd.mpr ((Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero (by positivity))).mp h))

theorem H15_odd_transfer {x y : ℕ} (hT : 2 ^ 1 ∣ y ↔ 2 ^ 1 ∣ x) (hx : Odd x) : Odd y := by
  have hT' : 2 ∣ y ↔ 2 ∣ x := by simpa using hT
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd, hT', ← even_iff_two_dvd, Nat.not_even_iff_odd]
  exact hx

/-- `x ∈ μ_{n_odd}` (`2^a ∣ x`) ⇒ `x + n/2 ∉ μ_{n_odd}`. -/
theorem H15_L0_add_half {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) (hodd : Odd nodd) (x : ZMod n)
    (hx : 2 ^ a ∣ x.val) : ¬ 2 ^ a ∣ (x + half n).val := by
  have hA := H15_dvd_n hn (le_refl a)
  intro h
  rw [H15_dvd_cast hA] at h hx
  rw [map_add, hx, zero_add] at h
  unfold half at h
  rw [map_natCast, ZMod.natCast_eq_zero_iff] at h
  exact H15_not_dvd_half hn ha hodd h

/-- `x` in layer 1 (`2^{a-1} ∣ x`, `2^a ∤ x`) ⇒ `x + n/2 ∈ μ_{n_odd}`. -/
theorem H15_add_half_L0 {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) (hodd : Odd nodd) (x : ZMod n)
    (h1 : 2 ^ (a - 1) ∣ x.val) (h2 : ¬ 2 ^ a ∣ x.val) : 2 ^ a ∣ (x + half n).val := by
  have hA := H15_dvd_n hn (le_refl a)
  rw [ZMod.val_add, H7_half_val, Nat.dvd_mod_iff hA, H15_half_eq hn ha]
  obtain ⟨w, hw⟩ := h1
  have hwodd : Odd w := by
    rw [← Nat.not_even_iff_odd]
    rintro ⟨u, rfl⟩
    apply h2
    rw [hw, H15_pow_sub_one ha]
    exact ⟨u, by ring⟩
  obtain ⟨u, hu⟩ := hwodd.add_odd hodd
  rw [hw, ← mul_add, hu, H15_pow_sub_one ha]
  exact ⟨u, by ring⟩

theorem H15_halve {a : ℕ} (x : ZMod n) (hx : ¬ 2 ^ a ∣ x.val) {v : ℕ} (hv : padicValNat 2 x.val = v + 1) :
    ∃ y : ZMod n, 2 * y = x ∧ ¬ 2 ^ a ∣ y.val ∧ padicValNat 2 y.val = v := by
  have hx0 : x.val ≠ 0 := fun h => hx (h ▸ dvd_zero _)
  have h2 : 2 ∣ x.val := by
    have := (padicValNat_dvd_iff_le hx0).mpr (show 1 ≤ padicValNat 2 x.val by omega)
    simpa using this
  obtain ⟨w, hw⟩ := h2
  have hwlt : w < n := by
    have := ZMod.val_lt x
    omega
  have hw0 : w ≠ 0 := by omega
  have hwv : (w : ZMod n).val = w := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hwlt]
  refine ⟨(w : ZMod n), ?_, ?_, ?_⟩
  · have := ZMod.natCast_zmod_val x
    rw [hw] at this
    push_cast at this
    exact this
  · rw [hwv]
    intro h
    apply hx
    rw [hw]
    exact Dvd.dvd.mul_left h 2
  · rw [hwv]
    rw [hw, padicValNat.mul (by norm_num) hw0, padicValNat.self (by norm_num)] at hv
    omega

end Arith

/-! ## The descent construction -/

section Descent

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

/-- `D_v(t)(k) := ∏_{ρ ∈ 𝓛_a, ρ^{2^v} = ξ} t(ρ)` (exponent model: `2^v ρ = k`). -/
noncomputable def H15_D (v : ℕ) (t : ZMod n → L) (k : ZMod n) : L :=
  ∏ ρ ∈ (topLayer n).filter (fun ρ => (2 ^ v : ZMod n) * ρ = k), t ρ

/-- The descended value on the layers `1..a-1` (and on the top layer): `s0^{-(2^v-1)} D_v(t)(k)`, `v = v_2(k)`. -/
noncomputable def H15_hmid (t : ZMod n → L) (s0 : L) (k : ZMod n) : L :=
  s0⁻¹ ^ (2 ^ padicValNat 2 k.val - 1) * H15_D (padicValNat 2 k.val) t k

/-- The full candidate `ŷ`: `f` on `μ_{n_odd} ∖ {1}`, `n` at `1`, the descent elsewhere. -/
noncomputable def H15_h (a : ℕ) (t : ZMod n → L) (s0 : L) (f : ZMod n → L) (e : L) (k : ZMod n) : L :=
  if 2 ^ a ∣ k.val then (if k = 0 then e else f k) else H15_hmid t s0 k

/-- `μ_{n_odd} ∖ {1}` as the `P` of Step 4: `s0^{-1} ŷ(-α)`. -/
noncomputable def H15_P (a : ℕ) (t : ZMod n → L) (s0 : L) (k : ZMod n) : L :=
  if k ∈ layer0' n a then s0⁻¹ * H15_hmid t s0 (k + half n) else 1

theorem H15_D_succ (hev : Even n) (h2 : 2 ≤ n) (v : ℕ) (t : ZMod n → L) (k : ZMod n) :
    H15_D (v + 1) t (2 * k) = H15_D v t k * H15_D v t (k + half n) := by
  unfold H15_D
  rw [← Finset.prod_union]
  · congr 1
    ext ρ
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hρ, he⟩
      have h0 : 2 * ((2 ^ v : ZMod n) * ρ - k) = 0 := by linear_combination he
      rcases (H15_two_mul_eq_zero hev _).mp h0 with h | h
      · exact Or.inl ⟨hρ, by linear_combination h⟩
      · exact Or.inr ⟨hρ, by linear_combination h⟩
    · rintro (⟨hρ, he⟩ | ⟨hρ, he⟩)
      · exact ⟨hρ, by linear_combination 2 * he⟩
      · exact ⟨hρ, by linear_combination 2 * he + H7_two_half hev⟩
  · rw [Finset.disjoint_filter]
    intro ρ _ h1 h2'
    apply H15_half_ne_zero h2
    linear_combination h1 - h2'

theorem H15_D_zero (t : ZMod n → L) {k : ZMod n} (hk : Odd k.val) : H15_D 0 t k = t k := by
  unfold H15_D
  have : (topLayer n).filter (fun ρ => (2 ^ 0 : ZMod n) * ρ = k) = {k} := by
    ext ρ
    simp only [Finset.mem_filter, Finset.mem_singleton, pow_zero, one_mul, topLayer, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, rfl⟩
      rfl
    · rintro rfl
      exact ⟨hk, rfl⟩
  rw [this, Finset.prod_singleton]

theorem H15_D_mul (v : ℕ) (t l : ZMod n → L) (k : ZMod n) :
    H15_D v (fun ρ => t ρ * l ρ) k = H15_D v t k * H15_D v l k := by
  unfold H15_D
  exact Finset.prod_mul_distrib

theorem H15_hmid_odd (t : ZMod n → L) (s0 : L) {k : ZMod n} (hk : Odd k.val) : H15_hmid t s0 k = t k := by
  unfold H15_hmid
  have hnd : ¬ 2 ∣ k.val := fun h => Nat.not_even_iff_odd.mpr hk (even_iff_two_dvd.mpr h)
  rw [padicValNat.eq_zero_of_not_dvd hnd, H15_D_zero t hk]
  simp

theorem H15_mem_layer0' {a : ℕ} (k : ZMod n) : k ∈ layer0' n a ↔ 2 ^ a ∣ k.val ∧ k ≠ 0 := by
  simp [layer0']

theorem H15_h_zero (a : ℕ) (t : ZMod n → L) (s0 : L) (f : ZMod n → L) (e : L) : H15_h a t s0 f e 0 = e := by
  unfold H15_h
  rw [ite_eq_left (by rw [ZMod.val_zero]; exact dvd_zero _), ite_eq_left rfl]

theorem H15_h_L0 {a : ℕ} (t : ZMod n → L) (s0 : L) (f : ZMod n → L) (e : L) {k : ZMod n} (hk : 2 ^ a ∣ k.val)
    (hk0 : k ≠ 0) : H15_h a t s0 f e k = f k := by
  unfold H15_h
  rw [ite_eq_left hk, ite_eq_right hk0]

theorem H15_h_mid {a : ℕ} (t : ZMod n → L) (s0 : L) (f : ZMod n → L) (e : L) {k : ZMod n} (hk : ¬ 2 ^ a ∣ k.val) :
    H15_h a t s0 f e k = H15_hmid t s0 k := by
  unfold H15_h
  rw [ite_eq_right hk]

/-- One descent step: for `v_2(x) ≤ a-2`, `ŷ(2x) = s0^{-1} ŷ(x) ŷ(x + n/2)` (and the layer bookkeeping). -/
theorem H15_hmid_two {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (t : ZMod n → L) (s0 : L)
    (x : ZMod n) (hx : ¬ 2 ^ a ∣ x.val) (hv : padicValNat 2 x.val + 2 ≤ a) :
    ¬ 2 ^ a ∣ (2 * x).val ∧ ¬ 2 ^ a ∣ (x + half n).val ∧
      padicValNat 2 (x + half n).val = padicValNat 2 x.val ∧
      H15_hmid t s0 (2 * x) = s0⁻¹ * H15_hmid t s0 x * H15_hmid t s0 (x + half n) := by
  have h8 : 2 ^ 3 ∣ n := H15_dvd_n hn ha
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h8)
  have h2n : 2 ≤ n := Nat.le_of_dvd (NeZero.pos n) (dvd_trans (by norm_num) h8)
  obtain ⟨hx0, -⟩ := H15_vk_lt hx
  have hxv := (H15_vk_iff hx0 (padicValNat 2 x.val)).mp rfl
  have hTm : ∀ j ≤ a - 1, 2 ^ j ∣ (x + half n).val ↔ 2 ^ j ∣ x.val := fun j hj =>
    H15_dvd_add_half (H15_dvd_n hn (by omega)) (H15_dvd_half hn (by omega) hj) x
  obtain ⟨-, hmv⟩ := H15_vk_transfer (a - 1) hTm hx0 (by omega)
  have h2a : 2 ^ (padicValNat 2 x.val + 1) ∣ (2 * x).val :=
    (H15_dvd_two_mul (H15_dvd_n hn (by omega)) x).mpr hxv.1
  have h2b : ¬ 2 ^ (padicValNat 2 x.val + 1 + 1) ∣ (2 * x).val := fun h =>
    hxv.2 ((H15_dvd_two_mul (H15_dvd_n hn (by omega)) x).mp h)
  have h20 : (2 * x).val ≠ 0 := by
    intro h
    rw [h] at h2b
    exact h2b (dvd_zero _)
  have h2v : padicValNat 2 (2 * x).val = padicValNat 2 x.val + 1 := (H15_vk_iff h20 _).mpr ⟨h2a, h2b⟩
  refine ⟨fun h => h2b (dvd_trans (pow_dvd_pow 2 (by omega)) h), fun h => ?_, hmv, ?_⟩
  · exact hxv.2 ((hTm (padicValNat 2 x.val + 1) (by omega)).mp (dvd_trans (pow_dvd_pow 2 (by omega)) h))
  · unfold H15_hmid
    have hp : ∀ w : ℕ, 2 ^ (w + 1) - 1 = 1 + (2 ^ w - 1) + (2 ^ w - 1) := by
      intro w
      have := Nat.one_le_two_pow (n := w)
      rw [pow_succ]
      omega
    rw [h2v, hmv, H15_D_succ hev h2n, hp, pow_add, pow_add, pow_one]
    ring

end Descent

/-! ## The laws of the descended values (layers `a, a-1, …, 1`) -/

section Laws

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

theorem H15_kappa_ne {r : ℕ} [Fact r.Prime] [CharP L r] (hr : ¬ r ∣ pp n * n) : kappa n L ≠ 0 := by
  have hp : r.Prime := Fact.out
  have hc : ((n ^ 2 * pp n : ℕ) : L) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff L r]
    intro hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
    · exact hr (dvd_mul_of_dvd_right (hp.dvd_of_dvd_pow h) _)
    · exact hr (dvd_mul_of_dvd_left h _)
  unfold kappa
  exact_mod_cast hc

theorem H15_n_ne {r : ℕ} [Fact r.Prime] [CharP L r] (hr : ¬ r ∣ pp n * n) : (n : L) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff L r]
  exact fun h => hr (dvd_mul_of_dvd_right h _)

theorem H15_r_odd {a nodd r : ℕ} [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hr : ¬ r ∣ pp n * n) :
    Odd r := by
  have hp : r.Prime := Fact.out
  have h2 : 2 ∣ n := dvd_trans (dvd_pow_self 2 (by omega)) (H15_dvd_n hn (le_refl a))
  refine hp.odd_of_ne_two ?_
  rintro rfl
  exact hr (dvd_mul_of_dvd_right h2 _)

theorem H15_vk_mul {a nodd r : ℕ} (hn : n = 2 ^ a * nodd) (hr : Odd r) (x : ZMod n) (hx : ¬ 2 ^ a ∣ x.val) :
    ¬ 2 ^ a ∣ ((r : ZMod n) * x).val ∧ padicValNat 2 ((r : ZMod n) * x).val = padicValNat 2 x.val := by
  obtain ⟨hx0, hxa⟩ := H15_vk_lt hx
  have hT : ∀ j ≤ a, 2 ^ j ∣ ((r : ZMod n) * x).val ↔ 2 ^ j ∣ x.val := fun j hj =>
    H15_dvd_mul_odd (H15_dvd_n hn hj) hr x
  exact ⟨fun h => hx ((hT a le_rfl).mp h), (H15_vk_transfer a hT hx0 hxa).2⟩

theorem H15_vk_neg {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (x : ZMod n) (hx : ¬ 2 ^ a ∣ x.val) :
    ¬ 2 ^ a ∣ (-x).val ∧ padicValNat 2 (-x).val = padicValNat 2 x.val := by
  obtain ⟨hx0, hxa⟩ := H15_vk_lt hx
  have hT : ∀ j ≤ a, 2 ^ j ∣ (-x).val ↔ 2 ^ j ∣ x.val := fun j hj => H15_dvd_neg (H15_dvd_n hn hj) x
  exact ⟨fun h => hx ((hT a le_rfl).mp h), (H15_vk_transfer a hT hx0 hxa).2⟩

/-- (F1_r) and (F3_r) on every layer above layer 0, by induction downwards (Step 3 for each step). -/
theorem H15_layers {a nodd r : ℕ} [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (hr : ¬ r ∣ pp n * n) (σr : ℤ) [CharP L r] (ω : L) (hω : IsPrimitiveRoot ω n)
    (t : ZMod n → L) (ht : t ∈ topData n r σr (kappa n L) ω) (s0 : L) (hS : s0 ^ 2 = kappa n L)
    (hsgn : (-1 : L) ^ σr.natAbs * s0 ^ (r - 1) = 1) :
    ∀ v : ℕ, ∀ x : ZMod n, ¬ 2 ^ a ∣ x.val → padicValNat 2 x.val = v →
      H15_hmid t s0 ((r : ZMod n) * x) = (ω ^ x.val) ^ ((r : ℤ) * σr) * H15_hmid t s0 x ^ r ∧
      H15_hmid t s0 x * H15_hmid t s0 (-x) = kappa n L * (ω ^ x.val) ^ (n / 2) := by
  have hrodd : Odd r := H15_r_odd hn ha hr
  have h2 : 2 ^ 1 ∣ n := H15_dvd_n hn (by omega)
  intro v
  induction v with
  | zero =>
    intro x hx hv
    have hx0 := (H15_vk_lt hx).1
    have hxo : Odd x.val := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      intro h2'
      have := (padicValNat_dvd_iff_le hx0).mp (by simpa using h2' : 2 ^ 1 ∣ x.val)
      omega
    have hrxo : Odd ((r : ZMod n) * x).val := H15_odd_transfer (H15_dvd_mul_odd h2 hrodd x) hxo
    have hnxo : Odd (-x).val := H15_odd_transfer (H15_dvd_neg h2 x) hxo
    rw [H15_hmid_odd t s0 hrxo, H15_hmid_odd t s0 hxo, H15_hmid_odd t s0 hnxo]
    exact ht.1 x hxo
  | succ v ih =>
    intro x hx hv
    obtain ⟨hx0, hxa⟩ := H15_vk_lt hx
    obtain ⟨y, rfl, hy, hyv⟩ := H15_halve x hx hv
    have hya : padicValNat 2 y.val + 2 ≤ a := by omega
    obtain ⟨-, hym, hymv, hdy⟩ := H15_hmid_two hn ha t s0 y hy hya
    have ihy := ih y hy hyv
    have ihym := ih (y + half n) hym (hymv.trans hyv)
    have hF1 : ∀ z ∈ ({y, y + half n} : Set (ZMod n)),
        H15_hmid t s0 ((r : ZMod n) * z) = (ω ^ z.val) ^ ((r : ℤ) * σr) * H15_hmid t s0 z ^ r := by
      intro z hz
      rcases hz with rfl | rfl
      · exact ihy.1
      · exact ihym.1
    have hF3 : ∀ z ∈ ({y, y + half n} : Set (ZMod n)),
        H15_hmid t s0 z * H15_hmid t s0 (-z) = kappa n L * (ω ^ z.val) ^ (n / 2) := by
      intro z hz
      rcases hz with rfl | rfl
      · exact ihy.2
      · exact ihym.2
    obtain ⟨s1, -, s3⟩ :=
      thm_6_4_step3_proved n a nodd r hn ha hodd hr σr ω hω (H15_hmid t s0) s0 hS y hF1 hF3
    obtain ⟨hry, hryv⟩ := H15_vk_mul hn hrodd y hy
    obtain ⟨-, -, -, hdry⟩ := H15_hmid_two hn ha t s0 ((r : ZMod n) * y) hry (by omega)
    obtain ⟨hny, hnyv⟩ := H15_vk_neg hn y hy
    obtain ⟨-, -, -, hdny⟩ := H15_hmid_two hn ha t s0 (-y) hny (by omega)
    constructor
    · rw [show (r : ZMod n) * (2 * y) = 2 * ((r : ZMod n) * y) by ring, hdry, s1, hdy, hsgn, one_mul]
    · rw [show -(2 * y) = 2 * (-y) by ring, hdy, hdny, s3]

/-- `ŷ(-1) = s0` for the descended values (via `n/4`: `ŷ(-1) = s0^{-1} ŷ(ι)ŷ(ι^{-1}) = s0^{-1} κ`). -/
theorem H15_hmid_half {a nodd r : ℕ} [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (hr : ¬ r ∣ pp n * n) (σr : ℤ) [CharP L r] (ω : L) (hω : IsPrimitiveRoot ω n)
    (t : ZMod n → L) (ht : t ∈ topData n r σr (kappa n L) ω) (s0 : L) (hS : s0 ^ 2 = kappa n L)
    (hsgn : (-1 : L) ^ σr.natAbs * s0 ^ (r - 1) = 1) :
    ¬ 2 ^ a ∣ (half n : ZMod n).val ∧ H15_hmid t s0 (half n) = s0 := by
  have h8 : 2 ^ 3 ∣ n := H15_dvd_n hn ha
  have h8' : 8 ∣ n := by simpa using h8
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h8)
  have hpos := NeZero.pos n
  have hκ : kappa n L ≠ 0 := H15_kappa_ne hr
  have hs0 : s0 ≠ 0 := by
    rintro rfl
    apply hκ
    rw [← hS]
    ring
  obtain ⟨q, hqdef⟩ : ∃ q : ZMod n, q = ((n / 4 : ℕ) : ZMod n) := ⟨_, rfl⟩
  have hqv : q.val = n / 4 := by rw [hqdef, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hn4 : n / 4 = 2 ^ (a - 2) * nodd := by
    rw [hn, show a = (a - 2) + 2 by omega, pow_add]
    simp only [show a - 2 + 2 - 2 = a - 2 by omega]
    rw [show 2 ^ (a - 2) * 2 ^ 2 * nodd = 4 * (2 ^ (a - 2) * nodd) by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  have hnodd0 : nodd ≠ 0 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) ⟨0, rfl⟩
  have hq0 : q.val ≠ 0 := by
    rw [hqv]
    omega
  have hqvk : padicValNat 2 q.val = a - 2 := by
    rw [hqv, hn4, padicValNat.mul (by positivity) hnodd0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (fun h => Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr h)), add_zero]
  have hqa : ¬ 2 ^ a ∣ q.val := by
    intro h
    have := (padicValNat_dvd_iff_le hq0).mp h
    omega
  have h2q : 2 * q = half n := by
    rw [hqdef]
    unfold half
    rw [show n / 2 = 2 * (n / 4) by omega]
    push_cast
    ring
  have hqm : q + half n = -q := by linear_combination h2q + H7_two_half hev
  obtain ⟨hma, -, -, hdq⟩ := H15_hmid_two hn ha t s0 q hqa (by omega)
  rw [h2q] at hma hdq
  refine ⟨hma, ?_⟩
  have hF3q := (H15_layers hn ha hodd hr σr ω hω t ht s0 hS hsgn (a - 2) q hqa hqvk).2
  have hω1 : (ω ^ q.val) ^ (n / 2) = 1 := by
    rw [hqv, ← pow_mul, mul_comm, pow_mul, H7_pow_half_eq_neg_one hev hω]
    exact Even.neg_one_pow ⟨n / 8, by omega⟩
  rw [hdq, hqm, mul_assoc, hF3q, hω1, mul_one, ← hS, pow_two, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]

end Laws

/-! ## One solution of the Fourier system -/

section Build

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

theorem H15_omega_add_half {ω : L} (hev : Even n) (hω : IsPrimitiveRoot ω n) (x : ZMod n) :
    ω ^ (x + half n).val = -ω ^ x.val := by
  rw [H7_pow_val_add ω hω.pow_eq_one, H7_half_val, H7_pow_half_eq_neg_one hev hω]
  ring

theorem H15_unit_r {r : ℕ} [Fact r.Prime] (hr : ¬ r ∣ pp n * n) : IsUnit (r : ZMod n) := by
  have hp : r.Prime := Fact.out
  rw [ZMod.isUnit_iff_coprime]
  exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => hr (dvd_mul_of_dvd_right h _))

theorem H15_natCast_pow_r {r : ℕ} [Fact r.Prime] [CharP L r] (m : ℕ) : (m : L) ^ r = m := by
  have e := ZMod.pow_card (m : ZMod r)
  have e2 := congrArg (ZMod.castHom (dvd_refl r) L) e
  simpa only [map_pow, map_natCast] using e2

/-- The sign condition `(-1)^σ s0^{r-1} = 1` for any `s0` with `s0^2 = κ` (Step 3: Euler's criterion), given
`(-1)^σ = (p/r)` and one top datum (used only to call Step 3 at `x = 1`). -/
theorem H15_sgn {a nodd r : ℕ} [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (hr : ¬ r ∣ pp n * n) (σr : ℤ) (hsign : (-1 : ℤ) ^ σr.natAbs = legendreSym r (pp n : ℤ))
    [CharP L r] (ω : L) (hω : IsPrimitiveRoot ω n) (t0 : ZMod n → L) (ht0 : t0 ∈ topData n r σr (kappa n L) ω)
    (s0 : L) (hS : s0 ^ 2 = kappa n L) : (-1 : L) ^ σr.natAbs * s0 ^ (r - 1) = 1 := by
  have h8 : 2 ^ 3 ∣ n := H15_dvd_n hn ha
  have h8' : 8 ∣ n := by simpa using h8
  have hone : Odd (1 : ZMod n).val := by
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by have := Nat.le_of_dvd (NeZero.pos n) h8'; omega)]
    exact odd_one
  have hone' : Odd ((1 : ZMod n) + half n).val :=
    H15_odd_transfer (H15_dvd_add_half (H15_dvd_n hn (by omega)) (H15_dvd_half hn (by omega) (by omega)) 1) hone
  have hF1t : ∀ z ∈ ({1, 1 + half n} : Set (ZMod n)),
      t0 ((r : ZMod n) * z) = (ω ^ z.val) ^ ((r : ℤ) * σr) * t0 z ^ r := by
    intro z hz
    rcases hz with rfl | rfl
    · exact (ht0.1 _ hone).1
    · exact (ht0.1 _ hone').1
  have hF3t : ∀ z ∈ ({1, 1 + half n} : Set (ZMod n)), t0 z * t0 (-z) = kappa n L * (ω ^ z.val) ^ (n / 2) := by
    intro z hz
    rcases hz with rfl | rfl
    · exact (ht0.1 _ hone).2
    · exact (ht0.1 _ hone').2
  obtain ⟨-, hleg, -⟩ := thm_6_4_step3_proved n a nodd r hn ha hodd hr σr ω hω t0 s0 hS 1 hF1t hF3t
  have hc : ((-1 : L)) ^ σr.natAbs = ((legendreSym r (pp n : ℤ) : ℤ) : L) := by
    rw [← hsign]
    simp
  rw [hleg, ← hc, ← mul_pow, neg_one_mul, neg_neg, one_pow]

/-- The candidate `ŷ` satisfies (F1_r), (F3_r), (F4_r), given top data `t`, `s0^2 = κ`, the sign condition, and
`f ∈ G'` with (E1) `f(α^2) = P(α) f(α)`. -/
theorem H15_build {a nodd r : ℕ} [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (hr : ¬ r ∣ pp n * n) (σr : ℤ) [CharP L r] (ω : L) (hω : IsPrimitiveRoot ω n)
    (t : ZMod n → L) (ht : t ∈ topData n r σr (kappa n L) ω) (s0 : L) (hS : s0 ^ 2 = kappa n L)
    (hsgn : (-1 : L) ^ σr.natAbs * s0 ^ (r - 1) = 1) (f : ZMod n → L) (hf : f ∈ Gprime n a r σr (kappa n L) ω)
    (hE1 : ∀ α ∈ layer0' n a, f (2 * α) = s0⁻¹ * H15_hmid t s0 (α + half n) * f α)
    (e : L) (he2 : e ^ 2 = (n : L) ^ 2) (her : e ^ r = e) :
    F1 r σr ω (H15_h a t s0 f e) ∧ F3r (kappa n L) ω (H15_h a t s0 f e) ∧ F4 (H15_h a t s0 f e) := by
  have hp : r.Prime := Fact.out
  have hrodd : Odd r := H15_r_odd hn ha hr
  have h8 : 2 ^ 3 ∣ n := H15_dvd_n hn ha
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h8)
  have hA : 2 ^ a ∣ n := H15_dvd_n hn le_rfl
  have hκ : kappa n L ≠ 0 := H15_kappa_ne hr
  have hω0 : ω ≠ 0 := hω.ne_zero (NeZero.ne n)
  have hs0 : s0 ≠ 0 := by
    rintro rfl
    apply hκ
    rw [← hS]
    ring
  have hlay := H15_layers hn ha hodd hr σr ω hω t ht s0 hS hsgn
  obtain ⟨hma, hhalf⟩ := H15_hmid_half hn ha hodd hr σr ω hω t ht s0 hS hsgn
  have hu := H15_unit_r hr
  set h := H15_h a t s0 f e with hdef
  have hhm : h (half n) = s0 := by rw [hdef, H15_h_mid t s0 f e hma, hhalf]
  -- F4 at points of layer 0
  have hF4L0 : ∀ α : ZMod n, 2 ^ a ∣ α.val → h α * h (α + half n) = h (half n) * h (2 * α) := by
    intro α hα
    by_cases hα0 : α = 0
    · subst hα0
      rw [mul_zero, zero_add, mul_comm]
    · have hαm := H15_L0_add_half hn (by omega) hodd α hα
      have hαl : α ∈ layer0' n a := (H15_mem_layer0' α).mpr ⟨hα, hα0⟩
      have h2α : 2 ^ a ∣ (2 * α).val := by
        rw [H15_dvd_cast hA] at hα ⊢
        rw [map_mul, hα, mul_zero]
      have h2α0 : 2 * α ≠ 0 := by
        intro h0
        rcases (H15_two_mul_eq_zero hev α).mp h0 with h1 | h1
        · exact hα0 h1
        · exact hma (h1 ▸ hα)
      rw [hhm, hdef, H15_h_L0 t s0 f e hα hα0, H15_h_mid t s0 f e hαm, H15_h_L0 t s0 f e h2α h2α0, hE1 α hαl]
      linear_combination (-(H15_hmid t s0 (α + half n) * f α)) * mul_inv_cancel₀ hs0
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · -- F1
    intro k
    by_cases hk : 2 ^ a ∣ k.val
    · by_cases hk0 : k = 0
      · subst hk0
        rw [mul_zero, hdef, H15_h_zero, ZMod.val_zero, pow_zero, one_zpow, one_mul, her]
      · have hrk : 2 ^ a ∣ ((r : ZMod n) * k).val := (H15_dvd_mul_odd hA hrodd k).mpr hk
        have hrk0 : (r : ZMod n) * k ≠ 0 := fun h0 => hk0 ((hu.mul_right_eq_zero).mp h0)
        rw [hdef, H15_h_L0 t s0 f e hrk hrk0, H15_h_L0 t s0 f e hk hk0]
        exact (hf.1 k ((H15_mem_layer0' k).mpr ⟨hk, hk0⟩)).1
    · obtain ⟨hrk, -⟩ := H15_vk_mul hn hrodd k hk
      rw [hdef, H15_h_mid t s0 f e hrk, H15_h_mid t s0 f e hk]
      exact (hlay _ k hk rfl).1
  · -- F3
    intro k hk0
    by_cases hk : 2 ^ a ∣ k.val
    · have hnk : 2 ^ a ∣ (-k).val := (H15_dvd_neg hA k).mpr hk
      have hnk0 : -k ≠ 0 := neg_ne_zero.mpr hk0
      rw [hdef, H15_h_L0 t s0 f e hk hk0, H15_h_L0 t s0 f e hnk hnk0]
      exact (hf.1 k ((H15_mem_layer0' k).mpr ⟨hk, hk0⟩)).2
    · obtain ⟨hnk, -⟩ := H15_vk_neg hn k hk
      rw [hdef, H15_h_mid t s0 f e hnk, H15_h_mid t s0 f e hk]
      exact (hlay _ k hk rfl).2
  · rw [hdef, H15_h_zero]
    exact he2
  · -- F4
    intro k
    by_cases hk : 2 ^ a ∣ k.val
    · exact hF4L0 k hk
    · by_cases hkm : 2 ^ a ∣ (k + half n).val
      · have e := hF4L0 (k + half n) hkm
        rw [show k + half n + half n = k by linear_combination H7_two_half hev,
          show 2 * (k + half n) = 2 * k by linear_combination H7_two_half hev] at e
        rw [mul_comm]
        exact e
      · obtain ⟨hk0, hka⟩ := H15_vk_lt hk
        have hv : padicValNat 2 k.val + 2 ≤ a := by
          by_contra hcon
          have hva : padicValNat 2 k.val = a - 1 := by omega
          have h1 : 2 ^ (a - 1) ∣ k.val := (padicValNat_dvd_iff_le hk0).mpr hva.ge
          exact hkm (H15_add_half_L0 hn (by omega) hodd k h1 hk)
        obtain ⟨h2k, -, -, hd⟩ := H15_hmid_two hn ha t s0 k hk hv
        rw [hhm, hdef, H15_h_mid t s0 f e hk, H15_h_mid t s0 f e hkm, H15_h_mid t s0 f e h2k, hd]
        linear_combination (-(H15_hmid t s0 k * H15_hmid t s0 (k + half n))) * mul_inv_cancel₀ hs0

/-- `P ∈ G''` (laws with `κ = 1`): `P(α^r) = α^{rσ} P(α)^r`, `P(α)P(α^{-1}) = α^m`. -/
theorem H15_P_mem {a nodd r : ℕ} [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (hr : ¬ r ∣ pp n * n) (σr : ℤ) [CharP L r] (ω : L) (hω : IsPrimitiveRoot ω n)
    (t : ZMod n → L) (ht : t ∈ topData n r σr (kappa n L) ω) (s0 : L) (hS : s0 ^ 2 = kappa n L)
    (hsgn : (-1 : L) ^ σr.natAbs * s0 ^ (r - 1) = 1) :
    H15_P a t s0 ∈ Gprime n a r σr 1 ω := by
  have hrodd : Odd r := H15_r_odd hn ha hr
  have h8 : 2 ^ 3 ∣ n := H15_dvd_n hn ha
  have h8' : 8 ∣ n := by simpa using h8
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h8)
  have hA : 2 ^ a ∣ n := H15_dvd_n hn le_rfl
  have hκ : kappa n L ≠ 0 := H15_kappa_ne hr
  have hs0 : s0 ≠ 0 := by
    rintro rfl
    apply hκ
    rw [← hS]
    ring
  have hlay := H15_layers hn ha hodd hr σr ω hω t ht s0 hS hsgn
  have hu := H15_unit_r hr
  have hr1 : 1 ≤ r := hrodd.pos
  have hsgn' : (-1 : L) ^ σr.natAbs = s0⁻¹ ^ (r - 1) := by
    rw [inv_pow]
    exact eq_inv_of_mul_eq_one_left hsgn
  have hpowr : s0⁻¹ ^ r = s0⁻¹ * s0⁻¹ ^ (r - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hr1]
  refine ⟨fun α hα => ?_, fun α hα => ?_⟩
  · obtain ⟨hαa, hα0⟩ := (H15_mem_layer0' α).mp hα
    have hrα : (r : ZMod n) * α ∈ layer0' n a :=
      (H15_mem_layer0' _).mpr ⟨(H15_dvd_mul_odd hA hrodd α).mpr hαa, fun h0 => hα0 ((hu.mul_right_eq_zero).mp h0)⟩
    have hnα : -α ∈ layer0' n a := (H15_mem_layer0' _).mpr ⟨(H15_dvd_neg hA α).mpr hαa, neg_ne_zero.mpr hα0⟩
    have hαm := H15_L0_add_half hn (by omega) hodd α hαa
    have hl := hlay _ (α + half n) hαm rfl
    unfold H15_P
    rw [ite_eq_left hrα, ite_eq_left hα, ite_eq_left hnα]
    constructor
    · have e := hl.1
      rw [mul_add, H7_odd_mul_half hev r hrodd, H15_omega_add_half hev hω,
        show -ω ^ α.val = (-1) * ω ^ α.val by ring, mul_zpow, H7_neg_one_zpow r hrodd] at e
      rw [e, mul_pow, hpowr, hsgn']
      ring
    · rw [H7_neg_add_half hev,
        show s0⁻¹ * H15_hmid t s0 (α + half n) * (s0⁻¹ * H15_hmid t s0 (-(α + half n)))
          = s0⁻¹ ^ 2 * (H15_hmid t s0 (α + half n) * H15_hmid t s0 (-(α + half n))) by ring,
        hl.2, H15_omega_add_half hev hω, Even.neg_pow ⟨n / 4, by omega⟩, ← hS, ← mul_assoc, ← mul_pow,
        inv_mul_cancel₀ hs0, one_pow]
  · unfold H15_P
    rw [ite_eq_right hα]

/-- A quotient of two elements of `G''` lies in `G`. -/
theorem H15_div_mem_G {a r : ℕ} (σr : ℤ) (ω : L) (hω0 : ω ≠ 0) (A B : ZMod n → L)
    (hA : A ∈ Gprime n a r σr 1 ω) (hB : B ∈ Gprime n a r σr 1 ω) :
    (fun k => A k / B k) ∈ Ggrp n a r := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · obtain ⟨hA1, hA3⟩ := hA.1 k hk
    obtain ⟨hB1, hB3⟩ := hB.1 k hk
    have hW : (ω ^ k.val) ^ (n / 2) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hω0)
    have hBk : B k ≠ 0 := by
      intro h0
      rw [h0, zero_mul, one_mul] at hB3
      exact hW hB3.symm
    have hBnk : B (-k) ≠ 0 := by
      intro h0
      rw [h0, mul_zero, one_mul] at hB3
      exact hW hB3.symm
    have hZ : (ω ^ k.val) ^ ((r : ℤ) * σr) ≠ 0 := zpow_ne_zero _ (pow_ne_zero _ hω0)
    constructor
    · show A ((r : ZMod n) * k) / B ((r : ZMod n) * k) = (A k / B k) ^ r
      rw [hA1, hB1, mul_div_mul_left _ _ hZ, div_pow]
    · show A (-k) / B (-k) * (A k / B k) = 1
      rw [div_mul_div_comm, mul_comm (A (-k)), mul_comm (B (-k)), hA3, hB3]
      exact div_self (by rw [one_mul]; exact hW)
  · show A k / B k = 1
    rw [hA.2 k hk, hB.2 k hk, div_one]

/-- Twisting the top data by `λ ∈ 𝒟^0` keeps top data. -/
theorem H15_twist_mem {r : ℕ} (σr : ℤ) (κ ω : L) (t lam : ZMod n → L) (ht : t ∈ topData n r σr κ ω)
    (hl : lam ∈ (topData0 n r : Set (ZMod n → L))) : (fun k => t k * lam k) ∈ topData n r σr κ ω := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · obtain ⟨h1, h3⟩ := ht.1 k hk
    obtain ⟨l1, l3⟩ := hl.1 k hk
    constructor
    · show t ((r : ZMod n) * k) * lam ((r : ZMod n) * k) = (ω ^ k.val) ^ ((r : ℤ) * σr) * (t k * lam k) ^ r
      rw [h1, l1]
      ring
    · show t k * lam k * (t (-k) * lam (-k)) = κ * (ω ^ k.val) ^ (n / 2)
      rw [show t k * lam k * (t (-k) * lam (-k)) = (t k * t (-k)) * (lam k * lam (-k)) by ring, h3, l3, mul_one]
  · show t k * lam k = 0
    rw [ht.2 k hk, zero_mul]

theorem H15_hmid_twist {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (t lam : ZMod n → L)
    (s0 : L) (α : ZMod n) (hα : α ∈ layer0' n a) :
    H15_hmid (fun k => t k * lam k) s0 (α + half n) = H15_hmid t s0 (α + half n) * Pmap n a lam α := by
  obtain ⟨hαa, -⟩ := (H15_mem_layer0' α).mp hα
  have hTm : 2 ^ (a - 1) ∣ (α + half n).val :=
    (H15_dvd_add_half (H15_dvd_n hn (by omega)) (H15_dvd_half hn (by omega) le_rfl) α).mpr
      (dvd_trans (pow_dvd_pow 2 (by omega)) hαa)
  have hna : ¬ 2 ^ (a - 1 + 1) ∣ (α + half n).val := by
    rw [show a - 1 + 1 = a by omega]
    exact H15_L0_add_half hn (by omega) hodd α hαa
  have h0 : (α + half n).val ≠ 0 := fun h => hna (h ▸ dvd_zero _)
  have hv : padicValNat 2 (α + half n).val = a - 1 := (H15_vk_iff h0 _).mpr ⟨hTm, hna⟩
  unfold H15_hmid
  rw [H15_D_mul, hv]
  unfold Pmap H15_D
  rw [ite_eq_left hα]
  ring

end Build

/-! ## The torsor under the homogeneous group -/

section Torsor

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

/-- The homogeneous laws (h1_r), (h3), (h4) (the subtype counted in `thm_6_4_step67`). -/
def H15_H (r : ℕ) (lam : ZMod n → L) : Prop :=
  (∀ k, lam ((r : ZMod n) * k) = lam k ^ r) ∧ (∀ k, lam k * lam (-k) = 1) ∧
    ∀ k, lam k * lam (k + half n) = lam (half n) * lam (2 * k)

theorem H15_F3r_ne {κ ω : L} (hκ : κ ≠ 0) (hω0 : ω ≠ 0) (hn0 : (n : L) ≠ 0) (h : ZMod n → L)
    (hF3 : F3r κ ω h) (k : ZMod n) : h k ≠ 0 := by
  intro hk
  by_cases hk0 : k = 0
  · subst hk0
    have e := hF3.2
    rw [hk, zero_pow two_ne_zero] at e
    exact pow_ne_zero 2 hn0 e.symm
  · have e := hF3.1 k hk0
    rw [hk, zero_mul] at e
    exact mul_ne_zero hκ (pow_ne_zero _ (pow_ne_zero _ hω0)) e.symm

theorem H15_ratio {r : ℕ} {σr : ℤ} {κ ω : L} (hκ : κ ≠ 0) (hω0 : ω ≠ 0) (hn0 : (n : L) ≠ 0) (h h' : ZMod n → L)
    (hh : F1 r σr ω h ∧ F3r κ ω h ∧ F4 h) (hh' : F1 r σr ω h' ∧ F3r κ ω h' ∧ F4 h') :
    H15_H r (fun k => h' k / h k) := by
  obtain ⟨hF1, hF3, hF4⟩ := hh
  obtain ⟨hF1', hF3', hF4'⟩ := hh'
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_⟩
  · show h' ((r : ZMod n) * k) / h ((r : ZMod n) * k) = (h' k / h k) ^ r
    rw [hF1 k, hF1' k, mul_div_mul_left _ _ (zpow_ne_zero _ (pow_ne_zero _ hω0)), div_pow]
  · show h' k / h k * (h' (-k) / h (-k)) = 1
    rw [div_mul_div_comm]
    by_cases hk0 : k = 0
    · subst hk0
      rw [neg_zero, ← pow_two, ← pow_two, hF3.2, hF3'.2]
      exact div_self (pow_ne_zero 2 hn0)
    · rw [hF3.1 k hk0, hF3'.1 k hk0]
      exact div_self (mul_ne_zero hκ (pow_ne_zero _ (pow_ne_zero _ hω0)))
  · show h' k / h k * (h' (k + half n) / h (k + half n)) = h' (half n) / h (half n) * (h' (2 * k) / h (2 * k))
    rw [div_mul_div_comm, div_mul_div_comm, hF4 k, hF4' k]

theorem H15_twistF {r : ℕ} {σr : ℤ} {κ ω : L} (h lam : ZMod n → L) (hh : F1 r σr ω h ∧ F3r κ ω h ∧ F4 h)
    (hl : H15_H r lam) :
    F1 r σr ω (fun k => lam k * h k) ∧ F3r κ ω (fun k => lam k * h k) ∧ F4 (fun k => lam k * h k) := by
  obtain ⟨hF1, hF3, hF4⟩ := hh
  obtain ⟨hl1, hl3, hl4⟩ := hl
  refine ⟨fun k => ?_, ⟨fun k hk0 => ?_, ?_⟩, fun k => ?_⟩
  · show lam ((r : ZMod n) * k) * h ((r : ZMod n) * k) = (ω ^ k.val) ^ ((r : ℤ) * σr) * (lam k * h k) ^ r
    rw [hF1 k, hl1 k]
    ring
  · show lam k * h k * (lam (-k) * h (-k)) = κ * (ω ^ k.val) ^ (n / 2)
    rw [show lam k * h k * (lam (-k) * h (-k)) = (lam k * lam (-k)) * (h k * h (-k)) by ring, hl3 k,
      hF3.1 k hk0, one_mul]
  · show (lam 0 * h 0) ^ 2 = (n : L) ^ 2
    have e := hl3 0
    rw [neg_zero] at e
    rw [mul_pow, hF3.2, pow_two (lam 0), e, one_mul]
  · show lam k * h k * (lam (k + half n) * h (k + half n)) =
      lam (half n) * h (half n) * (lam (2 * k) * h (2 * k))
    rw [show lam k * h k * (lam (k + half n) * h (k + half n)) =
      (lam k * lam (k + half n)) * (h k * h (k + half n)) by ring, hl4 k, hF4 k]
    ring

theorem H15_torsor {r : ℕ} (σr : ℤ) {κ ω : L} (hκ : κ ≠ 0) (hω0 : ω ≠ 0) (hn0 : (n : L) ≠ 0) (h0 : ZMod n → L)
    (hh0 : F1 r σr ω h0 ∧ F3r κ ω h0 ∧ F4 h0) :
    Nat.card ({h | F1 r σr ω h ∧ F3r κ ω h ∧ F4 h} : Set (ZMod n → L)) =
      Nat.card {lam : ZMod n → L // H15_H r lam} := by
  have hne := H15_F3r_ne hκ hω0 hn0 h0 hh0.2.1
  apply Nat.card_congr
  exact
    { toFun := fun h => ⟨fun k => h.1 k / h0 k, H15_ratio hκ hω0 hn0 _ _ hh0 h.2⟩
      invFun := fun lam => ⟨fun k => lam.1 k * h0 k, H15_twistF _ _ hh0 lam.2⟩
      left_inv := fun h => Subtype.ext (funext fun k => div_mul_cancel₀ _ (hne k))
      right_inv := fun lam => Subtype.ext (funext fun k => mul_div_cancel_right₀ _ (hne k)) }

end Torsor

/-! ## One solution exists (choice of top data, sign, layer 0) -/

section Exists

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

theorem H15_exists {a nodd r : ℕ} [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (hr : ¬ r ∣ pp n * n) (σr : ℤ) (hsign : (-1 : ℤ) ^ σr.natAbs = legendreSym r (pp n : ℤ))
    [CharP L r] [IsAlgClosed L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (htop : (topData n r σr (kappa n L) ω).Nonempty)
    (hG' : (Gprime n a r σr (kappa n L) ω).Nonempty)
    (hτ : ∀ f ∈ Gprime n a r σr (kappa n L) ω, tauG n a f / f ∈ Gprime n a r σr 1 ω)
    (hPi : Set.SurjOn (Pmap n a) (topData0 n r : Set (ZMod n → L)) (Ggrp n a r)) :
    ∃ h : ZMod n → L, F1 r σr ω h ∧ F3r (kappa n L) ω h ∧ F4 h := by
  have h8 : 2 ^ 3 ∣ n := H15_dvd_n hn ha
  have h8' : 8 ∣ n := by simpa using h8
  have hκ : kappa n L ≠ 0 := H15_kappa_ne hr
  have hω0 : ω ≠ 0 := hω.ne_zero (NeZero.ne n)
  obtain ⟨t0, ht0⟩ := htop
  obtain ⟨s0, hS⟩ := IsAlgClosed.exists_pow_nat_eq (kappa n L) two_pos
  have hsgn := H15_sgn hn ha hodd hr σr hsign ω hω t0 ht0 s0 hS
  -- layer 0: `f0 ∈ G'`, and the top data twisted so that `P = τ f0 / f0`
  obtain ⟨f0, hf0⟩ := hG'
  have hA := hτ f0 hf0
  have hB := H15_P_mem hn ha hodd hr σr ω hω t0 ht0 s0 hS hsgn
  have hg := H15_div_mem_G σr ω hω0 _ _ hA hB
  obtain ⟨lam, hlam, hPl⟩ := hPi hg
  have ht := H15_twist_mem σr (kappa n L) ω t0 lam ht0 hlam
  have hE1 : ∀ α ∈ layer0' n a,
      f0 (2 * α) = s0⁻¹ * H15_hmid (fun k => t0 k * lam k) s0 (α + half n) * f0 α := by
    intro α hα
    have hτα : tauG n a f0 α = f0 (2 * α) := by
      unfold tauG
      rw [ite_eq_left hα]
    have hf0α : f0 α ≠ 0 := by
      intro h0
      have e := (hf0.1 α hα).2
      rw [h0, zero_mul] at e
      exact mul_ne_zero hκ (pow_ne_zero _ (pow_ne_zero _ hω0)) e.symm
    have hBα : H15_P a t0 s0 α ≠ 0 := by
      intro h0
      have e := (hB.1 α hα).2
      rw [h0, zero_mul, one_mul] at e
      exact pow_ne_zero _ (pow_ne_zero _ hω0) e.symm
    have hgα : Pmap n a lam α = (tauG n a f0 / f0) α / H15_P a t0 s0 α := by rw [hPl]
    have hPα : H15_P a t0 s0 α = s0⁻¹ * H15_hmid t0 s0 (α + half n) := by
      unfold H15_P
      rw [ite_eq_left hα]
    rw [H15_hmid_twist hn ha hodd t0 lam s0 α hα, hgα, Pi.div_apply, hτα]
    calc f0 (2 * α) = H15_P a t0 s0 α * (f0 (2 * α) / f0 α / H15_P a t0 s0 α) * f0 α := by
          field_simp
      _ = _ := by
          rw [hPα]
          ring
  exact ⟨_, H15_build hn ha hodd hr σr ω hω _ ht s0 hS hsgn f0 hf0 hE1 (n : L) rfl (H15_natCast_pow_r n)⟩

end Exists

/-! ## `∏ (r^{L_i} - 1) ≠ 0` -/

theorem H15_pairProd_ne_zero (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a)
    (hodd : Odd nodd) (hr : ¬ r ∣ pp n * n) (hr1 : r % 2 ^ a ≠ 2 ^ a - 1) : pairProd n r ≠ 0 := by
  have hp : r.Prime := Fact.out
  have hpairs := (thm_6_4_pairs_proved n a nodd r hn ha hodd hr hr1).1
  unfold pairProd
  rw [Finset.prod_ne_zero_iff]
  intro P hP
  obtain ⟨O, hO, rfl⟩ := Finset.mem_image.mp hP
  obtain ⟨-, hne, hcard⟩ := hpairs O hO
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hO
  have hkO : k ∈ orbit r k := H6_self_mem r k
  have hU : (({orbit r k, inv (orbit r k)} : Finset (Finset (ZMod n))).biUnion id) =
      orbit r k ∪ inv (orbit r k) := by
    simp [Finset.biUnion_insert]
  have hc2 : 2 ≤ (orbit r k ∪ inv (orbit r k)).card := by
    by_contra hcon
    push Not at hcon
    have h1 : 1 ≤ (orbit r k).card := Finset.card_pos.mpr ⟨k, hkO⟩
    have hs1 : orbit r k = orbit r k ∪ inv (orbit r k) :=
      Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
    have hs2 : inv (orbit r k) = orbit r k ∪ inv (orbit r k) :=
      Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
    exact hne (hs2.trans hs1.symm)
  unfold pairLen
  rw [hU]
  have hL : 1 ≤ (orbit r k ∪ inv (orbit r k)).card / 2 := by omega
  have : 1 < r ^ ((orbit r k ∪ inv (orbit r k)).card / 2) := Nat.one_lt_pow (by omega) hp.one_lt
  omega

/-! ## Row 24b' — Step 3, last sentence (descent for a solution) -/

section Step3b

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

/-- For `h` with (F4) and `h(-1) = s0 ≠ 0`, the descent formula holds above layer 0: `h = s0^{-(2^v-1)} D_v(h)`. -/
theorem H15_descent {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (h : ZMod n → L) (s0 : L)
    (hF4 : ∀ k, h k * h (k + half n) = s0 * h (2 * k)) (hs0 : s0 ≠ 0) :
    ∀ v : ℕ, ∀ x : ZMod n, ¬ 2 ^ a ∣ x.val → padicValNat 2 x.val = v → h x = H15_hmid h s0 x := by
  intro v
  induction v with
  | zero =>
    intro x hx hv
    have hx0 := (H15_vk_lt hx).1
    have hxo : Odd x.val := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      intro h2'
      have := (padicValNat_dvd_iff_le hx0).mp (by simpa using h2' : 2 ^ 1 ∣ x.val)
      omega
    rw [H15_hmid_odd h s0 hxo]
  | succ v ih =>
    intro x hx hv
    obtain ⟨hx0, hxa⟩ := H15_vk_lt hx
    obtain ⟨y, rfl, hy, hyv⟩ := H15_halve x hx hv
    obtain ⟨-, hym, hymv, hdy⟩ := H15_hmid_two hn ha h s0 y hy (by omega)
    rw [hdy, ← ih y hy hyv, ← ih (y + half n) hym (hymv.trans hyv)]
    linear_combination (-s0⁻¹) * hF4 y - h (2 * y) * inv_mul_cancel₀ hs0

theorem H15_dft_half {F : Type*} [Field F] [Algebra F L] (hev : Even n) (ω : L) (hω : IsPrimitiveRoot ω n)
    (y : ZMod n → F) : dftA ω y (half n) = algebraMap F L (S y) := by
  show (∑ t, algebraMap F L (y t) * (ω ^ (half n).val) ^ t.val) = algebraMap F L (∑ t, (-1) ^ t.val * y t)
  rw [H7_half_val, H7_pow_half_eq_neg_one hev hω, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, map_pow, map_neg, map_one, mul_comm]

/-- `Ξ_a` (elements of order `2^a` of `μ_{2^a}`) = the `ρ ∈ 𝓛_a` with `ρ^{2^{a-1}} = -1`. -/
theorem H15_Xi_eq {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) :
    univ.filter (fun k : ZMod n => (2 ^ a : ZMod n) * k = 0 ∧ (2 ^ (a - 1) : ZMod n) * k ≠ 0) =
      (topLayer n).filter (fun ρ => (2 ^ (a - 1) : ZMod n) * ρ = half n) := by
  have h8 : 2 ^ 3 ∣ n := H15_dvd_n hn ha
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h8)
  have h2n : 2 ≤ n := Nat.le_of_dvd (NeZero.pos n) (dvd_trans (by norm_num) h8)
  have hA : 2 ^ a ∣ n := H15_dvd_n hn le_rfl
  have hma : ¬ 2 ^ a ∣ (half n : ZMod n).val := by
    rw [H7_half_val]
    exact H15_not_dvd_half hn (by omega) hodd
  have hpa : (2 ^ a : ZMod n) = 2 * 2 ^ (a - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, topLayer]
  constructor
  · rintro ⟨h1, h2⟩
    have hy2 : 2 * ((2 ^ (a - 1) : ZMod n) * k) = 0 := by rw [← mul_assoc, ← hpa]; exact h1
    rcases (H15_two_mul_eq_zero hev _).mp hy2 with h3 | h3
    · exact absurd h3 h2
    · refine ⟨?_, h3⟩
      by_contra hko
      rw [Nat.not_odd_iff_even] at hko
      obtain ⟨w, hw⟩ := hko
      have hk2 : k = 2 * (w : ZMod n) := by
        have := ZMod.natCast_zmod_val k
        rw [hw] at this
        push_cast at this
        rw [← this]
        ring
      rw [hk2, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ a)] at h3
      have hc : ZMod.castHom hA (ZMod (2 ^ a)) ((2 : ZMod n) ^ a * (w : ZMod n)) = 0 := by
        rw [map_mul, map_pow, map_natCast, map_ofNat]
        have h2a : (2 : ZMod (2 ^ a)) ^ a = 0 := by exact_mod_cast ZMod.natCast_self (2 ^ a)
        rw [h2a, zero_mul]
      exact hma ((H15_dvd_cast hA (half n)).mpr (by rw [← h3]; exact hc))
  · rintro ⟨-, h3⟩
    refine ⟨?_, by rw [h3]; exact H15_half_ne_zero h2n⟩
    rw [hpa, mul_assoc, h3, two_mul, H7_two_half hev]

end Step3b

/-- Row 24b' — proof of Theorem 6.4, Step 3, last sentence, GIVEN the row sec_6_3_fourier (exact instance at the same
`L`, `ω`). -/
theorem thm_6_4_step3b_of (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a)
    (hodd : Odd nodd) (hr : ¬ r ∣ pp n * n) (σr : ℤ) {L : Type*} [Field L]
    [Algebra (GaloisField r (n / Int.gcd σr n)) L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (y : ZMod n → GaloisField r (n / Int.gcd σr n)) (hy : y ∈ NFrSet n r σr)
    (hFour : Set.BijOn (dftA ω) (NFrSet n r σr) {h | F1 r σr ω h ∧ F3r (kappa n L) ω h ∧ F4 h} ∧
      ∀ y ∈ NFrSet n r σr, S y ^ 2 = kappa n _) :
    ∏ k ∈ univ.filter (fun k : ZMod n => (2 ^ a : ZMod n) * k = 0 ∧ (2 ^ (a - 1) : ZMod n) * k ≠ 0), dftA ω y k =
        (-kappa n L) ^ (2 ^ (a - 2)) ∧
      (-kappa n L) ^ (2 ^ (a - 2)) = algebraMap _ L (S y) ^ (2 ^ (a - 1)) ∧
      (-1) ^ σr.natAbs * algebraMap _ L (S y) ^ (r - 1) = 1 := by
  have : CharP L r :=
    charP_of_injective_algebraMap (algebraMap (GaloisField r (n / Int.gcd σr n)) L).injective r
  have h8 : 2 ^ 3 ∣ n := H15_dvd_n hn ha
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h8)
  have hκ : kappa n L ≠ 0 := H15_kappa_ne hr
  have hrodd : Odd r := H15_r_odd hn ha hr
  have hSL := H15_dft_half (L := L) hev ω hω y
  have hS2 : algebraMap _ L (S y) ^ 2 = kappa n L := by
    rw [← map_pow, hFour.2 y hy]
    unfold kappa
    simp
  have hS0 : algebraMap _ L (S y) ≠ 0 := by
    intro h0
    apply hκ
    rw [← hS2, h0]
    ring
  obtain ⟨-, -, hF4⟩ := hFour.1.mapsTo hy
  have hF4' : ∀ k, dftA ω y k * dftA ω y (k + half n) = algebraMap _ L (S y) * dftA ω y (2 * k) := fun k => by
    rw [hF4 k, hSL]
  have hma : ¬ 2 ^ a ∣ (half n : ZMod n).val := by
    rw [H7_half_val]
    exact H15_not_dvd_half hn (by omega) hodd
  have hnodd0 : nodd ≠ 0 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) ⟨0, rfl⟩
  have hmv : padicValNat 2 (half n : ZMod n).val = a - 1 := by
    rw [H7_half_val, H15_half_eq hn (by omega), padicValNat.mul (by positivity) hnodd0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (fun h => Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr h)), add_zero]
  have hm := H15_descent hn ha (dftA ω y) _ hF4' hS0 _ (half n) hma rfl
  unfold H15_hmid at hm
  rw [hmv] at hm
  have hN : 1 ≤ 2 ^ (a - 1) := Nat.one_le_two_pow
  have hD : H15_D (a - 1) (dftA ω y) (half n) = algebraMap _ L (S y) ^ (2 ^ (a - 1)) := by
    calc H15_D (a - 1) (dftA ω y) (half n)
        = (algebraMap _ L (S y) * (algebraMap _ L (S y))⁻¹) ^ (2 ^ (a - 1) - 1) *
            H15_D (a - 1) (dftA ω y) (half n) := by rw [mul_inv_cancel₀ hS0, one_pow, one_mul]
      _ = algebraMap _ L (S y) ^ (2 ^ (a - 1) - 1) *
            ((algebraMap _ L (S y))⁻¹ ^ (2 ^ (a - 1) - 1) * H15_D (a - 1) (dftA ω y) (half n)) := by
          rw [mul_pow]
          ring
      _ = algebraMap _ L (S y) ^ (2 ^ (a - 1) - 1) * algebraMap _ L (S y) := by rw [← hm, hSL]
      _ = _ := by rw [← pow_succ, Nat.sub_add_cancel hN]
  have hpow : (-kappa n L) ^ (2 ^ (a - 2)) = algebraMap _ L (S y) ^ (2 ^ (a - 1)) := by
    have he : Even (2 ^ (a - 2)) := (Nat.even_pow' (by omega)).mpr even_two
    rw [he.neg_pow, ← hS2, ← pow_mul, ← pow_succ']
    congr 2
    omega
  refine ⟨?_, hpow, ?_⟩
  · rw [H15_Xi_eq hn ha hodd]
    exact hD.trans hpow.symm
  · have hSr := congrArg (algebraMap (GaloisField r (n / Int.gcd σr n)) L)
      (H5_S_pow_char r hrodd hev σr y hy.1)
    rw [map_pow, map_mul, map_pow, map_neg, map_one] at hSr
    have hr1 : 1 ≤ r := hrodd.pos
    have hpr : algebraMap _ L (S y) ^ (r - 1) = (-1) ^ σr.natAbs := by
      apply mul_right_cancel₀ hS0
      rw [← pow_succ, Nat.sub_add_cancel hr1, hSr]
    rw [hpr, ← mul_pow, neg_one_mul, neg_neg, one_pow]

/-! ## Row 26(ii) — Proposition 6.6 (`n = 2^a`, `r ≡ -1 (mod 2^a)`): layer 0 is `{1}` -/

section Prop66

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

theorem H15_r_eq_neg_one {a r : ℕ} (hn : n = 2 ^ a) (hr1 : r % 2 ^ a = 2 ^ a - 1) : (r : ZMod n) = -1 := by
  have hpos := NeZero.pos n
  have h' : r % n = n - 1 := by rw [hn]; exact hr1
  rw [← ZMod.natCast_mod r n, h', Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self, Nat.cast_one, zero_sub]

theorem H15_L0_iff {a : ℕ} (hn : n = 2 ^ a) (k : ZMod n) : 2 ^ a ∣ k.val ↔ k = 0 := by
  constructor
  · intro h
    have hlt := ZMod.val_lt k
    rw [← hn] at h
    exact (ZMod.val_eq_zero k).mp (Nat.eq_zero_of_dvd_of_lt h hlt)
  · rintro rfl
    rw [ZMod.val_zero]
    exact dvd_zero _

theorem H15_hr66 {a r : ℕ} [Fact r.Prime] (hn : n = 2 ^ a) (ha : 3 ≤ a) (hr : ¬ r ∣ pp n)
    (hr1 : r % 2 ^ a = 2 ^ a - 1) : ¬ r ∣ pp n * n := by
  have hp : r.Prime := Fact.out
  have hN : 8 ≤ 2 ^ a :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  intro hd
  rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
  · exact hr h
  · rw [hn] at h
    have h2 : r = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
    rw [h2, Nat.mod_eq_of_lt (by omega)] at hr1
    omega

/-- Representatives of the top orbits `{ρ, ρ^{-1}} = {ρ, ρ^r}`: odd `k` with `k < n/2`. -/
noncomputable def H15_R (n : ℕ) [NeZero n] : Finset (ZMod n) := (topLayer n).filter (fun k => k.val < n / 2)

theorem H15_mem_R (k : ZMod n) : k ∈ H15_R n ↔ Odd k.val ∧ k.val < n / 2 := by
  simp [H15_R, topLayer]

theorem H15_R_neg (h4 : 4 ∣ n) {k : ZMod n} (hk : Odd k.val) :
    Odd (-k).val ∧ (k ∈ H15_R n ↔ -k ∉ H15_R n) := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [ZMod.val_zero] at hk
    exact absurd hk (by decide)
  have hlt := ZMod.val_lt k
  have hneg : (-k).val = n - k.val := by rw [ZMod.neg_val, ite_eq_right hk0]
  rw [Nat.odd_iff] at hk
  have hno : Odd (-k).val := by
    rw [Nat.odd_iff, hneg]
    omega
  refine ⟨hno, ?_⟩
  rw [H15_mem_R, H15_mem_R, hneg, Nat.odd_iff, Nat.odd_iff]
  omega

theorem H15_card_R (h4 : 4 ∣ n) : (H15_R n).card = n / 4 := by
  symm
  rw [← Finset.card_range (n / 4)]
  apply Finset.card_bij (fun j _ => ((2 * j + 1 : ℕ) : ZMod n))
  · intro j hj
    rw [Finset.mem_range] at hj
    rw [H15_mem_R, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    exact ⟨⟨j, rfl⟩, by omega⟩
  · intro j1 hj1 j2 hj2 h
    rw [Finset.mem_range] at hj1 hj2
    have := congrArg ZMod.val h
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  · intro k hk
    rw [H15_mem_R] at hk
    obtain ⟨⟨j, hj⟩, hlt⟩ := hk
    refine ⟨j, Finset.mem_range.mpr (by omega), ?_⟩
    rw [← hj, ZMod.natCast_zmod_val]

/-- `W(k) := ξ^{rσ}` at `ξ = ω^k`. -/
noncomputable def H15_W (r : ℕ) (σr : ℤ) (ω : L) (k : ZMod n) : L := (ω ^ k.val) ^ ((r : ℤ) * σr)

theorem H15_W_ne (r : ℕ) (σr : ℤ) {ω : L} (hω0 : ω ≠ 0) (k : ZMod n) : H15_W r σr ω k ≠ 0 :=
  zpow_ne_zero _ (pow_ne_zero _ hω0)

theorem H15_W_neg (r : ℕ) (σr : ℤ) {ω : L} (hω : IsPrimitiveRoot ω n) (k : ZMod n) :
    H15_W r σr ω k * H15_W r σr ω (-k) = 1 := by
  unfold H15_W
  rw [← mul_zpow, ← H7_pow_val_add ω hω.pow_eq_one, add_neg_cancel, ZMod.val_zero, pow_zero, one_zpow]

theorem H15_omega_odd (hev : Even n) {ω : L} (hω : IsPrimitiveRoot ω n) {k : ZMod n} (hk : Odd k.val) :
    (ω ^ k.val) ^ (n / 2) = -1 := by
  rw [← pow_mul, mul_comm, pow_mul, H7_pow_half_eq_neg_one hev hω, hk.neg_one_pow]

/-- Top data from values `cc` at the representatives: `ρ ↦ cc ρ`, `ρ^{-1} ↦ W(ρ) cc(ρ)^r` (F1 at `ρ`). -/
noncomputable def H15_Hfun (r : ℕ) (σr : ℤ) (ω : L) (cc : ZMod n → L) (k : ZMod n) : L :=
  if k ∈ H15_R n then cc k else if -k ∈ H15_R n then H15_W r σr ω (-k) * cc (-k) ^ r else 0

theorem H15_Hfun_R (r : ℕ) (σr : ℤ) (ω : L) (cc : ZMod n → L) {k : ZMod n} (hk : k ∈ H15_R n) :
    H15_Hfun r σr ω cc k = cc k := by
  unfold H15_Hfun
  rw [ite_eq_left hk]

theorem H15_Hfun_congr (r : ℕ) (σr : ℤ) (ω : L) {cc cc' : ZMod n → L} (h : ∀ k ∈ H15_R n, cc k = cc' k) :
    H15_Hfun r σr ω cc = H15_Hfun r σr ω cc' := by
  funext k
  unfold H15_Hfun
  split_ifs with h1 h2
  · exact h k h1
  · rw [h (-k) h2]
  · rfl

theorem H15_Hfun_self {a r : ℕ} (hn : n = 2 ^ a) (ha : 3 ≤ a) (hr1 : r % 2 ^ a = 2 ^ a - 1) (σr : ℤ) (κ ω : L)
    (h : ZMod n → L) (ht : h ∈ topData n r σr κ ω) : H15_Hfun r σr ω h = h := by
  have h4' : 2 ^ 2 ∣ n := H15_dvd_n (nodd := 1) (by rw [hn, mul_one]) (by omega)
  have h4 : 4 ∣ n := by simpa using h4'
  have hrm := H15_r_eq_neg_one hn hr1
  funext k
  unfold H15_Hfun
  split_ifs with h1 h2
  · rfl
  · have hko : Odd (-k).val := ((H15_mem_R _).mp h2).1
    have e := (ht.1 (-k) hko).1
    rw [hrm, neg_one_mul, neg_neg] at e
    exact e.symm
  · have hke : Even k.val := by
      by_contra hko
      rw [Nat.not_even_iff_odd] at hko
      exact h2 (by_contra fun h3 => h1 ((H15_R_neg h4 hko).2.mpr h3))
    exact (ht.2 k hke).symm

theorem H15_Hfun_mem {a r : ℕ} [Fact r.Prime] [CharP L r] (hn : n = 2 ^ a) (ha : 3 ≤ a) (hr : ¬ r ∣ pp n)
    (hr1 : r % 2 ^ a = 2 ^ a - 1) (σr : ℤ) (ω : L) (hω : IsPrimitiveRoot ω n) (cc : ZMod n → L)
    (hcc : ∀ k ∈ H15_R n, cc k ^ (r + 1) = -kappa n L / H15_W r σr ω k) :
    H15_Hfun r σr ω cc ∈ topData n r σr (kappa n L) ω := by
  have hn1 : n = 2 ^ a * 1 := by rw [hn, mul_one]
  have h4' : 2 ^ 2 ∣ n := H15_dvd_n hn1 (by omega)
  have h4 : 4 ∣ n := by simpa using h4'
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h4)
  have h2 : 2 ^ 1 ∣ n := H15_dvd_n hn1 (by omega)
  have hrn := H15_hr66 hn ha hr hr1
  have hrodd : Odd r := H15_r_odd hn1 ha hrn
  have hrm := H15_r_eq_neg_one hn hr1
  have hκ : kappa n L ≠ 0 := H15_kappa_ne hrn
  have hω0 : ω ≠ 0 := hω.ne_zero (NeZero.ne n)
  have hκr : kappa n L ^ r = kappa n L := by
    unfold kappa
    rw [show (n : L) ^ 2 * (pp n : L) = ((n ^ 2 * pp n : ℕ) : L) by push_cast; ring, H15_natCast_pow_r]
  have hr1' : 1 ≤ r := hrodd.pos
  have hκq : (-kappa n L) ^ (r - 1) = 1 := by
    have he : Even (r - 1) := by
      obtain ⟨j, hj⟩ := hrodd
      exact ⟨j, by omega⟩
    rw [he.neg_pow]
    apply mul_right_cancel₀ hκ
    rw [← pow_succ, Nat.sub_add_cancel hr1', hκr, one_mul]
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · have hrk : (r : ZMod n) * k = -k := by rw [hrm, neg_one_mul]
    rw [hrk, H15_omega_odd hev hω hk]
    obtain ⟨-, hiff⟩ := H15_R_neg h4 hk
    by_cases hkR : k ∈ H15_R n
    · have hnR : -k ∉ H15_R n := hiff.mp hkR
      have hHk : H15_Hfun r σr ω cc k = cc k := H15_Hfun_R r σr ω cc hkR
      have hHnk : H15_Hfun r σr ω cc (-k) = H15_W r σr ω k * cc k ^ r := by
        unfold H15_Hfun
        rw [ite_eq_right hnR, neg_neg, ite_eq_left hkR]
      rw [hHk, hHnk]
      refine ⟨rfl, ?_⟩
      calc cc k * (H15_W r σr ω k * cc k ^ r) = H15_W r σr ω k * cc k ^ (r + 1) := by ring
        _ = H15_W r σr ω k * (-kappa n L / H15_W r σr ω k) := by rw [hcc k hkR]
        _ = kappa n L * -1 := by
          rw [mul_comm, div_mul_cancel₀ _ (H15_W_ne r σr hω0 k)]
          ring
    · have hnR : -k ∈ H15_R n := by
        by_contra h
        exact hkR (hiff.mpr h)
      have hHk : H15_Hfun r σr ω cc k = H15_W r σr ω (-k) * cc (-k) ^ r := by
        unfold H15_Hfun
        rw [ite_eq_right hkR, ite_eq_left hnR]
      have hHnk : H15_Hfun r σr ω cc (-k) = cc (-k) := H15_Hfun_R r σr ω cc hnR
      rw [hHk, hHnk]
      have hc := hcc (-k) hnR
      have hWW := H15_W_neg r σr hω k
      have hWn := H15_W_ne r σr hω0 (-k)
      constructor
      · show cc (-k) = H15_W r σr ω k * (H15_W r σr ω (-k) * cc (-k) ^ r) ^ r
        have key : H15_W r σr ω k * (H15_W r σr ω (-k) * cc (-k) ^ r) ^ r =
            (H15_W r σr ω k * H15_W r σr ω (-k)) * H15_W r σr ω (-k) ^ (r - 1) *
              (cc (-k) ^ (r + 1)) ^ (r - 1) * cc (-k) := by
          obtain ⟨q, hq⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
          rw [hq, Nat.add_sub_cancel]
          ring
        rw [key, hWW, hc, div_pow, hκq, one_mul, mul_one_div_cancel (pow_ne_zero _ hWn), one_mul]
      · calc H15_W r σr ω (-k) * cc (-k) ^ r * cc (-k) = H15_W r σr ω (-k) * cc (-k) ^ (r + 1) := by ring
          _ = H15_W r σr ω (-k) * (-kappa n L / H15_W r σr ω (-k)) := by rw [hc]
          _ = kappa n L * -1 := by
            rw [mul_comm, div_mul_cancel₀ _ hWn]
            ring
  · have hkR : k ∉ H15_R n := fun h => (Nat.not_even_iff_odd.mpr ((H15_mem_R k).mp h).1) hk
    have hnke : Even (-k).val := by
      rw [even_iff_two_dvd] at hk ⊢
      have := H15_dvd_neg h2 k
      simp only [pow_one] at this
      exact this.mpr hk
    have hnR : -k ∉ H15_R n := fun h => (Nat.not_even_iff_odd.mpr ((H15_mem_R _).mp h).1) hnke
    unfold H15_Hfun
    rw [ite_eq_right hkR, ite_eq_right hnR]

theorem H15_card_roots [IsAlgClosed L] {N : ℕ} (hN : 0 < N) {ζ : L} (hζ : IsPrimitiveRoot ζ N) (d : L)
    (hd : d ≠ 0) : Nat.card {c : L // c ^ N = d} = N := by
  classical
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq d hN
  have h1 : Nat.card {c : L // c ^ N = d} = (Polynomial.nthRootsFinset N d).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun c => (Polynomial.mem_nthRootsFinset hN d).symm))
  rw [h1, Polynomial.nthRootsFinset_def, Multiset.toFinset_card_of_nodup (hζ.nthRoots_nodup hd),
    hζ.card_nthRoots, ite_eq_left ⟨α, hα⟩]

/-- Top data for `r ≡ -1 (mod 2^a)`, `n = 2^a`: `(r+1)^{n/4}` (one root of `c^{r+1} = -κ ρ^{-rσ}` per pair). -/
theorem H15_topData_card {a r : ℕ} [Fact r.Prime] [CharP L r] [IsAlgClosed L] (hn : n = 2 ^ a) (ha : 3 ≤ a)
    (hr : ¬ r ∣ pp n) (hr1 : r % 2 ^ a = 2 ^ a - 1) (σr : ℤ) (ω : L) (hω : IsPrimitiveRoot ω n) :
    Nat.card (topData n r σr (kappa n L) ω) = (r + 1) ^ (n / 4) := by
  classical
  have hn1 : n = 2 ^ a * 1 := by rw [hn, mul_one]
  have h4' : 2 ^ 2 ∣ n := H15_dvd_n hn1 (by omega)
  have h4 : 4 ∣ n := by simpa using h4'
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h4)
  have hrn := H15_hr66 hn ha hr hr1
  have hrm := H15_r_eq_neg_one hn hr1
  have hκ : kappa n L ≠ 0 := H15_kappa_ne hrn
  have hω0 : ω ≠ 0 := hω.ne_zero (NeZero.ne n)
  have hr1L : ((r + 1 : ℕ) : L) ≠ 0 := by
    rw [Nat.cast_add, CharP.cast_eq_zero, zero_add, Nat.cast_one]
    exact one_ne_zero
  have : NeZero ((r + 1 : ℕ) : L) := ⟨hr1L⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot L (r + 1)
  have hroot : ∀ h ∈ topData n r σr (kappa n L) ω, ∀ k ∈ H15_R n,
      h k ^ (r + 1) = -kappa n L / H15_W r σr ω k := by
    intro h ht k hk
    have hko := ((H15_mem_R k).mp hk).1
    obtain ⟨e1, e3⟩ := ht.1 k hko
    rw [hrm, neg_one_mul] at e1
    rw [e1, H15_omega_odd hev hω hko] at e3
    rw [eq_div_iff (H15_W_ne r σr hω0 k)]
    unfold H15_W
    linear_combination e3
  let e : topData n r σr (kappa n L) ω ≃
      ((k : H15_R n) → {c : L // c ^ (r + 1) = -kappa n L / H15_W r σr ω k.1}) :=
    { toFun := fun h k => ⟨h.1 k.1, hroot h.1 h.2 k.1 k.2⟩
      invFun := fun (c : (k : H15_R n) → {c : L // c ^ (r + 1) = -kappa n L / H15_W r σr ω k.1}) =>
        ⟨H15_Hfun r σr ω (fun k => if hk : k ∈ H15_R n then (c ⟨k, hk⟩).1 else 0),
        H15_Hfun_mem hn ha hr hr1 σr ω hω _ (fun k hk => by
          rw [dite_eq_left hk]
          have hck := (c ⟨k, hk⟩).2
          exact hck)⟩
      left_inv := fun h => by
        apply Subtype.ext
        show H15_Hfun r σr ω (fun k => if hk : k ∈ H15_R n then h.1 k else 0) = h.1
        exact (H15_Hfun_congr r σr ω (cc := fun k => if hk : k ∈ H15_R n then h.1 k else 0) (cc' := h.1)
          (fun k hk => dite_eq_left hk)).trans (H15_Hfun_self hn ha hr1 σr _ ω h.1 h.2)
      right_inv := fun c => funext fun k => Subtype.ext (by
          show H15_Hfun r σr ω (fun k => if hk : k ∈ H15_R n then (c ⟨k, hk⟩).1 else 0) k.1 = (c k).1
          exact (H15_Hfun_R r σr ω _ k.2).trans (dite_eq_left k.2)) }
  calc Nat.card (topData n r σr (kappa n L) ω)
      = Nat.card ((k : H15_R n) → {c : L // c ^ (r + 1) = -kappa n L / H15_W r σr ω k.1}) := Nat.card_congr e
    _ = ∏ k : H15_R n, Nat.card {c : L // c ^ (r + 1) = -kappa n L / H15_W r σr ω k.1} := Nat.card_pi
    _ = ∏ _k : H15_R n, (r + 1) := Finset.prod_congr rfl (fun k _ =>
          H15_card_roots (by omega) hζ _ (div_ne_zero (neg_ne_zero.mpr hκ) (H15_W_ne r σr hω0 k.1)))
    _ = (r + 1) ^ (n / 4) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, H15_card_R h4]

/-- The data map `ŷ ↦ (ŷ|_{𝓛_a}, ŷ(-1), ŷ(1))`. -/
noncomputable def H15_Phi (h : ZMod n → L) : (ZMod n → L) × L × L :=
  (fun k => if Odd k.val then h k else 0, h (half n), h 0)

theorem H15_card_sq (c : L) (hc : c ≠ 0) (h2 : (2 : L) ≠ 0) {x0 : L} (hx0 : x0 ^ 2 = c) :
    Nat.card {x : L | x ^ 2 = c} = 2 := by
  have hset : {x : L | x ^ 2 = c} = {x0, -x0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [← hx0, sq_eq_sq_iff_eq_or_eq_neg]
  have hne : x0 ≠ -x0 := by
    intro h
    have h2x : 2 * x0 = 0 := by linear_combination h
    have hx00 : x0 = 0 := (mul_eq_zero.mp h2x).resolve_left h2
    apply hc
    rw [← hx0, hx00]
    ring
  rw [hset, Nat.card_coe_set_eq, Set.ncard_pair hne]

theorem H15_hmid_congr {t t' : ZMod n → L} (heq : ∀ ρ : ZMod n, Odd ρ.val → t ρ = t' ρ) (s0 : L) (x : ZMod n) :
    H15_hmid t s0 x = H15_hmid t' s0 x := by
  unfold H15_hmid H15_D
  congr 1
  refine Finset.prod_congr rfl fun ρ hρ => heq ρ ?_
  have := (Finset.mem_filter.mp hρ).1
  simpa [topLayer] using this

/-- The Fourier solutions for `n = 2^a`, `r ≡ -1`: `4 (r+1)^{n/4}` (top data × `S` × `ŷ(1) = ±n`). -/
theorem H15_card_F66 {a r : ℕ} [Fact r.Prime] [CharP L r] [IsAlgClosed L] (hn : n = 2 ^ a) (ha : 3 ≤ a)
    (hr : ¬ r ∣ pp n) (hr1 : r % 2 ^ a = 2 ^ a - 1) (σr : ℤ)
    (hsign : (-1 : ℤ) ^ σr.natAbs = legendreSym r (pp n : ℤ)) (ω : L) (hω : IsPrimitiveRoot ω n) :
    Nat.card ({h | F1 r σr ω h ∧ F3r (kappa n L) ω h ∧ F4 h} : Set (ZMod n → L)) = 4 * (r + 1) ^ (n / 4) := by
  have hn1 : n = 2 ^ a * 1 := by rw [hn, mul_one]
  have h4' : 2 ^ 2 ∣ n := H15_dvd_n hn1 (by omega)
  have h4 : 4 ∣ n := by simpa using h4'
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h4)
  have h2n : 2 ≤ n := Nat.le_of_dvd (NeZero.pos n) (dvd_trans (by norm_num) h4)
  have h2' : 2 ^ 1 ∣ n := H15_dvd_n hn1 (by omega)
  have hp : r.Prime := Fact.out
  have hrn := H15_hr66 hn ha hr hr1
  have hrodd : Odd r := H15_r_odd hn1 ha hrn
  have hκ : kappa n L ≠ 0 := H15_kappa_ne hrn
  have hn0 : (n : L) ≠ 0 := H15_n_ne hrn
  have h2L : (2 : L) ≠ 0 := H5_two_ne_zero r (fun h =>
    (Nat.not_even_iff_odd.mpr hrodd) ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h ▸ even_two))
  have hm0 : (half n : ZMod n) ≠ 0 := H15_half_ne_zero h2n
  have hnm : -(half n : ZMod n) = half n := by linear_combination -(H7_two_half hev)
  have hωm : (ω ^ (half n : ZMod n).val) ^ (n / 2) = 1 := by
    rw [H7_half_val, H7_pow_half_eq_neg_one hev hω]
    exact Even.neg_one_pow ⟨n / 4, by omega⟩
  have hsq : ∀ h : ZMod n → L, F3r (kappa n L) ω h → h (half n) ^ 2 = kappa n L := by
    intro h hF3
    have e := hF3.1 (half n) hm0
    rw [hnm, ← pow_two, hωm, mul_one] at e
    exact e
  have hbij : Set.BijOn H15_Phi {h | F1 r σr ω h ∧ F3r (kappa n L) ω h ∧ F4 h}
      (topData n r σr (kappa n L) ω ×ˢ ({s : L | s ^ 2 = kappa n L} ×ˢ {e : L | e ^ 2 = (n : L) ^ 2})) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro h ⟨hF1, hF3, hF4⟩
      refine ⟨⟨fun k hk => ?_, fun k hk => ?_⟩, hsq h hF3, hF3.2⟩
      · have hrko : Odd ((r : ZMod n) * k).val := H15_odd_transfer (H15_dvd_mul_odd h2' hrodd k) hk
        have hnko : Odd (-k).val := H15_odd_transfer (H15_dvd_neg h2' k) hk
        have hk0 : k ≠ 0 := by
          rintro rfl
          rw [ZMod.val_zero] at hk
          exact absurd hk (by decide)
        show (if Odd ((r : ZMod n) * k).val then h ((r : ZMod n) * k) else 0) =
            (ω ^ k.val) ^ ((r : ℤ) * σr) * (if Odd k.val then h k else 0) ^ r ∧
          (if Odd k.val then h k else 0) * (if Odd (-k).val then h (-k) else 0) =
            kappa n L * (ω ^ k.val) ^ (n / 2)
        rw [ite_eq_left hrko, ite_eq_left hk, ite_eq_left hnko]
        exact ⟨hF1 k, hF3.1 k hk0⟩
      · show (if Odd k.val then h k else 0) = 0
        rw [ite_eq_right (Nat.not_odd_iff_even.mpr hk)]
    · intro h1 hh1 h2 hh2 heq
      simp only [H15_Phi, Prod.mk.injEq] at heq
      obtain ⟨htop, hm, h0⟩ := heq
      have hodd_eq : ∀ ρ : ZMod n, Odd ρ.val → h1 ρ = h2 ρ := fun ρ hρ => by
        simpa [hρ] using congrFun htop ρ
      have hs2 := hsq h1 hh1.2.1
      have hs0 : h1 (half n) ≠ 0 := by
        intro h0'
        apply hκ
        rw [← hs2, h0']
        ring
      have hF4a : ∀ k, h1 k * h1 (k + half n) = h1 (half n) * h1 (2 * k) := hh1.2.2
      have hF4b : ∀ k, h2 k * h2 (k + half n) = h1 (half n) * h2 (2 * k) := fun k => by
        rw [hm]
        exact hh2.2.2 k
      funext x
      by_cases hx0 : x = 0
      · rw [hx0]
        exact h0
      · have hx : ¬ 2 ^ a ∣ x.val := fun h => hx0 ((H15_L0_iff hn x).mp h)
        rw [H15_descent hn1 ha h1 _ hF4a hs0 _ x hx rfl, H15_descent hn1 ha h2 _ hF4b hs0 _ x hx rfl]
        exact H15_hmid_congr hodd_eq _ x
    · rintro ⟨t, s, e⟩ ⟨ht, hs, he⟩
      have hsgn := H15_sgn hn1 ha odd_one hrn σr hsign ω hω t ht s hs
      have hf1 : (fun _ => (1 : L)) ∈ Gprime n a r σr (kappa n L) ω :=
        ⟨fun k hk => absurd ((H15_L0_iff hn k).mp ((H15_mem_layer0' k).mp hk).1) ((H15_mem_layer0' k).mp hk).2,
          fun k _ => rfl⟩
      have hE1 : ∀ α ∈ layer0' n a,
          (fun _ => (1 : L)) (2 * α) = s⁻¹ * H15_hmid t s (α + half n) * (fun _ => (1 : L)) α :=
        fun α hα => absurd ((H15_L0_iff hn α).mp ((H15_mem_layer0' α).mp hα).1) ((H15_mem_layer0' α).mp hα).2
      have he' : e ^ 2 = (n : L) ^ 2 := he
      have her : e ^ r = e := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp he' with h | h
        · rw [h, H15_natCast_pow_r]
        · rw [h, hrodd.neg_pow, H15_natCast_pow_r]
      refine ⟨H15_h a t s (fun _ => 1) e,
        H15_build hn1 ha odd_one hrn σr ω hω t ht s hs hsgn _ hf1 hE1 e he her, ?_⟩
      obtain ⟨hma, hhalf⟩ := H15_hmid_half hn1 ha odd_one hrn σr ω hω t ht s hs hsgn
      simp only [H15_Phi, Prod.mk.injEq]
      refine ⟨funext fun k => ?_, by rw [H15_h_mid t s _ e hma, hhalf], H15_h_zero a t s _ e⟩
      show (if Odd k.val then H15_h a t s (fun _ => 1) e k else 0) = t k
      by_cases hk : Odd k.val
      · rw [ite_eq_left hk]
        have hk' : ¬ 2 ^ a ∣ k.val := fun h => (Nat.not_even_iff_odd.mpr hk)
          (even_iff_two_dvd.mpr (dvd_trans (dvd_pow_self 2 (by omega)) h))
        rw [H15_h_mid t s _ e hk', H15_hmid_odd t s hk]
      · rw [ite_eq_right hk]
        exact (ht.2 k (Nat.not_odd_iff_even.mp hk)).symm
  rw [Nat.card_congr (hbij.equiv _), Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod,
    Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod, H15_topData_card hn ha hr hr1 σr ω hω]
  obtain ⟨s0, hs0⟩ := IsAlgClosed.exists_pow_nat_eq (kappa n L) two_pos
  rw [H15_card_sq _ hκ h2L hs0, H15_card_sq _ (pow_ne_zero 2 hn0) h2L rfl]
  ring

end Prop66

/-- Row 26(ii) — Proposition 6.6, second case, GIVEN the row sec_6_3_fourier (exact instance with `n_odd = 1`,
universally quantified over its remaining hypotheses and the field `L : Type`). -/
theorem prop_6_6_ii_of (n a r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a) (ha : 3 ≤ a) (hr : ¬ r ∣ pp n)
    (hr1 : r % 2 ^ a = 2 ^ a - 1) (σr : ℤ) (hsign : (-1 : ℤ) ^ σr.natAbs = legendreSym r (pp n : ℤ))
    (hFour : ∀ (_hn' : n = 2 ^ a * 1) (_hodd' : Odd 1) (_hr' : ¬ r ∣ pp n * n) (L : Type) [Field L]
      [Algebra (GaloisField r (n / Int.gcd σr n)) L] (ω : L) (_hω : IsPrimitiveRoot ω n),
      Set.BijOn (dftA ω) (NFrSet n r σr) {h | F1 r σr ω h ∧ F3r (kappa n L) ω h ∧ F4 h} ∧
        ∀ y ∈ NFrSet n r σr, S y ^ 2 = kappa n _) :
    Nat.card (NFrSet n r σr) = 4 * (r + 1) ^ (n / 4) := by
  have hrn := H15_hr66 hn ha hr hr1
  have hnF : ((n : ℕ) : AlgebraicClosure (GaloisField r (n / Int.gcd σr n))) ≠ 0 := H15_n_ne hrn
  have : NeZero ((n : ℕ) : AlgebraicClosure (GaloisField r (n / Int.gcd σr n))) := ⟨hnF⟩
  obtain ⟨ω, hω⟩ :=
    HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure (GaloisField r (n / Int.gcd σr n))) n
  rw [Nat.card_congr ((hFour (by rw [hn, mul_one]) odd_one hrn _ ω hω).1.equiv _)]
  exact H15_card_F66 hn ha hr hr1 σr hsign ω hω

/-! ## Orbit construction (Step 2 existence, Step 5 `G' ≠ ∅`): solve `f(rx) = W(x) f(x)^r`, `f(x)f(-x) = C(x)` -/

section OrbitSolve

open Classical

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

/-- `Ψ_0 = t`, `Ψ_{i+1} = W(r^i k) Ψ_i^r`: the values along the orbit of `k` forced by `f(rx) = W(x) f(x)^r`. -/
noncomputable def H15_Psi (r : ℕ) (W : ZMod n → L) (k : ZMod n) (t : L) : ℕ → L
  | 0 => t
  | i + 1 => W ((r : ZMod n) ^ i * k) * H15_Psi r W k t i ^ r

theorem H15_Psi_succ (r : ℕ) (W : ZMod n → L) (k : ZMod n) (t : L) (i : ℕ) :
    H15_Psi r W k t (i + 1) = W ((r : ZMod n) ^ i * k) * H15_Psi r W k t i ^ r := rfl

theorem H15_Psi_one_mul (r : ℕ) (W : ZMod n → L) (k : ZMod n) (t : L) (i : ℕ) :
    H15_Psi r W k t i = H15_Psi r W k 1 i * t ^ (r ^ i) := by
  induction i with
  | zero => simp [H15_Psi]
  | succ i ih =>
    rw [H15_Psi_succ, H15_Psi_succ, ih, mul_pow, ← pow_mul, ← pow_succ]
    ring

theorem H15_Psi_ne (r : ℕ) {W : ZMod n → L} (hW0 : ∀ x, W x ≠ 0) (k : ZMod n) {t : L} (ht : t ≠ 0) :
    ∀ i, H15_Psi r W k t i ≠ 0 := by
  intro i
  induction i with
  | zero => exact ht
  | succ i ih => exact mul_ne_zero (hW0 _) (pow_ne_zero _ ih)

theorem H15_per_exists {r : ℕ} (hcop : Nat.Coprime r n) (k : ZMod n) :
    ∃ i, 0 < i ∧ (r : ZMod n) ^ i * k = k := by
  obtain ⟨m, hm⟩ := H6_pow_period hcop
  exact ⟨m + 1, Nat.succ_pos m, by rw [hm, one_mul]⟩

/-- The length of the orbit of `k` (minimal period). -/
noncomputable def H15_per {r : ℕ} (hcop : Nat.Coprime r n) (k : ZMod n) : ℕ := Nat.find (H15_per_exists hcop k)

theorem H15_per_pos {r : ℕ} (hcop : Nat.Coprime r n) (k : ZMod n) : 0 < H15_per hcop k :=
  (Nat.find_spec (H15_per_exists hcop k)).1

theorem H15_per_spec {r : ℕ} (hcop : Nat.Coprime r n) (k : ZMod n) :
    (r : ZMod n) ^ H15_per hcop k * k = k :=
  (Nat.find_spec (H15_per_exists hcop k)).2

theorem H15_pow_mod_per {r : ℕ} (hcop : Nat.Coprime r n) (k : ZMod n) (i : ℕ) :
    (r : ZMod n) ^ (i % H15_per hcop k) * k = (r : ZMod n) ^ i * k := by
  have hq : ∀ q : ℕ, ((r : ZMod n) ^ H15_per hcop k) ^ q * k = k := by
    intro q
    induction q with
    | zero => simp
    | succ q ih => rw [pow_succ, mul_assoc, H15_per_spec, ih]
  conv_rhs => rw [← Nat.mod_add_div i (H15_per hcop k)]
  rw [pow_add, pow_mul, mul_assoc, hq]

theorem H15_pow_inj {r : ℕ} (hcop : Nat.Coprime r n) (k : ZMod n) {s s' : ℕ} (hs : s < H15_per hcop k)
    (hs' : s' < H15_per hcop k) (h : (r : ZMod n) ^ s * k = (r : ZMod n) ^ s' * k) : s = s' := by
  have hu : IsUnit (r : ZMod n) := (ZMod.isUnit_iff_coprime r n).mpr hcop
  have key : ∀ {p q : ℕ}, p < q → q < H15_per hcop k → (r : ZMod n) ^ p * k = (r : ZMod n) ^ q * k → False := by
    intro p q hpq hq e
    have e2 : (r : ZMod n) ^ p * ((r : ZMod n) ^ (q - p) * k) = (r : ZMod n) ^ p * k := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hpq.le]
      exact e.symm
    exact Nat.find_min (H15_per_exists hcop k) (by omega : q - p < H15_per hcop k)
      ⟨by omega, (hu.pow p).mul_left_cancel e2⟩
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact key hlt hs' h
  · exact key hlt hs h.symm

theorem H15_pow_eq_mod {r : ℕ} (hcop : Nat.Coprime r n) (k : ZMod n) {i j : ℕ}
    (h : (r : ZMod n) ^ i * k = (r : ZMod n) ^ j * k) : i % H15_per hcop k = j % H15_per hcop k := by
  apply H15_pow_inj hcop k (Nat.mod_lt _ (H15_per_pos hcop k)) (Nat.mod_lt _ (H15_per_pos hcop k))
  rw [H15_pow_mod_per, H15_pow_mod_per]
  exact h

theorem H15_Psi_mod {r : ℕ} (hcop : Nat.Coprime r n) (W : ZMod n → L) (k : ZMod n) (t : L)
    (hwrap : H15_Psi r W k t (H15_per hcop k) = t) (i : ℕ) :
    H15_Psi r W k t i = H15_Psi r W k t (i % H15_per hcop k) := by
  have hper : ∀ i, H15_Psi r W k t (i + H15_per hcop k) = H15_Psi r W k t i := by
    intro i
    induction i with
    | zero =>
      rw [zero_add]
      exact hwrap
    | succ i ih =>
      rw [show i + 1 + H15_per hcop k = (i + H15_per hcop k) + 1 by omega, H15_Psi_succ, H15_Psi_succ, ih,
        pow_add, mul_assoc, H15_per_spec]
  have key : ∀ q s, H15_Psi r W k t (s + H15_per hcop k * q) = H15_Psi r W k t s := by
    intro q
    induction q with
    | zero => intro s; simp
    | succ q ih =>
      intro s
      rw [show s + H15_per hcop k * (q + 1) = (s + H15_per hcop k * q) + H15_per hcop k by ring, hper, ih]
  conv_lhs => rw [← Nat.mod_add_div i (H15_per hcop k)]
  exact key _ _

/-- The orbit function: `x = r^i k ↦ Ψ_i` (well defined once `Ψ` wraps at the orbit length). -/
noncomputable def H15_orbF (r : ℕ) (W : ZMod n → L) (k : ZMod n) (t : L) (x : ZMod n) : L :=
  if h : ∃ i, x = (r : ZMod n) ^ i * k then H15_Psi r W k t (Nat.find h) else 0

theorem H15_orbF_pow {r : ℕ} (hcop : Nat.Coprime r n) (W : ZMod n → L) (k : ZMod n) (t : L)
    (hwrap : H15_Psi r W k t (H15_per hcop k) = t) (i : ℕ) :
    H15_orbF r W k t ((r : ZMod n) ^ i * k) = H15_Psi r W k t i := by
  have h : ∃ j, (r : ZMod n) ^ i * k = (r : ZMod n) ^ j * k := ⟨i, rfl⟩
  unfold H15_orbF
  rw [dite_eq_left h, H15_Psi_mod hcop W k t hwrap (Nat.find h), H15_Psi_mod hcop W k t hwrap i]
  congr 1
  exact (H15_pow_eq_mod hcop k (Nat.find_spec h)).symm

end OrbitSolve

section OrbitSolve2

open Classical

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

theorem H15_mul_div_cancel' (a b : L) (ha : a ≠ 0) : a * (b / a) = b := by
  rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self ha, mul_one]

theorem H15_pow_mem {r : ℕ} {A : Finset (ZMod n)} (hAu : ∀ x ∈ A, (r : ZMod n) * x ∈ A) {k : ZMod n}
    (hk : k ∈ A) : ∀ i, (r : ZMod n) ^ i * k ∈ A := by
  intro i
  induction i with
  | zero => simpa using hk
  | succ i ih =>
    rw [pow_succ', mul_assoc]
    exact hAu _ ih

theorem H15_orbit_back {r : ℕ} (hcop : Nat.Coprime r n) {c x : ZMod n} (h : (r : ZMod n) * x ∈ orbit r c) :
    x ∈ orbit r c := by
  obtain ⟨m, hm⟩ := H6_pow_period hcop
  obtain ⟨i, hi⟩ := H6_mem_orbit.mp h
  refine H6_mem_orbit.mpr ⟨m + i, ?_⟩
  calc x = (r : ZMod n) ^ (m + 1) * x := by rw [hm, one_mul]
    _ = (r : ZMod n) ^ m * ((r : ZMod n) * x) := by ring
    _ = (r : ZMod n) ^ (m + i) * c := by rw [hi]; ring

theorem H15_orbit_mul {r : ℕ} {c x : ZMod n} (h : x ∈ orbit r c) : (r : ZMod n) * x ∈ orbit r c := by
  obtain ⟨i, rfl⟩ := H6_mem_orbit.mp h
  exact H6_mem_orbit.mpr ⟨i + 1, by ring⟩

/-- The function on a non-self-inverse block: `Ψ` on `O`, `C/·` on `O^{-1}`. -/
noncomputable def H15_g1 (r : ℕ) (W C : ZMod n → L) (k : ZMod n) (t : L) (x : ZMod n) : L :=
  if x ∈ orbit r k then H15_orbF r W k t x else C x / H15_orbF r W k t (-x)

/-- One block `O ∪ O^{-1}` (self-inverse or not) carries a solution. -/
theorem H15_block {r : ℕ} (hcop : Nat.Coprime r n) (hr2 : 2 ≤ r) [IsAlgClosed L] (W C : ZMod n → L)
    (hW0 : ∀ x, W x ≠ 0) (hWW : ∀ x, W x * W (-x) = 1) (hC0 : ∀ x, C x ≠ 0) (hCn : ∀ x, C (-x) = C x)
    (hCu : ∀ x, C ((r : ZMod n) * x) = C x ^ r) (k : ZMod n) (hk : -k ≠ k) :
    ∃ g : ZMod n → L, ∀ x ∈ orbit r k ∪ orbit r (-k),
      g ((r : ZMod n) * x) = W x * g x ^ r ∧ g x * g (-x) = C x := by
  by_cases hself : -k ∈ orbit r k
  · -- self-inverse orbit: `-k = r^{h0} k`, one root of `t^{1+r^{h0}} = C(k)/A`
    have hex : ∃ i, -k = (r : ZMod n) ^ i * k := H6_mem_orbit.mp hself
    obtain ⟨h0, hh0, hmin⟩ : ∃ h0, -k = (r : ZMod n) ^ h0 * k ∧ ∀ j, -k = (r : ZMod n) ^ j * k → h0 ≤ j :=
      ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min' hex hj⟩
    have hh00 : h0 ≠ 0 := by
      rintro rfl
      rw [pow_zero, one_mul] at hh0
      exact hk hh0
    have hA1 := H15_Psi_ne r hW0 k one_ne_zero h0
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (C k / H15_Psi r W k 1 h0) (by positivity : 0 < 1 + r ^ h0)
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [zero_pow (by positivity)] at ht
      exact div_ne_zero (hC0 k) hA1 ht.symm
    have hb0 : t * H15_Psi r W k t h0 = C k := by
      rw [H15_Psi_one_mul r W k t h0]
      calc t * (H15_Psi r W k 1 h0 * t ^ (r ^ h0)) = H15_Psi r W k 1 h0 * t ^ (1 + r ^ h0) := by ring
        _ = H15_Psi r W k 1 h0 * (C k / H15_Psi r W k 1 h0) := by rw [ht]
        _ = C k := H15_mul_div_cancel' _ _ hA1
    have hneg_i : ∀ i, (r : ZMod n) ^ (i + h0) * k = -((r : ZMod n) ^ i * k) := by
      intro i
      rw [pow_add, mul_assoc, ← hh0]
      ring
    have hb : ∀ i, H15_Psi r W k t i * H15_Psi r W k t (i + h0) = C ((r : ZMod n) ^ i * k) := by
      intro i
      induction i with
      | zero =>
        rw [zero_add, pow_zero, one_mul]
        exact hb0
      | succ i ih =>
        rw [show i + 1 + h0 = (i + h0) + 1 by omega, H15_Psi_succ, H15_Psi_succ, hneg_i i,
          show (r : ZMod n) ^ (i + 1) * k = (r : ZMod n) * ((r : ZMod n) ^ i * k) by ring, hCu, ← ih]
        calc W ((r : ZMod n) ^ i * k) * H15_Psi r W k t i ^ r *
              (W (-((r : ZMod n) ^ i * k)) * H15_Psi r W k t (i + h0) ^ r)
            = (W ((r : ZMod n) ^ i * k) * W (-((r : ZMod n) ^ i * k))) *
                (H15_Psi r W k t i * H15_Psi r W k t (i + h0)) ^ r := by ring
          _ = _ := by rw [hWW, one_mul]
    -- the orbit length is `2 h0`, and `Ψ` wraps there
    have hper2 : (r : ZMod n) ^ (2 * h0) * k = k := by
      rw [two_mul, hneg_i h0, ← hh0, neg_neg]
    have hlt : h0 < H15_per hcop k := by
      have := hmin (h0 % H15_per hcop k) (by rw [H15_pow_mod_per]; exact hh0)
      have := Nat.mod_lt h0 (H15_per_pos hcop k)
      omega
    have hle : H15_per hcop k ≤ 2 * h0 := Nat.find_min' _ ⟨by omega, hper2⟩
    have hdvd : H15_per hcop k ∣ 2 * h0 := by
      have e := H15_pow_eq_mod hcop k (i := 2 * h0) (j := 0) (by rw [hper2, pow_zero, one_mul])
      rw [Nat.zero_mod] at e
      exact Nat.dvd_of_mod_eq_zero e
    have hP : H15_per hcop k = h0 + h0 := by
      obtain ⟨c, hc⟩ := hdvd
      rcases c with _ | _ | c
      · omega
      · omega
      · have := Nat.mul_le_mul_left (H15_per hcop k) (show 2 ≤ c + 1 + 1 by omega)
        omega
    have hΨh0 := H15_Psi_ne r hW0 k ht0 h0
    have e1 := hb 0
    rw [zero_add, pow_zero, one_mul] at e1
    have e2 := hb h0
    rw [← hh0, hCn] at e2
    have hwrap : H15_Psi r W k t (H15_per hcop k) = t := by
      rw [hP]
      exact mul_left_cancel₀ hΨh0 (e2.trans (e1.symm.trans (mul_comm _ _)))
    have horb : orbit r (-k) = orbit r k := H6_orbit_eq hcop hself
    refine ⟨H15_orbF r W k t, fun x hx => ?_⟩
    have hxk : x ∈ orbit r k := by
      rcases Finset.mem_union.mp hx with h | h
      · exact h
      · rwa [horb] at h
    obtain ⟨i, rfl⟩ := H6_mem_orbit.mp hxk
    constructor
    · rw [show (r : ZMod n) * ((r : ZMod n) ^ i * k) = (r : ZMod n) ^ (i + 1) * k by ring,
        H15_orbF_pow hcop W k t hwrap, H15_orbF_pow hcop W k t hwrap, H15_Psi_succ]
    · rw [← hneg_i i, H15_orbF_pow hcop W k t hwrap, H15_orbF_pow hcop W k t hwrap]
      exact hb i
  · -- `O ≠ O^{-1}`: a root of the wrap `t^{r^L - 1} = 1/A` on `O`, then `C/·` on `O^{-1}`
    have hper0 := H15_per_pos hcop k
    have hA := H15_Psi_ne r hW0 k one_ne_zero (H15_per hcop k)
    have hN : 0 < r ^ H15_per hcop k - 1 := by
      have := Nat.one_lt_pow (Nat.pos_iff_ne_zero.mp hper0) (by omega : 1 < r)
      omega
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (H15_Psi r W k 1 (H15_per hcop k))⁻¹ hN
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega)] at ht
      exact inv_ne_zero hA ht.symm
    have hwrap : H15_Psi r W k t (H15_per hcop k) = t := by
      rw [H15_Psi_one_mul r W k t]
      have hsplit : r ^ H15_per hcop k = (r ^ H15_per hcop k - 1) + 1 := by omega
      rw [hsplit, pow_succ, ht, ← mul_assoc, mul_inv_cancel₀ hA, one_mul]
    have hne : ∀ i, H15_orbF r W k t ((r : ZMod n) ^ i * k) ≠ 0 := fun i => by
      rw [H15_orbF_pow hcop W k t hwrap]
      exact H15_Psi_ne r hW0 k ht0 i
    have hnot : ∀ x ∈ orbit r k, -x ∉ orbit r k := by
      intro x hx hnx
      apply hself
      have h1 : orbit r (-x) = orbit r k := H6_orbit_eq hcop hnx
      have h2 : orbit r (-x) = orbit r (-k) := H6_orbit_eq hcop (H6_neg_mem hx)
      rw [← h1, h2]
      exact H6_self_mem r (-k)
    have hin : ∀ x ∈ orbit r k, H15_g1 r W C k t x = H15_orbF r W k t x := fun x hx => by
      unfold H15_g1
      rw [ite_eq_left hx]
    have hout : ∀ x ∉ orbit r k, H15_g1 r W C k t x = C x / H15_orbF r W k t (-x) := fun x hx => by
      unfold H15_g1
      rw [ite_eq_right hx]
    refine ⟨H15_g1 r W C k t, fun x hx => ?_⟩
    by_cases hxk : x ∈ orbit r k
    · have hnx := hnot x hxk
      have hrx := H15_orbit_mul hxk
      rw [hin _ hrx, hin x hxk, hout _ hnx, neg_neg]
      obtain ⟨i, rfl⟩ := H6_mem_orbit.mp hxk
      constructor
      · rw [show (r : ZMod n) * ((r : ZMod n) ^ i * k) = (r : ZMod n) ^ (i + 1) * k by ring,
          H15_orbF_pow hcop W k t hwrap, H15_orbF_pow hcop W k t hwrap, H15_Psi_succ]
      · rw [hCn]
        exact H15_mul_div_cancel' _ _ (hne i)
    · have hxk' : x ∈ orbit r (-k) := by
        rcases Finset.mem_union.mp hx with h | h
        · exact absurd h hxk
        · exact h
      have hnxk : -x ∈ orbit r k := by
        have := H6_neg_mem hxk'
        rwa [neg_neg] at this
      have hrx : (r : ZMod n) * x ∉ orbit r k := fun h => hxk (H15_orbit_back hcop h)
      obtain ⟨i, hi⟩ := H6_mem_orbit.mp hnxk
      have hnrx : -((r : ZMod n) * x) = (r : ZMod n) ^ (i + 1) * k := by
        rw [pow_succ', mul_assoc, ← hi]
        ring
      rw [hout _ hrx, hout x hxk, hin _ hnxk, hnrx, hi, H15_orbF_pow hcop W k t hwrap,
        H15_orbF_pow hcop W k t hwrap, H15_Psi_succ, ← hi]
      constructor
      · rw [hCu, div_pow, eq_inv_of_mul_eq_one_left (hWW x)]
        ring
      · exact div_mul_cancel₀ _ (H15_Psi_ne r hW0 k ht0 i)

/-- Solutions of `f(rx) = W(x) f(x)^r`, `f(x)f(-x) = C(x)` on any finite set closed under `x ↦ rx`, `x ↦ -x`
without fixed points of `x ↦ -x` (algebraically closed `L`). -/
theorem H15_orbit_solve {r : ℕ} (hcop : Nat.Coprime r n) (hr2 : 2 ≤ r) [IsAlgClosed L] (W C : ZMod n → L)
    (hW0 : ∀ x, W x ≠ 0) (hWW : ∀ x, W x * W (-x) = 1) (hC0 : ∀ x, C x ≠ 0) (hCn : ∀ x, C (-x) = C x)
    (hCu : ∀ x, C ((r : ZMod n) * x) = C x ^ r) (A : Finset (ZMod n)) :
    (∀ x ∈ A, (r : ZMod n) * x ∈ A) → (∀ x ∈ A, -x ∈ A) → (∀ x ∈ A, -x ≠ x) →
      ∃ f : ZMod n → L, ∀ x ∈ A, f ((r : ZMod n) * x) = W x * f x ^ r ∧ f x * f (-x) = C x := by
  refine Finset.strongInduction (p := fun A => (∀ x ∈ A, (r : ZMod n) * x ∈ A) → (∀ x ∈ A, -x ∈ A) →
    (∀ x ∈ A, -x ≠ x) → ∃ f : ZMod n → L, ∀ x ∈ A, f ((r : ZMod n) * x) = W x * f x ^ r ∧ f x * f (-x) = C x)
    (fun A ih => ?_) A
  intro hAu hAn hAne
  rcases A.eq_empty_or_nonempty with hA | ⟨k, hk⟩
  · exact ⟨fun _ => 1, fun x hx => by simp [hA] at hx⟩
  · have hBu : ∀ x ∈ orbit r k ∪ orbit r (-k), (r : ZMod n) * x ∈ orbit r k ∪ orbit r (-k) := by
      intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · exact Finset.mem_union_left _ (H15_orbit_mul h)
      · exact Finset.mem_union_right _ (H15_orbit_mul h)
    have hBn : ∀ x ∈ orbit r k ∪ orbit r (-k), -x ∈ orbit r k ∪ orbit r (-k) := by
      intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · exact Finset.mem_union_right _ (H6_neg_mem h)
      · have := H6_neg_mem h
        rw [neg_neg] at this
        exact Finset.mem_union_left _ this
    have hBback : ∀ x, (r : ZMod n) * x ∈ orbit r k ∪ orbit r (-k) → x ∈ orbit r k ∪ orbit r (-k) := by
      intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · exact Finset.mem_union_left _ (H15_orbit_back hcop h)
      · exact Finset.mem_union_right _ (H15_orbit_back hcop h)
    have hBnback : ∀ x, -x ∈ orbit r k ∪ orbit r (-k) → x ∈ orbit r k ∪ orbit r (-k) := by
      intro x hx
      have := hBn _ hx
      rwa [neg_neg] at this
    have hBA : orbit r k ∪ orbit r (-k) ⊆ A := by
      intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · obtain ⟨i, rfl⟩ := H6_mem_orbit.mp h
        exact H15_pow_mem hAu hk i
      · obtain ⟨i, rfl⟩ := H6_mem_orbit.mp h
        exact H15_pow_mem hAu (hAn k hk) i
    have hss : A \ (orbit r k ∪ orbit r (-k)) ⊂ A :=
      Finset.sdiff_ssubset hBA ⟨k, Finset.mem_union_left _ (H6_self_mem r k)⟩
    obtain ⟨f', hf'⟩ := ih _ hss
      (fun x hx => by
        obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
        exact Finset.mem_sdiff.mpr ⟨hAu x h1, fun h => h2 (hBback x h)⟩)
      (fun x hx => by
        obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
        exact Finset.mem_sdiff.mpr ⟨hAn x h1, fun h => h2 (hBnback x h)⟩)
      (fun x hx => hAne x (Finset.mem_sdiff.mp hx).1)
    obtain ⟨g, hg⟩ := H15_block hcop hr2 W C hW0 hWW hC0 hCn hCu k (hAne k hk)
    refine ⟨fun x => if x ∈ orbit r k ∪ orbit r (-k) then g x else f' x, fun x hx => ?_⟩
    by_cases hxB : x ∈ orbit r k ∪ orbit r (-k)
    · have h1 := hBu x hxB
      have h2 := hBn x hxB
      simp only [ite_eq_left hxB, ite_eq_left h1, ite_eq_left h2]
      exact hg x hxB
    · have hxA' : x ∈ A \ (orbit r k ∪ orbit r (-k)) := Finset.mem_sdiff.mpr ⟨hx, hxB⟩
      have h1 : (r : ZMod n) * x ∉ orbit r k ∪ orbit r (-k) := fun h => hxB (hBback x h)
      have h2 : -x ∉ orbit r k ∪ orbit r (-k) := fun h => hxB (hBnback x h)
      simp only [ite_eq_right hxB, ite_eq_right h1, ite_eq_right h2]
      exact hf' x hxA'

end OrbitSolve2

/-! ## Step 2 (the count): solutions on a closed set split over the blocks; a block `O ∪ O^{-1}` has `r^L - 1` -/

section Count

open Classical

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

/-- Solutions of the block laws on `A`, with the fixed value `z` off `A`. -/
def H15_Sol (r : ℕ) (W C : ZMod n → L) (z : L) (A : Finset (ZMod n)) : Set (ZMod n → L) :=
  {f | (∀ x ∈ A, f ((r : ZMod n) * x) = W x * f x ^ r ∧ f x * f (-x) = C x) ∧ ∀ x ∉ A, f x = z}

/-- The pair `{O, O^{-1}}` of the orbit of `x`. -/
noncomputable def H15_pairOf (r : ℕ) (x : ZMod n) : Finset (Finset (ZMod n)) := {orbit r x, orbit r (-x)}

theorem H15_B_mul {r : ℕ} {k x : ZMod n} (hx : x ∈ orbit r k ∪ orbit r (-k)) :
    (r : ZMod n) * x ∈ orbit r k ∪ orbit r (-k) := by
  rcases Finset.mem_union.mp hx with h | h
  · exact Finset.mem_union_left _ (H15_orbit_mul h)
  · exact Finset.mem_union_right _ (H15_orbit_mul h)

theorem H15_B_neg {r : ℕ} {k x : ZMod n} (hx : x ∈ orbit r k ∪ orbit r (-k)) : -x ∈ orbit r k ∪ orbit r (-k) := by
  rcases Finset.mem_union.mp hx with h | h
  · exact Finset.mem_union_right _ (H6_neg_mem h)
  · have := H6_neg_mem h
    rw [neg_neg] at this
    exact Finset.mem_union_left _ this

theorem H15_B_back {r : ℕ} (hcop : Nat.Coprime r n) {k x : ZMod n}
    (hx : (r : ZMod n) * x ∈ orbit r k ∪ orbit r (-k)) : x ∈ orbit r k ∪ orbit r (-k) := by
  rcases Finset.mem_union.mp hx with h | h
  · exact Finset.mem_union_left _ (H15_orbit_back hcop h)
  · exact Finset.mem_union_right _ (H15_orbit_back hcop h)

theorem H15_B_nback {r : ℕ} {k x : ZMod n} (hx : -x ∈ orbit r k ∪ orbit r (-k)) : x ∈ orbit r k ∪ orbit r (-k) := by
  have := H15_B_neg hx
  rwa [neg_neg] at this

theorem H15_orbit_card {r : ℕ} (hcop : Nat.Coprime r n) (k : ZMod n) : (orbit r k).card = H15_per hcop k := by
  have himg : orbit r k = (Finset.range (H15_per hcop k)).image (fun i => (r : ZMod n) ^ i * k) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_range, H6_mem_orbit]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i % H15_per hcop k, Nat.mod_lt _ (H15_per_pos hcop k), H15_pow_mod_per hcop k i⟩
    · rintro ⟨i, -, rfl⟩
      exact ⟨i, rfl⟩
  rw [himg, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  exact H15_pow_inj hcop k (Finset.mem_range.mp (Finset.mem_coe.mp hi)) (Finset.mem_range.mp (Finset.mem_coe.mp hj)) hij

theorem H15_pairLen {r : ℕ} (hcop : Nat.Coprime r n) (k : ZMod n) (hself : -k ∉ orbit r k) :
    pairLen (H15_pairOf r k) = H15_per hcop k := by
  have hdisj : Disjoint (orbit r k) (orbit r (-k)) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    apply hself
    have h1 := H6_orbit_eq hcop hz
    have h2 := H6_orbit_eq hcop hz'
    rw [← h1, h2]
    exact H6_self_mem r (-k)
  unfold pairLen H15_pairOf
  rw [show (({orbit r k, orbit r (-k)} : Finset (Finset (ZMod n))).biUnion id) = orbit r k ∪ orbit r (-k) by
      simp [Finset.biUnion_insert],
    Finset.card_union_of_disjoint hdisj, ← H6_inv_orbit, H6_card_inv, H15_orbit_card hcop k]
  omega

theorem H15_g1_laws {r : ℕ} (hcop : Nat.Coprime r n) (W C : ZMod n → L)
    (hW0 : ∀ x, W x ≠ 0) (hWW : ∀ x, W x * W (-x) = 1) (hCn : ∀ x, C (-x) = C x)
    (hCu : ∀ x, C ((r : ZMod n) * x) = C x ^ r) (k : ZMod n) (hself : -k ∉ orbit r k) (t : L) (ht0 : t ≠ 0)
    (hwrap : H15_Psi r W k t (H15_per hcop k) = t) :
    ∀ x ∈ orbit r k ∪ orbit r (-k), H15_g1 r W C k t ((r : ZMod n) * x) = W x * H15_g1 r W C k t x ^ r ∧
      H15_g1 r W C k t x * H15_g1 r W C k t (-x) = C x := by
  have hne : ∀ i, H15_orbF r W k t ((r : ZMod n) ^ i * k) ≠ 0 := fun i => by
    rw [H15_orbF_pow hcop W k t hwrap]
    exact H15_Psi_ne r hW0 k ht0 i
  have hnot : ∀ x ∈ orbit r k, -x ∉ orbit r k := by
    intro x hx hnx
    apply hself
    have h1 : orbit r (-x) = orbit r k := H6_orbit_eq hcop hnx
    have h2 : orbit r (-x) = orbit r (-k) := H6_orbit_eq hcop (H6_neg_mem hx)
    rw [← h1, h2]
    exact H6_self_mem r (-k)
  have hin : ∀ x ∈ orbit r k, H15_g1 r W C k t x = H15_orbF r W k t x := fun x hx => by
    unfold H15_g1
    rw [ite_eq_left hx]
  have hout : ∀ x ∉ orbit r k, H15_g1 r W C k t x = C x / H15_orbF r W k t (-x) := fun x hx => by
    unfold H15_g1
    rw [ite_eq_right hx]
  intro x hx
  by_cases hxk : x ∈ orbit r k
  · have hnx := hnot x hxk
    have hrx := H15_orbit_mul hxk
    rw [hin _ hrx, hin x hxk, hout _ hnx, neg_neg]
    obtain ⟨i, rfl⟩ := H6_mem_orbit.mp hxk
    constructor
    · rw [show (r : ZMod n) * ((r : ZMod n) ^ i * k) = (r : ZMod n) ^ (i + 1) * k by ring,
        H15_orbF_pow hcop W k t hwrap, H15_orbF_pow hcop W k t hwrap, H15_Psi_succ]
    · rw [hCn]
      exact H15_mul_div_cancel' _ _ (hne i)
  · have hxk' : x ∈ orbit r (-k) := by
      rcases Finset.mem_union.mp hx with h | h
      · exact absurd h hxk
      · exact h
    have hnxk : -x ∈ orbit r k := by
      have := H6_neg_mem hxk'
      rwa [neg_neg] at this
    have hrx : (r : ZMod n) * x ∉ orbit r k := fun h => hxk (H15_orbit_back hcop h)
    obtain ⟨i, hi⟩ := H6_mem_orbit.mp hnxk
    have hnrx : -((r : ZMod n) * x) = (r : ZMod n) ^ (i + 1) * k := by
      rw [pow_succ', mul_assoc, ← hi]
      ring
    rw [hout _ hrx, hout x hxk, hin _ hnxk, hnrx, hi, H15_orbF_pow hcop W k t hwrap,
      H15_orbF_pow hcop W k t hwrap, H15_Psi_succ, ← hi]
    constructor
    · rw [hCu, div_pow, eq_inv_of_mul_eq_one_left (hWW x)]
      ring
    · exact div_mul_cancel₀ _ (H15_Psi_ne r hW0 k ht0 i)

/-- A non-self-inverse block carries exactly `r^L - 1` solutions (`L` the orbit length). -/
theorem H15_count_block {r : ℕ} [Fact r.Prime] [CharP L r] [IsAlgClosed L] (hcop : Nat.Coprime r n)
    (W C : ZMod n → L) (z : L) (hW0 : ∀ x, W x ≠ 0) (hWW : ∀ x, W x * W (-x) = 1) (hC0 : ∀ x, C x ≠ 0)
    (hCn : ∀ x, C (-x) = C x) (hCu : ∀ x, C ((r : ZMod n) * x) = C x ^ r) (k : ZMod n)
    (hself : -k ∉ orbit r k) :
    Nat.card (H15_Sol r W C z (orbit r k ∪ orbit r (-k))) = r ^ H15_per hcop k - 1 := by
  have hp : r.Prime := Fact.out
  have hper0 := H15_per_pos hcop k
  have hA := H15_Psi_ne r hW0 k one_ne_zero (H15_per hcop k)
  have hN : 0 < r ^ H15_per hcop k - 1 := by
    have := Nat.one_lt_pow (Nat.pos_iff_ne_zero.mp hper0) hp.one_lt
    omega
  have hNL : ((r ^ H15_per hcop k - 1 : ℕ) : L) ≠ 0 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hp.pos), Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega),
      Nat.cast_one, zero_sub]
    exact neg_ne_zero.mpr one_ne_zero
  have : NeZero ((r ^ H15_per hcop k - 1 : ℕ) : L) := ⟨hNL⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot L (r ^ H15_per hcop k - 1)
  rw [← H15_card_roots hN hζ (H15_Psi r W k 1 (H15_per hcop k))⁻¹ (inv_ne_zero hA)]
  have hkB : k ∈ orbit r k ∪ orbit r (-k) := Finset.mem_union_left _ (H6_self_mem r k)
  have hsplit : r ^ H15_per hcop k = (r ^ H15_per hcop k - 1) + 1 := by omega
  -- a root gives the wrap
  have hwrap_of : ∀ t : L, t ^ (r ^ H15_per hcop k - 1) = (H15_Psi r W k 1 (H15_per hcop k))⁻¹ →
      H15_Psi r W k t (H15_per hcop k) = t := by
    intro t ht
    rw [H15_Psi_one_mul r W k t, hsplit, pow_succ, ht, ← mul_assoc, mul_inv_cancel₀ hA, one_mul]
  have hroot_ne : ∀ t : L, t ^ (r ^ H15_per hcop k - 1) = (H15_Psi r W k 1 (H15_per hcop k))⁻¹ → t ≠ 0 := by
    intro t ht h0
    rw [h0, zero_pow (by omega)] at ht
    exact inv_ne_zero hA ht.symm
  -- a solution is determined along the orbit by its value at `k`
  have hfE2 : ∀ f ∈ H15_Sol r W C z (orbit r k ∪ orbit r (-k)), ∀ i,
      f ((r : ZMod n) ^ i * k) = H15_Psi r W k (f k) i := by
    intro f hf i
    induction i with
    | zero => simp [H15_Psi]
    | succ i ih =>
      have hmem : (r : ZMod n) ^ i * k ∈ orbit r k ∪ orbit r (-k) :=
        Finset.mem_union_left _ (H6_mem_orbit.mpr ⟨i, rfl⟩)
      rw [show (r : ZMod n) ^ (i + 1) * k = (r : ZMod n) * ((r : ZMod n) ^ i * k) by ring, (hf.1 _ hmem).1, ih,
        H15_Psi_succ]
  have hfk0 : ∀ f ∈ H15_Sol r W C z (orbit r k ∪ orbit r (-k)), f k ≠ 0 := by
    intro f hf h0
    have e := (hf.1 k hkB).2
    rw [h0, zero_mul] at e
    exact hC0 k e.symm
  have hroot : ∀ f ∈ H15_Sol r W C z (orbit r k ∪ orbit r (-k)),
      f k ^ (r ^ H15_per hcop k - 1) = (H15_Psi r W k 1 (H15_per hcop k))⁻¹ := by
    intro f hf
    have e := hfE2 f hf (H15_per hcop k)
    rw [H15_per_spec, H15_Psi_one_mul r W k (f k), hsplit, pow_succ] at e
    apply eq_inv_of_mul_eq_one_right
    apply mul_right_cancel₀ (hfk0 f hf)
    rw [one_mul]
    calc H15_Psi r W k 1 (H15_per hcop k) * f k ^ (r ^ H15_per hcop k - 1) * f k
        = H15_Psi r W k 1 (H15_per hcop k) * (f k ^ (r ^ H15_per hcop k - 1) * f k) := by ring
      _ = f k := e.symm
  apply Nat.card_congr
  exact
    { toFun := fun f => ⟨f.1 k, hroot f.1 f.2⟩
      invFun := fun t => ⟨fun x => if x ∈ orbit r k ∪ orbit r (-k) then H15_g1 r W C k t.1 x else z, by
        have hlaws := H15_g1_laws hcop W C hW0 hWW hCn hCu k hself t.1 (hroot_ne t.1 t.2) (hwrap_of t.1 t.2)
        refine ⟨fun x hx => ?_, fun x hx => ?_⟩
        · simp only [ite_eq_left hx, ite_eq_left (H15_B_mul hx), ite_eq_left (H15_B_neg hx)]
          exact hlaws x hx
        · simp only [ite_eq_right hx]⟩
      left_inv := fun f => by
        apply Subtype.ext
        funext x
        show (if x ∈ orbit r k ∪ orbit r (-k) then H15_g1 r W C k (f.1 k) x else z) = f.1 x
        have hw := hwrap_of (f.1 k) (hroot f.1 f.2)
        by_cases hx : x ∈ orbit r k ∪ orbit r (-k)
        · rw [ite_eq_left hx]
          unfold H15_g1
          by_cases hxk : x ∈ orbit r k
          · rw [ite_eq_left hxk]
            obtain ⟨i, rfl⟩ := H6_mem_orbit.mp hxk
            rw [H15_orbF_pow hcop W k _ hw, hfE2 f.1 f.2 i]
          · rw [ite_eq_right hxk]
            have hxk' : x ∈ orbit r (-k) := by
              rcases Finset.mem_union.mp hx with h | h
              · exact absurd h hxk
              · exact h
            have hnxk : -x ∈ orbit r k := by
              have := H6_neg_mem hxk'
              rwa [neg_neg] at this
            obtain ⟨i, hi⟩ := H6_mem_orbit.mp hnxk
            have hfnx : f.1 (-x) = H15_Psi r W k (f.1 k) i := by rw [hi, hfE2 f.1 f.2 i]
            have hfnx0 : f.1 (-x) ≠ 0 := by
              rw [hfnx]
              exact H15_Psi_ne r hW0 k (hfk0 f.1 f.2) i
            rw [hi, H15_orbF_pow hcop W k _ hw, ← hfE2 f.1 f.2 i, ← hi, ← (f.2.1 x hx).2, mul_div_assoc,
              div_self hfnx0, mul_one]
        · rw [ite_eq_right hx]
          exact (f.2.2 x hx).symm
      right_inv := fun t => by
        apply Subtype.ext
        show (if k ∈ orbit r k ∪ orbit r (-k) then H15_g1 r W C k t.1 k else z) = t.1
        rw [ite_eq_left hkB]
        unfold H15_g1
        rw [ite_eq_left (H6_self_mem r k)]
        have := H15_orbF_pow hcop W k t.1 (hwrap_of t.1 t.2) 0
        rw [pow_zero, one_mul] at this
        exact this }

/-- Solutions on `A` split as (solutions on a block `B`) × (solutions on `A \ B`). -/
theorem H15_sol_split {r : ℕ} (W C : ZMod n → L) (z : L) (A B : Finset (ZMod n)) (hBA : B ⊆ A)
    (hBu : ∀ x ∈ B, (r : ZMod n) * x ∈ B) (hBn : ∀ x ∈ B, -x ∈ B)
    (hBback : ∀ x, (r : ZMod n) * x ∈ B → x ∈ B) (hBnback : ∀ x, -x ∈ B → x ∈ B) :
    Nat.card (H15_Sol r W C z A) = Nat.card (H15_Sol r W C z B) * Nat.card (H15_Sol r W C z (A \ B)) := by
  rw [← Nat.card_prod]
  apply Nat.card_congr
  exact
    { toFun := fun f => (⟨fun x => if x ∈ B then f.1 x else z, by
          refine ⟨fun x hx => ?_, fun x hx => ?_⟩
          · simp only [ite_eq_left hx, ite_eq_left (hBu x hx), ite_eq_left (hBn x hx)]
            exact f.2.1 x (hBA hx)
          · simp only [ite_eq_right hx]⟩,
        ⟨fun x => if x ∈ B then z else f.1 x, by
          refine ⟨fun x hx => ?_, fun x hx => ?_⟩
          · obtain ⟨hxA, hxB⟩ := Finset.mem_sdiff.mp hx
            have h1 : (r : ZMod n) * x ∉ B := fun h => hxB (hBback x h)
            have h2 : -x ∉ B := fun h => hxB (hBnback x h)
            simp only [ite_eq_right hxB, ite_eq_right h1, ite_eq_right h2]
            exact f.2.1 x hxA
          · by_cases hxB : x ∈ B
            · simp only [ite_eq_left hxB]
            · simp only [ite_eq_right hxB]
              exact f.2.2 x (fun hxA => hx (Finset.mem_sdiff.mpr ⟨hxA, hxB⟩))⟩)
      invFun := fun p => ⟨fun x => if x ∈ B then p.1.1 x else p.2.1 x, by
        refine ⟨fun x hx => ?_, fun x hx => ?_⟩
        · by_cases hxB : x ∈ B
          · simp only [ite_eq_left hxB, ite_eq_left (hBu x hxB), ite_eq_left (hBn x hxB)]
            exact p.1.2.1 x hxB
          · have hx' : x ∈ A \ B := Finset.mem_sdiff.mpr ⟨hx, hxB⟩
            have h1 : (r : ZMod n) * x ∉ B := fun h => hxB (hBback x h)
            have h2 : -x ∉ B := fun h => hxB (hBnback x h)
            simp only [ite_eq_right hxB, ite_eq_right h1, ite_eq_right h2]
            exact p.2.2.1 x hx'
        · have hxB : x ∉ B := fun h => hx (hBA h)
          simp only [ite_eq_right hxB]
          exact p.2.2.2 x (fun h => hx (Finset.mem_sdiff.mp h).1)⟩
      left_inv := fun f => by
        apply Subtype.ext
        funext x
        by_cases hxB : x ∈ B <;> simp [hxB]
      right_inv := fun p => by
        refine Prod.ext (Subtype.ext (funext fun x => ?_)) (Subtype.ext (funext fun x => ?_))
        · by_cases hxB : x ∈ B
          · simp [hxB]
          · simp only [hxB, ite_false]
            exact (p.1.2.2 x hxB).symm
        · by_cases hxB : x ∈ B
          · simp only [hxB, ite_true]
            exact (p.2.2.2 x (fun h => (Finset.mem_sdiff.mp h).2 hxB)).symm
          · simp [hxB] }

end Count

/-! ## Row 24c (Steps 4-5) REDUCED to `G' ≠ ∅` (the orbit construction of Step 5 is NOT done here) -/

section Step45

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

theorem H15_L0_half_vk {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (k : ZMod n)
    (hk : 2 ^ a ∣ k.val) : ¬ 2 ^ a ∣ (k + half n).val ∧ padicValNat 2 (k + half n).val = a - 1 := by
  have hTm : 2 ^ (a - 1) ∣ (k + half n).val :=
    (H15_dvd_add_half (H15_dvd_n hn (by omega)) (H15_dvd_half hn (by omega) le_rfl) k).mpr
      (dvd_trans (pow_dvd_pow 2 (by omega)) hk)
  have hna : ¬ 2 ^ a ∣ (k + half n).val := H15_L0_add_half hn (by omega) hodd k hk
  have hna' : ¬ 2 ^ (a - 1 + 1) ∣ (k + half n).val := by
    rw [show a - 1 + 1 = a by omega]
    exact hna
  have h0 : (k + half n).val ≠ 0 := fun h => hna (h ▸ dvd_zero _)
  exact ⟨hna, (H15_vk_iff h0 _).mpr ⟨hTm, hna'⟩⟩

theorem H15_layer0'_closed {a nodd r : ℕ} [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (hr : ¬ r ∣ pp n * n) (k : ZMod n) (hk : k ∈ layer0' n a) :
    (r : ZMod n) * k ∈ layer0' n a ∧ -k ∈ layer0' n a ∧ 2 * k ∈ layer0' n a := by
  have hrodd : Odd r := H15_r_odd hn ha hr
  have h8 : 2 ^ 3 ∣ n := H15_dvd_n hn ha
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h8)
  have hA : 2 ^ a ∣ n := H15_dvd_n hn le_rfl
  have hu := H15_unit_r hr
  obtain ⟨hka, hk0⟩ := (H15_mem_layer0' k).mp hk
  have hma : ¬ 2 ^ a ∣ (half n : ZMod n).val := by
    rw [H7_half_val]
    exact H15_not_dvd_half hn (by omega) hodd
  refine ⟨(H15_mem_layer0' _).mpr ⟨(H15_dvd_mul_odd hA hrodd k).mpr hka,
      fun h0 => hk0 ((hu.mul_right_eq_zero).mp h0)⟩,
    (H15_mem_layer0' _).mpr ⟨(H15_dvd_neg hA k).mpr hka, neg_ne_zero.mpr hk0⟩,
    (H15_mem_layer0' _).mpr ⟨?_, ?_⟩⟩
  · have hc := (H15_dvd_cast hA k).mp hka
    rw [H15_dvd_cast hA, map_mul, hc, mul_zero]
  · intro h0
    rcases (H15_two_mul_eq_zero hev k).mp h0 with h1 | h1
    · exact hk0 h1
    · exact hma (h1 ▸ hka)

/-- Step 5: `f ↦ τ f / f` maps `G'` into `G''` (κ cancels). -/
theorem H15_tau_mem {a nodd r : ℕ} [Fact r.Prime] [CharP L r] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a)
    (hodd : Odd nodd) (hr : ¬ r ∣ pp n * n) (σr : ℤ) (ω : L) (hω : IsPrimitiveRoot ω n) (f : ZMod n → L)
    (hf : f ∈ Gprime n a r σr (kappa n L) ω) : tauG n a f / f ∈ Gprime n a r σr 1 ω := by
  have h8 : 2 ^ 3 ∣ n := H15_dvd_n hn ha
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h8)
  have hκ : kappa n L ≠ 0 := H15_kappa_ne hr
  have hω0 : ω ≠ 0 := hω.ne_zero (NeZero.ne n)
  have hne : ∀ k ∈ layer0' n a, f k ≠ 0 := by
    intro k hk h0
    have e := (hf.1 k hk).2
    rw [h0, zero_mul] at e
    exact mul_ne_zero hκ (pow_ne_zero _ (pow_ne_zero _ hω0)) e.symm
  have hτ : ∀ k ∈ layer0' n a, tauG n a f k = f (2 * k) := by
    intro k hk
    unfold tauG
    rw [ite_eq_left hk]
  have hω1 : ∀ k ∈ layer0' n a, (ω ^ k.val) ^ (n / 2) = 1 := by
    intro k hk
    obtain ⟨hka, -⟩ := (H15_mem_layer0' k).mp hk
    have hke : Even k.val := even_iff_two_dvd.mpr (dvd_trans (dvd_pow_self 2 (by omega)) hka)
    rw [← pow_mul, mul_comm, pow_mul, H7_pow_half_eq_neg_one hev hω, hke.neg_one_pow]
  have hW2 : ∀ k : ZMod n, (ω ^ (2 * k).val) ^ ((r : ℤ) * σr) = ((ω ^ k.val) ^ ((r : ℤ) * σr)) ^ 2 := by
    intro k
    rw [two_mul, H7_pow_val_add ω hω.pow_eq_one, mul_zpow, pow_two]
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun k hk => ?_⟩
  · obtain ⟨hrk, -, h2k⟩ := H15_layer0'_closed hn ha hodd hr k hk
    show tauG n a f ((r : ZMod n) * k) / f ((r : ZMod n) * k) =
      (ω ^ k.val) ^ ((r : ℤ) * σr) * (tauG n a f k / f k) ^ r
    have hZ : (ω ^ k.val) ^ ((r : ℤ) * σr) ≠ 0 := zpow_ne_zero _ (pow_ne_zero _ hω0)
    rw [hτ _ hrk, hτ k hk, show 2 * ((r : ZMod n) * k) = (r : ZMod n) * (2 * k) by ring, (hf.1 _ h2k).1,
      (hf.1 k hk).1, hW2, pow_two, mul_assoc, mul_div_mul_left _ _ hZ, mul_div_assoc, div_pow]
  · obtain ⟨-, hnk, h2k⟩ := H15_layer0'_closed hn ha hodd hr k hk
    show tauG n a f k / f k * (tauG n a f (-k) / f (-k)) = 1 * (ω ^ k.val) ^ (n / 2)
    rw [hτ k hk, hτ _ hnk, show 2 * -k = -(2 * k) by ring, div_mul_div_comm, (hf.1 _ h2k).2, (hf.1 k hk).2,
      hω1 k hk, hω1 _ h2k, mul_one, one_mul]
    exact div_self hκ
  · show tauG n a f k / f k = 1
    unfold tauG
    rw [ite_eq_right hk, hf.2 k hk, div_one]

/-- Row 24c REDUCED: given the row sec_6_3_fourier (same `L`, `ω`) AND the extra assumption `G' ≠ ∅` (Step 5's
orbit construction, NOT a row and NOT proved here), the full conclusion of `thm_6_4_step45` holds. -/
theorem H15_step45_of_nonempty (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a)
    (hodd : Odd nodd) (hr : ¬ r ∣ pp n * n) (_hr1 : r % 2 ^ a ≠ 2 ^ a - 1) (σr : ℤ) {L : Type*} [Field L] [CharP L r]
    [IsAlgClosed L] [Algebra (GaloisField r (n / Int.gcd σr n)) L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (hFour : Set.BijOn (dftA ω) (NFrSet n r σr) {h | F1 r σr ω h ∧ F3r (kappa n L) ω h ∧ F4 h} ∧
      ∀ y ∈ NFrSet n r σr, S y ^ 2 = kappa n _)
    (hG' : (Gprime n a r σr (kappa n L) ω).Nonempty) :
    (∀ y ∈ NFrSet n r σr,
      (∀ k : ZMod n, 2 ^ a ∣ k.val →
        (algebraMap _ L (S y))⁻¹ * dftA ω y (k + half n) = (kappa n L)⁻¹ ^ (2 ^ (a - 2)) *
          ∏ ρ ∈ (topLayer n).filter (fun ρ => (2 ^ (a - 1) : ZMod n) * ρ = k + half n), dftA ω y ρ ∧
        dftA ω y (2 * k) = (algebraMap _ L (S y))⁻¹ * dftA ω y (k + half n) * dftA ω y k) ∧
      (dftA ω y 0 = (n : L) ∨ dftA ω y 0 = -(n : L)) ∧
      (∀ k ∈ layer0' n a,
        (algebraMap _ L (S y))⁻¹ * dftA ω y ((r : ZMod n) * k + half n) =
          (ω ^ k.val) ^ ((r : ℤ) * σr) * ((algebraMap _ L (S y))⁻¹ * dftA ω y (k + half n)) ^ r ∧
        ((algebraMap _ L (S y))⁻¹ * dftA ω y (k + half n)) * ((algebraMap _ L (S y))⁻¹ * dftA ω y (-k + half n)) =
          (ω ^ k.val) ^ (n / 2)) ∧
      ∀ k ∈ layer0' n a, dftA ω y ((r : ZMod n) * k) = (ω ^ k.val) ^ ((r : ℤ) * σr) * dftA ω y k ^ r ∧
        dftA ω y k * dftA ω y (-k) = kappa n L * (ω ^ k.val) ^ (n / 2)) ∧
    (Gprime n a r σr (kappa n L) ω).Nonempty ∧
    ∀ f ∈ Gprime n a r σr (kappa n L) ω, tauG n a f / f ∈ Gprime n a r σr 1 ω := by
  have h8 : 2 ^ 3 ∣ n := H15_dvd_n hn ha
  have h8' : 8 ∣ n := by simpa using h8
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h8)
  have hκ : kappa n L ≠ 0 := H15_kappa_ne hr
  have hrodd : Odd r := H15_r_odd hn ha hr
  refine ⟨fun y hy => ?_, hG', fun f hf => H15_tau_mem hn ha hodd hr σr ω hω f hf⟩
  obtain ⟨hF1, hF3, hF4⟩ := hFour.1.mapsTo hy
  have hSL := H15_dft_half (L := L) hev ω hω y
  obtain ⟨-, -, hsgn⟩ := thm_6_4_step3b_of n a nodd r hn ha hodd hr σr ω hω y hy hFour
  have hS2 : algebraMap _ L (S y) ^ 2 = kappa n L := by
    rw [← map_pow, hFour.2 y hy]
    unfold kappa
    simp
  obtain ⟨s, hs⟩ : ∃ s : L, algebraMap (GaloisField r (n / Int.gcd σr n)) L (S y) = s := ⟨_, rfl⟩
  rw [hs] at hSL hsgn hS2 ⊢
  have hs0 : s ≠ 0 := by
    intro h0
    apply hκ
    rw [← hS2, h0]
    ring
  have hF4' : ∀ k, dftA ω y k * dftA ω y (k + half n) = s * dftA ω y (2 * k) := fun k => by
    rw [hF4 k, hSL]
  have hr1' : 1 ≤ r := hrodd.pos
  have hsgn' : (-1 : L) ^ σr.natAbs = s⁻¹ ^ (r - 1) := by
    rw [inv_pow]
    exact eq_inv_of_mul_eq_one_left hsgn
  have hpowr : s⁻¹ ^ r = s⁻¹ * s⁻¹ ^ (r - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hr1']
  refine ⟨fun k hk => ⟨?_, ?_⟩, sq_eq_sq_iff_eq_or_eq_neg.mp hF3.2, fun k hk => ⟨?_, ?_⟩,
    fun k hk => ⟨hF1 k, hF3.1 k ((H15_mem_layer0' k).mp hk).2⟩⟩
  · obtain ⟨hna, hv⟩ := H15_L0_half_vk hn ha hodd k hk
    have hd := H15_descent hn ha (dftA ω y) s hF4' hs0 _ (k + half n) hna rfl
    unfold H15_hmid at hd
    rw [hv] at hd
    have hκs : (kappa n L)⁻¹ ^ (2 ^ (a - 2)) = s⁻¹ ^ (2 ^ (a - 1)) := by
      rw [← hS2, ← inv_pow, ← pow_mul]
      congr 1
      rw [← pow_succ']
      congr 1
      omega
    rw [hd, hκs]
    show s⁻¹ * (s⁻¹ ^ (2 ^ (a - 1) - 1) * H15_D (a - 1) (dftA ω y) (k + half n)) =
      s⁻¹ ^ (2 ^ (a - 1)) * H15_D (a - 1) (dftA ω y) (k + half n)
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel Nat.one_le_two_pow]
  · linear_combination (-s⁻¹) * hF4' k - dftA ω y (2 * k) * inv_mul_cancel₀ hs0
  · obtain ⟨hka, -⟩ := (H15_mem_layer0' k).mp hk
    have hkm := (H15_L0_half_vk hn ha hodd k hka).1
    have e := hF1 (k + half n)
    rw [mul_add, H7_odd_mul_half hev r hrodd, H15_omega_add_half hev hω,
      show -ω ^ k.val = (-1) * ω ^ k.val by ring, mul_zpow, H7_neg_one_zpow r hrodd] at e
    rw [e, mul_pow, hpowr, hsgn']
    ring
  · obtain ⟨hka, -⟩ := (H15_mem_layer0' k).mp hk
    have hkm := (H15_L0_half_vk hn ha hodd k hka).1
    have hkm0 : k + half n ≠ 0 := by
      intro h0
      apply hkm
      rw [h0, ZMod.val_zero]
      exact dvd_zero _
    rw [H7_neg_add_half hev,
      show s⁻¹ * dftA ω y (k + half n) * (s⁻¹ * dftA ω y (-(k + half n)))
        = s⁻¹ ^ 2 * (dftA ω y (k + half n) * dftA ω y (-(k + half n))) by ring,
      hF3.1 (k + half n) hkm0, H15_omega_add_half hev hω, Even.neg_pow ⟨n / 4, by omega⟩, ← hS2, ← mul_assoc,
      ← mul_pow, inv_mul_cancel₀ hs0, one_pow, one_mul]

end Step45

/-! ## Applications of the orbit construction: a top datum and `G' ≠ ∅` (rows 24c, 24(ii) with fewer hypotheses) -/

section OrbitApps

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

theorem H15_neg_one_pow_transfer {x y : ℕ} (h : 2 ^ 1 ∣ y ↔ 2 ^ 1 ∣ x) : (-1 : L) ^ y = (-1) ^ x := by
  rcases Nat.even_or_odd x with hx | hx
  · have hy : Even y := by
      rw [even_iff_two_dvd] at hx ⊢
      have h' : 2 ∣ y ↔ 2 ∣ x := by simpa using h
      exact h'.mpr hx
    rw [hx.neg_one_pow, hy.neg_one_pow]
  · rw [hx.neg_one_pow, (H15_odd_transfer h hx).neg_one_pow]

theorem H15_kappa_pow_r {r : ℕ} [Fact r.Prime] [CharP L r] : kappa n L ^ r = kappa n L := by
  unfold kappa
  rw [show (n : L) ^ 2 * (pp n : L) = ((n ^ 2 * pp n : ℕ) : L) by push_cast; ring, H15_natCast_pow_r]

/-- The laws of `G'` and of the top data, solved on any closed set `A` without fixed points of `x ↦ -x`. -/
theorem H15_exists_laws {a nodd r : ℕ} [Fact r.Prime] [CharP L r] [IsAlgClosed L] (hn : n = 2 ^ a * nodd)
    (ha : 3 ≤ a) (hr : ¬ r ∣ pp n * n) (σr : ℤ) (ω : L) (hω : IsPrimitiveRoot ω n) (A : Finset (ZMod n))
    (hAu : ∀ x ∈ A, (r : ZMod n) * x ∈ A) (hAn : ∀ x ∈ A, -x ∈ A) (hAne : ∀ x ∈ A, -x ≠ x) :
    ∃ f : ZMod n → L, ∀ x ∈ A, f ((r : ZMod n) * x) = (ω ^ x.val) ^ ((r : ℤ) * σr) * f x ^ r ∧
      f x * f (-x) = kappa n L * (ω ^ x.val) ^ (n / 2) := by
  have hp : r.Prime := Fact.out
  have h8 : 2 ^ 3 ∣ n := H15_dvd_n hn ha
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h8)
  have h2 : 2 ^ 1 ∣ n := H15_dvd_n hn (by omega)
  have hrodd : Odd r := H15_r_odd hn ha hr
  have hκ : kappa n L ≠ 0 := H15_kappa_ne hr
  have hω0 : ω ≠ 0 := hω.ne_zero (NeZero.ne n)
  have hcop : Nat.Coprime r n :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => hr (dvd_mul_of_dvd_right h _))
  have hpar : ∀ x : ZMod n, (ω ^ x.val) ^ (n / 2) = (-1) ^ x.val := fun x => by
    rw [← pow_mul, mul_comm, pow_mul, H7_pow_half_eq_neg_one hev hω]
  exact H15_orbit_solve hcop hp.two_le (H15_W r σr ω) (fun x => kappa n L * (ω ^ x.val) ^ (n / 2))
    (H15_W_ne r σr hω0) (H15_W_neg r σr hω)
    (fun x => mul_ne_zero hκ (pow_ne_zero _ (pow_ne_zero _ hω0)))
    (fun x => by
      show kappa n L * (ω ^ (-x).val) ^ (n / 2) = kappa n L * (ω ^ x.val) ^ (n / 2)
      rw [hpar, hpar, H15_neg_one_pow_transfer (L := L) (H15_dvd_neg h2 x)])
    (fun x => by
      show kappa n L * (ω ^ ((r : ZMod n) * x).val) ^ (n / 2) = (kappa n L * (ω ^ x.val) ^ (n / 2)) ^ r
      rw [hpar, hpar, H15_neg_one_pow_transfer (L := L) (H15_dvd_mul_odd h2 hrodd x), mul_pow,
        H15_kappa_pow_r (n := n) (r := r), ← pow_mul, mul_comm x.val r, pow_mul, hrodd.neg_one_pow])
    A hAu hAn hAne

/-- Step 5: `G' ≠ ∅` (orbit construction on `μ_{n_odd} ∖ {1}`, self-inverse orbits included). -/
theorem H15_Gprime_nonempty {a nodd r : ℕ} [Fact r.Prime] [CharP L r] [IsAlgClosed L] (hn : n = 2 ^ a * nodd)
    (ha : 3 ≤ a) (hodd : Odd nodd) (hr : ¬ r ∣ pp n * n) (σr : ℤ) (ω : L) (hω : IsPrimitiveRoot ω n) :
    (Gprime n a r σr (kappa n L) ω).Nonempty := by
  classical
  have h8 : 2 ^ 3 ∣ n := H15_dvd_n hn ha
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h8)
  have hma : ¬ 2 ^ a ∣ (half n : ZMod n).val := by
    rw [H7_half_val]
    exact H15_not_dvd_half hn (by omega) hodd
  obtain ⟨f, hf⟩ := H15_exists_laws hn ha hr σr ω hω (layer0' n a)
    (fun x hx => (H15_layer0'_closed hn ha hodd hr x hx).1)
    (fun x hx => (H15_layer0'_closed hn ha hodd hr x hx).2.1)
    (fun x hx hnx => by
      obtain ⟨hxa, hx0⟩ := (H15_mem_layer0' x).mp hx
      have h2x : 2 * x = 0 := by linear_combination -hnx
      rcases (H15_two_mul_eq_zero hev x).mp h2x with h1 | h1
      · exact hx0 h1
      · exact hma (h1 ▸ hxa))
  refine ⟨fun x => if x ∈ layer0' n a then f x else 1, fun k hk => ?_, fun k hk => ?_⟩
  · obtain ⟨h1, h2, -⟩ := H15_layer0'_closed hn ha hodd hr k hk
    simp only [ite_eq_left hk, ite_eq_left h1, ite_eq_left h2]
    exact hf k hk
  · simp only [ite_eq_right hk]

/-- Step 2 (existence only): a top datum exists. -/
theorem H15_topData_nonempty {a nodd r : ℕ} [Fact r.Prime] [CharP L r] [IsAlgClosed L] (hn : n = 2 ^ a * nodd)
    (ha : 3 ≤ a) (hr : ¬ r ∣ pp n * n) (σr : ℤ) (ω : L) (hω : IsPrimitiveRoot ω n) :
    (topData n r σr (kappa n L) ω).Nonempty := by
  classical
  have h8 : 2 ^ 3 ∣ n := H15_dvd_n hn ha
  have h8' : 8 ∣ n := by simpa using h8
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h8)
  have h2 : 2 ^ 1 ∣ n := H15_dvd_n hn (by omega)
  have hrodd : Odd r := H15_r_odd hn ha hr
  have hmemT : ∀ x : ZMod n, x ∈ topLayer n ↔ Odd x.val := fun x => by simp [topLayer]
  have hmv : Even (half n : ZMod n).val := by
    rw [H7_half_val]
    exact ⟨n / 4, by omega⟩
  obtain ⟨f, hf⟩ := H15_exists_laws hn ha hr σr ω hω (topLayer n)
    (fun x hx => (hmemT _).mpr (H15_odd_transfer (H15_dvd_mul_odd h2 hrodd x) ((hmemT x).mp hx)))
    (fun x hx => (hmemT _).mpr (H15_odd_transfer (H15_dvd_neg h2 x) ((hmemT x).mp hx)))
    (fun x hx hnx => by
      have hxo := (hmemT x).mp hx
      have h2x : 2 * x = 0 := by linear_combination -hnx
      rcases (H15_two_mul_eq_zero hev x).mp h2x with h1 | h1
      · rw [h1, ZMod.val_zero] at hxo
        exact absurd hxo (by decide)
      · rw [h1] at hxo
        exact (Nat.not_even_iff_odd.mpr hxo) hmv)
  refine ⟨fun x => if Odd x.val then f x else 0, fun k hk => ?_, fun k hk => ?_⟩
  · have h1 : Odd ((r : ZMod n) * k).val := H15_odd_transfer (H15_dvd_mul_odd h2 hrodd k) hk
    have h2' : Odd (-k).val := H15_odd_transfer (H15_dvd_neg h2 k) hk
    simp only [ite_eq_left hk, ite_eq_left h1, ite_eq_left h2']
    exact hf k ((hmemT k).mpr hk)
  · simp only [ite_eq_right (Nat.not_odd_iff_even.mpr hk)]

end OrbitApps

section Count2

open Classical

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

theorem H15_pairOf_eq {r : ℕ} (hcop : Nat.Coprime r n) {k x : ZMod n} (hx : x ∈ orbit r k ∪ orbit r (-k)) :
    H15_pairOf r x = H15_pairOf r k := by
  unfold H15_pairOf
  rcases Finset.mem_union.mp hx with h | h
  · rw [H6_orbit_eq hcop h, H6_orbit_eq hcop (H6_neg_mem h)]
  · have h' := H6_neg_mem h
    rw [neg_neg] at h'
    rw [H6_orbit_eq hcop h, H6_orbit_eq hcop h', Finset.pair_comm]

/-- The count on a closed set without self-inverse orbits: `∏_{pairs} (r^{L} - 1)`. -/
theorem H15_count_sol {r : ℕ} [Fact r.Prime] [CharP L r] [IsAlgClosed L] (hcop : Nat.Coprime r n)
    (W C : ZMod n → L) (z : L) (hW0 : ∀ x, W x ≠ 0) (hWW : ∀ x, W x * W (-x) = 1) (hC0 : ∀ x, C x ≠ 0)
    (hCn : ∀ x, C (-x) = C x) (hCu : ∀ x, C ((r : ZMod n) * x) = C x ^ r) (A : Finset (ZMod n)) :
    (∀ x ∈ A, (r : ZMod n) * x ∈ A) → (∀ x ∈ A, -x ∈ A) → (∀ x ∈ A, -x ∉ orbit r x) →
      Nat.card (H15_Sol r W C z A) = ∏ P ∈ A.image (H15_pairOf r), (r ^ pairLen P - 1) := by
  refine Finset.strongInduction (p := fun A => (∀ x ∈ A, (r : ZMod n) * x ∈ A) → (∀ x ∈ A, -x ∈ A) →
    (∀ x ∈ A, -x ∉ orbit r x) → Nat.card (H15_Sol r W C z A) = ∏ P ∈ A.image (H15_pairOf r), (r ^ pairLen P - 1))
    (fun A ih => ?_) A
  intro hAu hAn hAself
  rcases A.eq_empty_or_nonempty with hA | ⟨k, hk⟩
  · subst hA
    have hset : H15_Sol r W C z (∅ : Finset (ZMod n)) = {fun _ => z} := by
      ext f
      constructor
      · intro hf
        exact Set.mem_singleton_iff.mpr (funext fun x => hf.2 x (Finset.notMem_empty x))
      · intro hf
        rw [Set.mem_singleton_iff] at hf
        rw [hf]
        exact ⟨fun x hx => absurd hx (Finset.notMem_empty x), fun x _ => rfl⟩
    rw [hset, Nat.card_coe_set_eq, Set.ncard_singleton, Finset.image_empty, Finset.prod_empty]
  · have hBA : orbit r k ∪ orbit r (-k) ⊆ A := by
      intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · obtain ⟨i, rfl⟩ := H6_mem_orbit.mp h
        exact H15_pow_mem hAu hk i
      · obtain ⟨i, rfl⟩ := H6_mem_orbit.mp h
        exact H15_pow_mem hAu (hAn k hk) i
    have hss : A \ (orbit r k ∪ orbit r (-k)) ⊂ A :=
      Finset.sdiff_ssubset hBA ⟨k, Finset.mem_union_left _ (H6_self_mem r k)⟩
    have hIH := ih _ hss
      (fun x hx => by
        obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
        exact Finset.mem_sdiff.mpr ⟨hAu x h1, fun h => h2 (H15_B_back hcop h)⟩)
      (fun x hx => by
        obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
        exact Finset.mem_sdiff.mpr ⟨hAn x h1, fun h => h2 (H15_B_nback h)⟩)
      (fun x hx => hAself x (Finset.mem_sdiff.mp hx).1)
    have himg : A.image (H15_pairOf r) =
        insert (H15_pairOf r k) ((A \ (orbit r k ∪ orbit r (-k))).image (H15_pairOf r)) := by
      ext P
      simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_sdiff]
      constructor
      · rintro ⟨x, hxA, rfl⟩
        by_cases hxB : x ∈ orbit r k ∪ orbit r (-k)
        · exact Or.inl (H15_pairOf_eq hcop hxB)
        · exact Or.inr ⟨x, ⟨hxA, hxB⟩, rfl⟩
      · rintro (rfl | ⟨x, ⟨hxA, -⟩, rfl⟩)
        · exact ⟨k, hk, rfl⟩
        · exact ⟨x, hxA, rfl⟩
    have hnotin : H15_pairOf r k ∉ (A \ (orbit r k ∪ orbit r (-k))).image (H15_pairOf r) := by
      intro hP
      obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hP
      obtain ⟨-, hxB⟩ := Finset.mem_sdiff.mp hx
      have hO : orbit r x ∈ H15_pairOf r k := by
        rw [← hxeq]
        exact Finset.mem_insert_self _ _
      unfold H15_pairOf at hO
      rcases Finset.mem_insert.mp hO with h | h
      · exact hxB (Finset.mem_union_left _ (h ▸ H6_self_mem r x))
      · rw [Finset.mem_singleton] at h
        exact hxB (Finset.mem_union_right _ (h ▸ H6_self_mem r x))
    rw [H15_sol_split W C z A (orbit r k ∪ orbit r (-k)) hBA (fun x hx => H15_B_mul hx) (fun x hx => H15_B_neg hx)
        (fun x hx => H15_B_back hcop hx) (fun x hx => H15_B_nback hx),
      H15_count_block hcop W C z hW0 hWW hC0 hCn hCu k (hAself k hk), hIH, himg, Finset.prod_insert hnotin,
      H15_pairLen hcop k (hAself k hk)]

theorem H15_C_neg {ω : L} (hev : Even n) (hω : IsPrimitiveRoot ω n) (κ : L) (x : ZMod n) :
    κ * (ω ^ (-x).val) ^ (n / 2) = κ * (ω ^ x.val) ^ (n / 2) := by
  have h2 : 2 ^ 1 ∣ n := by simpa using even_iff_two_dvd.mp hev
  have hpar : ∀ x : ZMod n, (ω ^ x.val) ^ (n / 2) = (-1) ^ x.val := fun x => by
    rw [← pow_mul, mul_comm, pow_mul, H7_pow_half_eq_neg_one hev hω]
  rw [hpar, hpar, H15_neg_one_pow_transfer (L := L) (H15_dvd_neg h2 x)]

theorem H15_C_mul {ω : L} (hev : Even n) (hω : IsPrimitiveRoot ω n) {r : ℕ} (hrodd : Odd r) (κ : L)
    (hκr : κ ^ r = κ) (x : ZMod n) :
    κ * (ω ^ ((r : ZMod n) * x).val) ^ (n / 2) = (κ * (ω ^ x.val) ^ (n / 2)) ^ r := by
  have h2 : 2 ^ 1 ∣ n := by simpa using even_iff_two_dvd.mp hev
  have hpar : ∀ x : ZMod n, (ω ^ x.val) ^ (n / 2) = (-1) ^ x.val := fun x => by
    rw [← pow_mul, mul_comm, pow_mul, H7_pow_half_eq_neg_one hev hω]
  rw [hpar, hpar, H15_neg_one_pow_transfer (L := L) (H15_dvd_mul_odd h2 hrodd x), mul_pow, hκr, ← pow_mul,
    mul_comm x.val r, pow_mul, hrodd.neg_one_pow]

end Count2

/-- Row 24a — proof of Theorem 6.4, Step 2: the top data, and the homogeneous top data, number `∏_i (r^{L_i}-1)`. -/
theorem thm_6_4_step2_proved (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a)
    (hodd : Odd nodd) (hr : ¬ r ∣ pp n * n) (hr1 : r % 2 ^ a ≠ 2 ^ a - 1) (σr : ℤ) {L : Type*} [Field L] [CharP L r]
    [IsAlgClosed L] (ω : L) (hω : IsPrimitiveRoot ω n) :
    Nat.card (topData n r σr (kappa n L) ω) = pairProd n r ∧
      Nat.card (topData0 n r : Set (ZMod n → L)) = pairProd n r := by
  classical
  have hp : r.Prime := Fact.out
  have h8 : 2 ^ 3 ∣ n := H15_dvd_n hn ha
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h8)
  have h2 : 2 ^ 1 ∣ n := H15_dvd_n hn (by omega)
  have hrodd : Odd r := H15_r_odd hn ha hr
  have hκ : kappa n L ≠ 0 := H15_kappa_ne hr
  have hω0 : ω ≠ 0 := hω.ne_zero (NeZero.ne n)
  have hcop : Nat.Coprime r n :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => hr (dvd_mul_of_dvd_right h _))
  have hmemT : ∀ x : ZMod n, x ∈ topLayer n ↔ Odd x.val := fun x => by simp [topLayer]
  have hTu : ∀ x ∈ topLayer n, (r : ZMod n) * x ∈ topLayer n := fun x hx =>
    (hmemT _).mpr (H15_odd_transfer (H15_dvd_mul_odd h2 hrodd x) ((hmemT x).mp hx))
  have hTn : ∀ x ∈ topLayer n, -x ∈ topLayer n := fun x hx =>
    (hmemT _).mpr (H15_odd_transfer (H15_dvd_neg h2 x) ((hmemT x).mp hx))
  have hpairs := (thm_6_4_pairs_proved n a nodd r hn ha hodd hr hr1).1
  have hself : ∀ x ∈ topLayer n, -x ∉ orbit r x := by
    intro x hx hnx
    have hO : orbit r x ∈ topOrbits n r := Finset.mem_image.mpr ⟨x, hx, rfl⟩
    apply (hpairs _ hO).2.1
    rw [H6_inv_orbit]
    exact H6_orbit_eq hcop hnx
  have hP : (topLayer n).image (H15_pairOf r) = topPairs n r := by
    unfold topPairs topOrbits
    rw [Finset.image_image]
    refine Finset.image_congr (fun k _ => ?_)
    simp only [Function.comp, H15_pairOf, H6_inv_orbit]
  have hnot : ∀ x : ZMod n, x ∉ topLayer n ↔ Even x.val := fun x => by
    rw [hmemT, Nat.not_odd_iff_even]
  have hT : topData n r σr (kappa n L) ω =
      H15_Sol r (H15_W r σr ω) (fun x => kappa n L * (ω ^ x.val) ^ (n / 2)) 0 (topLayer n) := by
    ext h
    constructor
    · rintro ⟨h1, h2'⟩
      exact ⟨fun x hx => h1 x ((hmemT x).mp hx), fun x hx => h2' x ((hnot x).mp hx)⟩
    · rintro ⟨h1, h2'⟩
      exact ⟨fun x hx => h1 x ((hmemT x).mpr hx), fun x hx => h2' x ((hnot x).mpr hx)⟩
  have hT0 : (topData0 n r : Set (ZMod n → L)) = H15_Sol r (fun _ => 1) (fun _ => 1) 1 (topLayer n) := by
    ext lam
    constructor
    · rintro ⟨h1, h2'⟩
      refine ⟨fun x hx => ?_, fun x hx => h2' x ((hnot x).mp hx)⟩
      obtain ⟨e1, e3⟩ := h1 x ((hmemT x).mp hx)
      exact ⟨by rw [e1, one_mul], e3⟩
    · rintro ⟨h1, h2'⟩
      refine ⟨fun x hx => ?_, fun x hx => h2' x ((hnot x).mpr hx)⟩
      obtain ⟨e1, e3⟩ := h1 x ((hmemT x).mpr hx)
      exact ⟨by rw [e1, one_mul], e3⟩
  refine ⟨?_, ?_⟩
  · rw [hT, H15_count_sol hcop (H15_W r σr ω) (fun x => kappa n L * (ω ^ x.val) ^ (n / 2)) 0
      (H15_W_ne r σr hω0) (H15_W_neg r σr hω) (fun x => mul_ne_zero hκ (pow_ne_zero _ (pow_ne_zero _ hω0)))
      (fun x => H15_C_neg hev hω _ x) (fun x => H15_C_mul hev hω hrodd _ (H15_kappa_pow_r (n := n) (r := r)) x)
      (topLayer n) hTu hTn hself, hP]
    rfl
  · rw [hT0, H15_count_sol hcop (fun _ => (1 : L)) (fun _ => 1) 1 (fun _ => one_ne_zero) (fun _ => one_mul 1)
      (fun _ => one_ne_zero) (fun _ => rfl) (fun _ => (one_pow r).symm) (topLayer n) hTu hTn hself, hP]
    rfl

/-- Row 24c — proof of Theorem 6.4, Steps 4-5, GIVEN the row sec_6_3_fourier (exact instance at the same `L`, `ω`). -/
theorem thm_6_4_step45_of (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a)
    (hodd : Odd nodd) (hr : ¬ r ∣ pp n * n) (hr1 : r % 2 ^ a ≠ 2 ^ a - 1) (σr : ℤ) {L : Type*} [Field L] [CharP L r]
    [IsAlgClosed L] [Algebra (GaloisField r (n / Int.gcd σr n)) L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (hFour : Set.BijOn (dftA ω) (NFrSet n r σr) {h | F1 r σr ω h ∧ F3r (kappa n L) ω h ∧ F4 h} ∧
      ∀ y ∈ NFrSet n r σr, S y ^ 2 = kappa n _) :
    (∀ y ∈ NFrSet n r σr,
      (∀ k : ZMod n, 2 ^ a ∣ k.val →
        (algebraMap _ L (S y))⁻¹ * dftA ω y (k + half n) = (kappa n L)⁻¹ ^ (2 ^ (a - 2)) *
          ∏ ρ ∈ (topLayer n).filter (fun ρ => (2 ^ (a - 1) : ZMod n) * ρ = k + half n), dftA ω y ρ ∧
        dftA ω y (2 * k) = (algebraMap _ L (S y))⁻¹ * dftA ω y (k + half n) * dftA ω y k) ∧
      (dftA ω y 0 = (n : L) ∨ dftA ω y 0 = -(n : L)) ∧
      (∀ k ∈ layer0' n a,
        (algebraMap _ L (S y))⁻¹ * dftA ω y ((r : ZMod n) * k + half n) =
          (ω ^ k.val) ^ ((r : ℤ) * σr) * ((algebraMap _ L (S y))⁻¹ * dftA ω y (k + half n)) ^ r ∧
        ((algebraMap _ L (S y))⁻¹ * dftA ω y (k + half n)) * ((algebraMap _ L (S y))⁻¹ * dftA ω y (-k + half n)) =
          (ω ^ k.val) ^ (n / 2)) ∧
      ∀ k ∈ layer0' n a, dftA ω y ((r : ZMod n) * k) = (ω ^ k.val) ^ ((r : ℤ) * σr) * dftA ω y k ^ r ∧
        dftA ω y k * dftA ω y (-k) = kappa n L * (ω ^ k.val) ^ (n / 2)) ∧
    (Gprime n a r σr (kappa n L) ω).Nonempty ∧
    ∀ f ∈ Gprime n a r σr (kappa n L) ω, tauG n a f / f ∈ Gprime n a r σr 1 ω :=
  H15_step45_of_nonempty n a nodd r hn ha hodd hr hr1 σr ω hω hFour (H15_Gprime_nonempty hn ha hodd hr σr ω hω)

/-- Row 24(ii) — Theorem 6.4(ii), GIVEN the rows sec_6_3_fourier and thm_6_4_step67 only (exact instances, universally
quantified over the field `L : Type`). Built here: one solution of the Fourier system (top datum and `G' ≠ ∅` by the
orbit construction, descent by Step 3, layer 0 after a twist by `Π`), and the torsor under the homogeneous group. -/
theorem thm_6_4_ii_of (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (hr : ¬ r ∣ pp n * n) (_hr1 : r % 2 ^ a ≠ 2 ^ a - 1) (σr : ℤ)
    (hsign : (-1 : ℤ) ^ σr.natAbs = legendreSym r (pp n : ℤ))
    (hFour : ∀ (L : Type) [Field L] [Algebra (GaloisField r (n / Int.gcd σr n)) L] (ω : L)
      (_hω : IsPrimitiveRoot ω n),
      Set.BijOn (dftA ω) (NFrSet n r σr) {h | F1 r σr ω h ∧ F3r (kappa n L) ω h ∧ F4 h} ∧
        ∀ y ∈ NFrSet n r σr, S y ^ 2 = kappa n _)
    (hStep67 : ∀ (L : Type) [Field L] [CharP L r] [IsAlgClosed L],
      Set.SurjOn (Pmap n a) (topData0 n r : Set (ZMod n → L)) (Ggrp n a r) ∧
      Nat.card ((fun g => tauG n a g / g) '' (Ggrp n a r : Set (ZMod n → L))) *
          Nat.card {g : ZMod n → L // g ∈ (Ggrp n a r : Set (ZMod n → L)) ∧ tauG n a g = g} =
        Nat.card (Ggrp n a r : Set (ZMod n → L)) ∧
      Nat.card {lam : ZMod n → L // (∀ k, lam ((r : ZMod n) * k) = lam k ^ r) ∧ (∀ k, lam k * lam (-k) = 1) ∧
        ∀ k, lam k * lam (k + half n) = lam (half n) * lam (2 * k)} = 4 * pairProd n r) :
    Nat.card (NFrSet n r σr) = 4 * pairProd n r := by
  have hnF : ((n : ℕ) : AlgebraicClosure (GaloisField r (n / Int.gcd σr n))) ≠ 0 := H15_n_ne hr
  have : NeZero ((n : ℕ) : AlgebraicClosure (GaloisField r (n / Int.gcd σr n))) := ⟨hnF⟩
  obtain ⟨ω, hω⟩ :=
    HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure (GaloisField r (n / Int.gcd σr n))) n
  obtain ⟨hPi, -, hK⟩ := hStep67 (AlgebraicClosure (GaloisField r (n / Int.gcd σr n)))
  obtain ⟨h0, hh0⟩ := H15_exists hn ha hodd hr σr hsign ω hω (H15_topData_nonempty hn ha hr σr ω hω)
    (H15_Gprime_nonempty hn ha hodd hr σr ω hω) (fun f hf => H15_tau_mem hn ha hodd hr σr ω hω f hf) hPi
  rw [Nat.card_congr ((hFour _ ω hω).1.equiv _),
    H15_torsor σr (H15_kappa_ne hr) (hω.ne_zero (NeZero.ne n)) (H15_n_ne hr) h0 hh0]
  exact hK

/-- Row 25b, given rows 24(ii) and 26(ii) (exact instances) and the PROVED row 25a. -/
theorem cor_6_5_solvable_of (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a)
    (hodd : Odd nodd) (hp : (pp n).Prime) (hr : ¬ r ∣ pp n * n) {M : Type*} [Field M] (χ : MulChar (ZMod (pp n)) M) (g : (ZMod (pp n))ˣ)
    (_hg : ∀ x : (ZMod (pp n))ˣ, x ∈ Subgroup.zpowers g) (_hχg : IsPrimitiveRoot (χ (g : ZMod (pp n))) n)
    (μ : M) (hμ : IsPrimitiveRoot μ n) (σr : ℤ) (hχr : χ (r : ZMod (pp n)) = μ ^ σr)
    (hX35r : ∀ (μ' : M) (σ' : ℤ), IsPrimitiveRoot μ' n → χ (r : ZMod (pp n)) = μ' ^ σ' →
      (-1 : ℤ) ^ σ'.natAbs = legendreSym r ((-1) ^ (n / 2) * (pp n : ℤ)))
    (h64ii : ∀ (_hr1 : r % 2 ^ a ≠ 2 ^ a - 1) (_hsign : (-1 : ℤ) ^ σr.natAbs = legendreSym r (pp n : ℤ)),
      Nat.card (NFrSet n r σr) = 4 * pairProd n r)
    (h66ii : ∀ (_hn' : n = 2 ^ a) (_hr' : ¬ r ∣ pp n) (_hr1 : r % 2 ^ a = 2 ^ a - 1)
      (_hsign : (-1 : ℤ) ^ σr.natAbs = legendreSym r (pp n : ℤ)), Nat.card (NFrSet n r σr) = 4 * (r + 1) ^ (n / 4)) :
    r % 2 ^ a ≠ 2 ^ a - 1 ∨ nodd = 1 → (NFrSet n r σr).Nonempty := by
  intro hcase
  have hsg := cor_6_5_sign_proved n a nodd r hn ha hodd hp hr σr (hX35r μ σr hμ hχr)
  have hcard : Nat.card (NFrSet n r σr) ≠ 0 := by
    by_cases hr1 : r % 2 ^ a ≠ 2 ^ a - 1
    · rw [h64ii hr1 hsg]
      exact mul_ne_zero four_ne_zero (H15_pairProd_ne_zero n a nodd r hn ha hodd hr hr1)
    · push Not at hr1
      have hn1 : nodd = 1 := hcase.resolve_left (fun h => h hr1)
      rw [h66ii (by rw [hn, hn1, mul_one]) (fun h => hr (dvd_mul_of_dvd_left h _)) hr1 hsg]
      positivity
  obtain ⟨hne, -⟩ := Nat.card_ne_zero.mp hcard
  exact Set.nonempty_coe_sort.mp hne

end Xia.Proofs

#print axioms Xia.Proofs.thm_6_4_step2_proved
#print axioms Xia.Proofs.thm_6_4_step3b_of
#print axioms Xia.Proofs.thm_6_4_step45_of
#print axioms Xia.Proofs.thm_6_4_ii_of
#print axioms Xia.Proofs.prop_6_6_ii_of
#print axioms Xia.Proofs.cor_6_5_solvable_of
