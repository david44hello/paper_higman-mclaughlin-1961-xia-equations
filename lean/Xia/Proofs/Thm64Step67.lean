/- Xia/Proofs/Thm64Step67.lean — proofs of the rows thm_6_4_step67 of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry
import Xia.Defs.Layer0
import Xia.Proofs.Thm41Steps26
import Xia.Proofs.Thm41Steps57
import Xia.Proofs.Thm64

namespace Xia.Proofs

open Xia Finset

set_option linter.unusedSectionVars false

/-! ## 1. Arithmetic of `k ↦ r k` on `ℤ/n` (r odd, coprime to n) -/

section Basic

variable {n : ℕ} [NeZero n]

theorem H24_r_half (hn2 : 2 ∣ n) {r : ℕ} (hr : Odd r) : (r : ZMod n) * half n = half n := by
  obtain ⟨s, rfl⟩ := hr
  push_cast
  linear_combination (s : ZMod n) * H11_half_add (n := n) hn2

theorem H24_odd_mulr (hn2 : 2 ∣ n) {r : ℕ} (hr : Odd r) {k : ZMod n} (hk : Odd k.val) :
    Odd ((r : ZMod n) * k).val := by
  rw [H11_odd_iff hn2] at hk ⊢
  rw [map_mul, hk, mul_one, map_natCast, ZMod.natCast_eq_one_iff_odd]
  exact hr

theorem H24_pow_odd (hn2 : 2 ∣ n) {r : ℕ} (hr : Odd r) (i : ℕ) {k : ZMod n} (hk : Odd k.val) :
    Odd (((r : ZMod n)) ^ i * k).val := by
  induction i with
  | zero => simpa using hk
  | succ i ih =>
    rw [pow_succ', mul_assoc]
    exact H24_odd_mulr hn2 hr ih

theorem H24_per_dvd {r : ℕ} (hcop : Nat.Coprime r n) {x : ZMod n} {i : ℕ} (h : (r : ZMod n) ^ i * x = x) :
    H15_per hcop x ∣ i := by
  have e := H15_pow_eq_mod hcop x (i := i) (j := 0) (by rw [pow_zero, one_mul]; exact h)
  rw [Nat.zero_mod] at e
  exact Nat.dvd_of_mod_eq_zero e

theorem H24_inv_pow {r : ℕ} (hcop : Nat.Coprime r n) (i : ℕ) :
    ∃ w : ℕ, (r : ZMod n) ^ w * (r : ZMod n) ^ i = 1 := by
  obtain ⟨m, hm⟩ := H6_pow_period hcop
  refine ⟨i * m, ?_⟩
  rw [← pow_add, show i * m + i = (m + 1) * i by ring, pow_mul, hm, one_pow]

theorem H24_unit {r : ℕ} (hcop : Nat.Coprime r n) : IsUnit (r : ZMod n) :=
  (ZMod.isUnit_iff_coprime r n).mpr hcop

theorem H24_kk_mulr (hn2 : 2 ∣ n) {r : ℕ} (hr : Odd r) (a : ℕ) (ρ : ZMod n) :
    H11_kk a ((r : ZMod n) * ρ) = (r : ZMod n) * H11_kk a ρ := by
  unfold H11_kk
  rw [mul_add, H24_r_half hn2 hr]
  ring

theorem H24_kk_pow (hn2 : 2 ∣ n) {r : ℕ} (hr : Odd r) (a i : ℕ) (ρ : ZMod n) :
    H11_kk a ((r : ZMod n) ^ i * ρ) = (r : ZMod n) ^ i * H11_kk a ρ := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [show (r : ZMod n) ^ (i + 1) * ρ = (r : ZMod n) * ((r : ZMod n) ^ i * ρ) by ring,
      H24_kk_mulr hn2 hr, ih]
    ring

theorem H24_l0_mul {a r : ℕ} (hcop : Nat.Coprime r n) (h2a : 2 ^ a ∣ n) {k : ZMod n} (hk : k ∈ layer0' n a) :
    (r : ZMod n) * k ∈ layer0' n a := by
  simp only [layer0', Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  refine ⟨?_, ?_⟩
  · rw [H11_dvd_val_iff h2a] at hk ⊢
    rw [map_mul, hk.1, mul_zero]
  · intro h0
    exact hk.2 ((H24_unit hcop).mul_right_eq_zero.mp h0)

theorem H24_l0_pow {a r : ℕ} (hcop : Nat.Coprime r n) (h2a : 2 ^ a ∣ n) (i : ℕ) {k : ZMod n}
    (hk : k ∈ layer0' n a) : (r : ZMod n) ^ i * k ∈ layer0' n a := by
  induction i with
  | zero => simpa using hk
  | succ i ih =>
    rw [pow_succ', mul_assoc]
    exact H24_l0_mul hcop h2a ih

/-- No top orbit is self-inverse (`r ≢ -1 mod 2^a`): an odd `x` and `-x` never lie in one orbit. -/
theorem H24_not_both {r : ℕ} (hcop : Nat.Coprime r n)
    (hneg : ∀ (i : ℕ) (k : ZMod n), Odd k.val → -k ≠ (r : ZMod n) ^ i * k) {x ρ : ZMod n} (hx : Odd x.val)
    (h1 : x ∈ orbit r ρ) (h2 : -x ∈ orbit r ρ) : False := by
  rw [← H6_orbit_eq hcop h1] at h2
  obtain ⟨i, hi⟩ := H6_mem_orbit.mp h2
  exact hneg i x hx hi

end Basic

/-! ## 2. The group `G` (for `r`), homogeneous top data, the map `Π` -/

section Groups

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

theorem H24_G_pow {a r : ℕ} (hcop : Nat.Coprime r n) (h2a : 2 ^ a ∣ n) {g : ZMod n → L}
    (hg : g ∈ (Ggrp n a r : Set (ZMod n → L))) {k : ZMod n} (hk : k ∈ layer0' n a) (i : ℕ) :
    g ((r : ZMod n) ^ i * k) = g k ^ (r ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [show (r : ZMod n) ^ (i + 1) * k = (r : ZMod n) * ((r : ZMod n) ^ i * k) by ring,
      (hg.1 _ (H24_l0_pow hcop h2a i hk)).1, ih, ← pow_mul, ← pow_succ]

theorem H24_G_neg {a r : ℕ} {g : ZMod n → L} (hg : g ∈ (Ggrp n a r : Set (ZMod n → L))) {k : ZMod n}
    (hk : k ∈ layer0' n a) : g (-k) = (g k)⁻¹ :=
  eq_inv_of_mul_eq_one_left (hg.1 k hk).2

theorem H24_G_ne {a r : ℕ} {g : ZMod n → L} (hg : g ∈ (Ggrp n a r : Set (ZMod n → L))) (k : ZMod n) :
    g k ≠ 0 := by
  by_cases hk : k ∈ layer0' n a
  · exact right_ne_zero_of_mul_eq_one (hg.1 k hk).2
  · rw [hg.2 k hk]
    exact one_ne_zero

theorem H24_G_mul {a r : ℕ} {g1 g2 : ZMod n → L} (hg1 : g1 ∈ (Ggrp n a r : Set (ZMod n → L)))
    (hg2 : g2 ∈ (Ggrp n a r : Set (ZMod n → L))) : g1 * g2 ∈ (Ggrp n a r : Set (ZMod n → L)) := by
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun k hk => ?_⟩
  · simp only [Pi.mul_apply, (hg1.1 k hk).1, (hg2.1 k hk).1, mul_pow]
  · simp only [Pi.mul_apply]
    calc g1 (-k) * g2 (-k) * (g1 k * g2 k) = (g1 (-k) * g1 k) * (g2 (-k) * g2 k) := by ring
      _ = 1 := by rw [(hg1.1 k hk).2, (hg2.1 k hk).2, one_mul]
  · simp only [Pi.mul_apply, hg1.2 k hk, hg2.2 k hk, one_mul]

theorem H24_G_inv {a r : ℕ} {g : ZMod n → L} (hg : g ∈ (Ggrp n a r : Set (ZMod n → L))) :
    g⁻¹ ∈ (Ggrp n a r : Set (ZMod n → L)) := by
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun k hk => ?_⟩
  · simp only [Pi.inv_apply, (hg.1 k hk).1, inv_pow]
  · simp only [Pi.inv_apply]
    rw [← mul_inv, (hg.1 k hk).2, inv_one]
  · simp only [Pi.inv_apply, hg.2 k hk, inv_one]

theorem H24_T0_pow (hn2 : 2 ∣ n) {r : ℕ} (hr : Odd r) {lam : ZMod n → L}
    (hl : lam ∈ (topData0 n r : Set (ZMod n → L))) {ρ : ZMod n} (hρ : Odd ρ.val) (i : ℕ) :
    lam ((r : ZMod n) ^ i * ρ) = lam ρ ^ (r ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [show (r : ZMod n) ^ (i + 1) * ρ = (r : ZMod n) * ((r : ZMod n) ^ i * ρ) by ring,
      (hl.1 _ (H24_pow_odd hn2 hr i hρ)).1, ih, ← pow_mul, ← pow_succ]

theorem H24_T0_neg {r : ℕ} {lam : ZMod n → L} (hl : lam ∈ (topData0 n r : Set (ZMod n → L))) {ρ : ZMod n}
    (hρ : Odd ρ.val) : lam (-ρ) = (lam ρ)⁻¹ :=
  eq_inv_of_mul_eq_one_right (hl.1 ρ hρ).2

theorem H24_T0_ne {r : ℕ} {lam : ZMod n → L} (hl : lam ∈ (topData0 n r : Set (ZMod n → L))) (k : ZMod n) :
    lam k ≠ 0 := by
  rcases Nat.even_or_odd k.val with he | ho
  · rw [hl.2 k he]
    exact one_ne_zero
  · exact left_ne_zero_of_mul_eq_one (hl.1 k ho).2

theorem H24_T0_one {r : ℕ} : (1 : ZMod n → L) ∈ (topData0 n r : Set (ZMod n → L)) :=
  ⟨fun k _ => by simp, fun k _ => rfl⟩

theorem H24_T0_mul {r : ℕ} {l1 l2 : ZMod n → L} (hl1 : l1 ∈ (topData0 n r : Set (ZMod n → L)))
    (hl2 : l2 ∈ (topData0 n r : Set (ZMod n → L))) : l1 * l2 ∈ (topData0 n r : Set (ZMod n → L)) := by
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun k hk => ?_⟩
  · simp only [Pi.mul_apply, (hl1.1 k hk).1, (hl2.1 k hk).1, mul_pow]
  · simp only [Pi.mul_apply]
    calc l1 k * l2 k * (l1 (-k) * l2 (-k)) = (l1 k * l1 (-k)) * (l2 k * l2 (-k)) := by ring
      _ = 1 := by rw [(hl1.1 k hk).2, (hl2.1 k hk).2, one_mul]
  · simp only [Pi.mul_apply, hl1.2 k hk, hl2.2 k hk, one_mul]

theorem H24_T0_inv {r : ℕ} {l1 : ZMod n → L} (hl1 : l1 ∈ (topData0 n r : Set (ZMod n → L))) :
    l1⁻¹ ∈ (topData0 n r : Set (ZMod n → L)) := by
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun k hk => ?_⟩
  · simp only [Pi.inv_apply, (hl1.1 k hk).1, inv_pow]
  · simp only [Pi.inv_apply]
    rw [← mul_inv, (hl1.1 k hk).2, inv_one]
  · simp only [Pi.inv_apply, hl1.2 k hk, inv_one]

/-- Step 6, first claim for `r`: `P_λ ∈ G` for `λ ∈ 𝒟^0`. -/
theorem H24_Pmap_mem {a r : ℕ} (hn2 : 2 ∣ n) (hr : Odd r) (hcop : Nat.Coprime r n) (h2a : 2 ^ a ∣ n)
    {lam : ZMod n → L} (hl : lam ∈ (topData0 n r : Set (ZMod n → L))) :
    Pmap n a lam ∈ (Ggrp n a r : Set (ZMod n → L)) := by
  obtain ⟨w, hw⟩ := H24_inv_pow hcop 1
  rw [pow_one] at hw
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun k hk => ?_⟩
  · rw [H11_Pmap_eq, ite_eq_left (H24_l0_mul hcop h2a hk), H11_Pmap_eq, ite_eq_left hk, ← Finset.prod_pow]
    symm
    apply Finset.prod_nbij' (fun ρ => (r : ZMod n) * ρ) (fun ρ => (r : ZMod n) ^ w * ρ)
    · intro ρ hρ
      rw [H11_mem_fib hn2] at hρ ⊢
      exact ⟨H24_odd_mulr hn2 hr hρ.1, by rw [H24_kk_mulr hn2 hr, hρ.2]⟩
    · intro ρ hρ
      rw [H11_mem_fib hn2] at hρ ⊢
      refine ⟨H24_pow_odd hn2 hr w hρ.1, ?_⟩
      rw [H24_kk_pow hn2 hr, hρ.2, ← mul_assoc, hw, one_mul]
    · intro ρ _
      rw [← mul_assoc, hw, one_mul]
    · intro ρ _
      rw [← mul_assoc, mul_comm _ ((r : ZMod n) ^ w), hw, one_mul]
    · intro ρ hρ
      rw [H11_mem_fib hn2] at hρ
      exact ((hl.1 ρ hρ.1).1).symm
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
    rw [H24_T0_neg hl hρ.1, inv_mul_cancel₀ (H24_T0_ne hl ρ)]
  · rw [H11_Pmap_eq, ite_eq_right hk]

end Groups

/-! ## 3. Step 6, surjectivity: one top pair at a time (the `r = 3` argument with `3 ↦ r`) -/

section Surj

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

theorem H24_Psi_one (r : ℕ) (k : ZMod n) (t : L) (i : ℕ) :
    H15_Psi r (fun _ => (1 : L)) k t i = t ^ (r ^ i) := by
  induction i with
  | zero => simp [H15_Psi]
  | succ i ih => rw [H15_Psi_succ, ih, one_mul, ← pow_mul, ← pow_succ]

open Classical in
/-- The homogeneous top datum on the pair of the orbit of `ρ0`: `t^{r^i}` at `r^i ρ0`, its inverse at `-r^i ρ0`,
`1` elsewhere. -/
noncomputable def H24_lamt (r : ℕ) (ρ0 : ZMod n) (t : L) : ZMod n → L :=
  fun x => if x ∈ orbit r ρ0 ∪ orbit r (-ρ0) then H15_g1 r (fun _ => (1 : L)) (fun _ => 1) ρ0 t x else 1

theorem H24_lam_of_t {r : ℕ} (hn2 : 2 ∣ n) (hr : Odd r) (hr2 : 2 ≤ r) (hcop : Nat.Coprime r n)
    (hneg : ∀ (i : ℕ) (k : ZMod n), Odd k.val → -k ≠ (r : ZMod n) ^ i * k)
    {ρ0 : ZMod n} (hρ0 : Odd ρ0.val) {t : L} (ht : t ^ (r ^ H15_per hcop ρ0 - 1) = 1) :
    ∃ lam ∈ (topData0 n r : Set (ZMod n → L)), (∀ i : ℕ, lam ((r : ZMod n) ^ i * ρ0) = t ^ (r ^ i)) ∧
      ∀ ρ : ZMod n, (∀ i : ℕ, ρ ≠ (r : ZMod n) ^ i * ρ0 ∧ ρ ≠ -((r : ZMod n) ^ i * ρ0)) → lam ρ = 1 := by
  classical
  have hM := H15_per_pos hcop ρ0
  have hrM : 2 ≤ r ^ H15_per hcop ρ0 :=
    le_trans hr2 (Nat.le_self_pow (Nat.pos_iff_ne_zero.mp hM) r)
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at ht
    exact zero_ne_one ht
  have hwrap : H15_Psi r (fun _ => (1 : L)) ρ0 t (H15_per hcop ρ0) = t := by
    rw [H24_Psi_one, ← Nat.sub_add_cancel (by omega : 1 ≤ r ^ H15_per hcop ρ0), pow_succ, ht, one_mul]
  have hself : -ρ0 ∉ orbit r ρ0 := by
    intro h
    obtain ⟨i, hi⟩ := H6_mem_orbit.mp h
    exact hneg i ρ0 hρ0 hi
  have hlaws := H15_g1_laws hcop (fun _ => (1 : L)) (fun _ => (1 : L)) (fun _ => one_ne_zero)
    (fun _ => mul_one 1) (fun _ => rfl) (fun _ => (one_pow r).symm) ρ0 hself t ht0 hwrap
  have hBodd : ∀ x ∈ orbit r ρ0 ∪ orbit r (-ρ0), Odd x.val := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact H6_odd_of_mem hn2 hr hρ0 h
    · exact H6_odd_of_mem hn2 hr (H6_odd_neg hn2 hρ0) h
  have hin : ∀ x ∈ orbit r ρ0 ∪ orbit r (-ρ0),
      H24_lamt r ρ0 t x = H15_g1 r (fun _ => (1 : L)) (fun _ => 1) ρ0 t x := by
    intro x hx
    unfold H24_lamt
    rw [ite_eq_left hx]
  have hout : ∀ x ∉ orbit r ρ0 ∪ orbit r (-ρ0), H24_lamt r ρ0 t x = 1 := by
    intro x hx
    unfold H24_lamt
    rw [ite_eq_right hx]
  refine ⟨H24_lamt r ρ0 t, ⟨fun k hk => ?_, fun k hk => ?_⟩, fun i => ?_, fun ρ hρ => ?_⟩
  · by_cases hkB : k ∈ orbit r ρ0 ∪ orbit r (-ρ0)
    · rw [hin _ (H15_B_mul hkB), hin _ hkB, hin _ (H15_B_neg hkB), (hlaws k hkB).1, (hlaws k hkB).2, one_mul]
      exact ⟨rfl, rfl⟩
    · have h1 : (r : ZMod n) * k ∉ orbit r ρ0 ∪ orbit r (-ρ0) := fun h => hkB (H15_B_back hcop h)
      have h2 : -k ∉ orbit r ρ0 ∪ orbit r (-ρ0) := fun h => hkB (H15_B_nback h)
      rw [hout _ h1, hout _ hkB, hout _ h2, one_pow, mul_one]
      exact ⟨rfl, rfl⟩
  · have hkB : k ∉ orbit r ρ0 ∪ orbit r (-ρ0) := fun h =>
      (Nat.not_even_iff_odd.mpr (hBodd k h)) hk
    exact hout k hkB
  · have hmem : (r : ZMod n) ^ i * ρ0 ∈ orbit r ρ0 := H6_mem_orbit.mpr ⟨i, rfl⟩
    rw [hin _ (Finset.mem_union_left _ hmem)]
    unfold H15_g1
    rw [ite_eq_left hmem, H15_orbF_pow hcop _ ρ0 t hwrap i, H24_Psi_one]
  · apply hout
    intro h
    rcases Finset.mem_union.mp h with h' | h'
    · obtain ⟨i, hi⟩ := H6_mem_orbit.mp h'
      exact (hρ i).1 hi
    · obtain ⟨i, hi⟩ := H6_mem_orbit.mp h'
      exact (hρ i).2 (by rw [hi]; ring)

theorem H24_geom {r M ℓ : ℕ} (hr1 : 1 ≤ r) (hℓM : ℓ ∣ M) :
    (∑ j ∈ range (M / ℓ), r ^ (j * ℓ)) * (r ^ ℓ - 1) = r ^ M - 1 := by
  have h1 : 1 ≤ r ^ ℓ := Nat.one_le_pow _ _ hr1
  have key := geom_sum_mul_add (r ^ ℓ - 1) (M / ℓ)
  rw [Nat.sub_add_cancel h1, ← pow_mul, Nat.mul_div_cancel' hℓM] at key
  have e : ∑ j ∈ range (M / ℓ), r ^ (j * ℓ) = ∑ i ∈ range (M / ℓ), (r ^ ℓ) ^ i := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← pow_mul, mul_comm]
  rw [e, ← key, Nat.add_sub_cancel]

/-- The fibre over `k0` splits into the part in the orbit `O` of `ρ0` and the part in `O^{-1}` (λ = 1 elsewhere). -/
theorem H24_split {a r : ℕ} (hn2 : 2 ∣ n) (hcop : Nat.Coprime r n)
    (hneg : ∀ (i : ℕ) (k : ZMod n), Odd k.val → -k ≠ (r : ZMod n) ^ i * k) {ρ0 k0 : ZMod n}
    (hk0 : k0 ∈ layer0' n a) {lam : ZMod n → L}
    (hl3 : ∀ ρ : ZMod n, (∀ i : ℕ, ρ ≠ (r : ZMod n) ^ i * ρ0 ∧ ρ ≠ -((r : ZMod n) ^ i * ρ0)) → lam ρ = 1) :
    Pmap n a lam k0 = (∏ ρ ∈ (H11_fib a k0).filter (fun ρ => ρ ∈ orbit r ρ0), lam ρ) *
      ∏ ρ ∈ (H11_fib a k0).filter (fun ρ => -ρ ∈ orbit r ρ0), lam ρ := by
  rw [H11_Pmap_eq, ite_eq_left hk0,
    ← Finset.prod_filter_mul_prod_filter_not (H11_fib a k0) (fun ρ => ρ ∈ orbit r ρ0)]
  congr 1
  symm
  apply Finset.prod_subset
  · intro ρ hρ
    rw [Finset.mem_filter] at hρ ⊢
    refine ⟨hρ.1, fun hO => H24_not_both hcop hneg ((H11_mem_fib hn2 a k0 ρ).mp hρ.1).1 hO hρ.2⟩
  · intro ρ hρ hnot
    rw [Finset.mem_filter] at hρ hnot
    apply hl3
    intro i
    constructor
    · intro h
      exact hρ.2 (by rw [h]; exact H6_mem_orbit.mpr ⟨i, rfl⟩)
    · intro h
      exact hnot ⟨hρ.1, by rw [h, neg_neg]; exact H6_mem_orbit.mpr ⟨i, rfl⟩⟩

theorem H24_mul_lt {j ℓ M : ℕ} (hℓ : 0 < ℓ) (hℓM : ℓ ∣ M) (hj : j < M / ℓ) : j * ℓ < M := by
  have h1 : (j + 1) * ℓ ≤ M / ℓ * ℓ := Nat.mul_le_mul_right ℓ hj
  rw [Nat.div_mul_cancel hℓM, add_mul, one_mul] at h1
  exact lt_of_lt_of_le (Nat.lt_add_of_pos_right hℓ) h1

/-- The orbit part of the fibre over `k0 = kk ρ0` contributes `t^E`, `E = ∑_{j < M/ℓ} r^{jℓ}`. -/
theorem H24_S1 {a r : ℕ} (hn2 : 2 ∣ n) (hr : Odd r) (hcop : Nat.Coprime r n) {ρ0 k0 : ZMod n}
    (hρ0 : Odd ρ0.val) (hkk : H11_kk a ρ0 = k0) (hℓM : H15_per hcop k0 ∣ H15_per hcop ρ0) {t : L}
    {lam : ZMod n → L} (hl1 : ∀ i : ℕ, lam ((r : ZMod n) ^ i * ρ0) = t ^ (r ^ i)) :
    ∏ ρ ∈ (H11_fib a k0).filter (fun ρ => ρ ∈ orbit r ρ0), lam ρ =
      t ^ (∑ j ∈ range (H15_per hcop ρ0 / H15_per hcop k0), r ^ (j * H15_per hcop k0)) := by
  have hℓ := H15_per_pos hcop k0
  have hM := H15_per_pos hcop ρ0
  rw [← Finset.prod_pow_eq_pow_sum]
  symm
  apply Finset.prod_nbij (fun j => (r : ZMod n) ^ (j * H15_per hcop k0) * ρ0)
  · intro j _
    rw [Finset.mem_filter, H11_mem_fib hn2]
    refine ⟨⟨H24_pow_odd hn2 hr _ hρ0, ?_⟩, H6_mem_orbit.mpr ⟨_, rfl⟩⟩
    rw [H24_kk_pow hn2 hr, hkk, ← H15_pow_mod_per hcop k0 (j * H15_per hcop k0), Nat.mul_mod_left, pow_zero,
      one_mul]
  · intro j1 hj1 j2 hj2 he
    have h1 := H24_mul_lt hℓ hℓM (Finset.mem_range.mp (Finset.mem_coe.mp hj1))
    have h2 := H24_mul_lt hℓ hℓM (Finset.mem_range.mp (Finset.mem_coe.mp hj2))
    exact Nat.eq_of_mul_eq_mul_right hℓ (H15_pow_inj hcop ρ0 h1 h2 he)
  · intro ρ hρ
    rw [Finset.mem_coe, Finset.mem_filter, H11_mem_fib hn2] at hρ
    obtain ⟨⟨_, hkρ⟩, hO⟩ := hρ
    obtain ⟨i, rfl⟩ := H6_mem_orbit.mp hO
    have hik : (r : ZMod n) ^ i * k0 = k0 := by rw [← hkk, ← H24_kk_pow hn2 hr, hkρ, hkk]
    have hℓi : H15_per hcop k0 ∣ i % H15_per hcop ρ0 := (Nat.dvd_mod_iff hℓM).mpr (H24_per_dvd hcop hik)
    refine ⟨i % H15_per hcop ρ0 / H15_per hcop k0, Finset.mem_coe.mpr (Finset.mem_range.mpr ?_), ?_⟩
    · apply Nat.lt_of_mul_lt_mul_right (a := H15_per hcop k0)
      rw [Nat.div_mul_cancel hℓi, Nat.div_mul_cancel hℓM]
      exact Nat.mod_lt _ hM
    · show (r : ZMod n) ^ (i % H15_per hcop ρ0 / H15_per hcop k0 * H15_per hcop k0) * ρ0 = (r : ZMod n) ^ i * ρ0
      rw [Nat.div_mul_cancel hℓi, H15_pow_mod_per]
  · intro j _
    exact (hl1 _).symm

/-- Case (i): no `i` with `r^i k0 = -k0`; then the inverse part is empty. -/
theorem H24_S2_i {a r : ℕ} (hn2 : 2 ∣ n) (hr : Odd r) {ρ0 k0 : ZMod n} (hkk : H11_kk a ρ0 = k0)
    (hcase : ∀ i : ℕ, (r : ZMod n) ^ i * k0 ≠ -k0) (lam : ZMod n → L) :
    ∏ ρ ∈ (H11_fib a k0).filter (fun ρ => -ρ ∈ orbit r ρ0), lam ρ = 1 := by
  apply Finset.prod_eq_one
  intro ρ hρ
  exfalso
  rw [Finset.mem_filter, H11_mem_fib hn2] at hρ
  obtain ⟨⟨_, hkρ⟩, hO⟩ := hρ
  obtain ⟨i, hi⟩ := H6_mem_orbit.mp hO
  apply hcase i
  rw [← hkk, ← H24_kk_pow hn2 hr, ← hi, H11_kk_neg hn2, hkρ, hkk]

/-- Case (ii): `r^h k0 = -k0`; then `ρ ↦ -(r^h ρ)` carries the orbit part onto the inverse part. -/
theorem H24_S2_ii {a r : ℕ} (hn2 : 2 ∣ n) (hr : Odd r) (hcop : Nat.Coprime r n) {ρ0 k0 : ZMod n}
    (_hkk : H11_kk a ρ0 = k0) {h : ℕ} (hh : (r : ZMod n) ^ h * k0 = -k0) {lam : ZMod n → L}
    (hl : lam ∈ (topData0 n r : Set (ZMod n → L))) :
    ∏ ρ ∈ (H11_fib a k0).filter (fun ρ => -ρ ∈ orbit r ρ0), lam ρ =
      ((∏ ρ ∈ (H11_fib a k0).filter (fun ρ => ρ ∈ orbit r ρ0), lam ρ) ^ (r ^ h))⁻¹ := by
  obtain ⟨w, hw⟩ := H24_inv_pow hcop h
  rw [← Finset.prod_pow, ← Finset.prod_inv_distrib]
  symm
  apply Finset.prod_nbij' (fun ρ => -((r : ZMod n) ^ h * ρ)) (fun x => (r : ZMod n) ^ w * (-x))
  · intro ρ hρ
    rw [Finset.mem_filter, H11_mem_fib hn2] at hρ ⊢
    obtain ⟨⟨hoddρ, hkρ⟩, hO⟩ := hρ
    refine ⟨⟨H11_odd_neg hn2 (H24_pow_odd hn2 hr h hoddρ), ?_⟩, ?_⟩
    · rw [H11_kk_neg hn2, H24_kk_pow hn2 hr, hkρ, hh, neg_neg]
    · rw [neg_neg]
      obtain ⟨i, rfl⟩ := H6_mem_orbit.mp hO
      exact H6_mem_orbit.mpr ⟨h + i, by ring⟩
  · intro x hx
    rw [Finset.mem_filter, H11_mem_fib hn2] at hx ⊢
    obtain ⟨⟨hoddx, hkx⟩, hO⟩ := hx
    refine ⟨⟨H24_pow_odd hn2 hr w (H11_odd_neg hn2 hoddx), ?_⟩, ?_⟩
    · rw [H24_kk_pow hn2 hr, H11_kk_neg hn2, hkx, ← hh, ← mul_assoc, hw, one_mul]
    · obtain ⟨i, hi⟩ := H6_mem_orbit.mp hO
      rw [hi]
      exact H6_mem_orbit.mpr ⟨w + i, by ring⟩
  · intro ρ _
    simp only [neg_neg]
    rw [← mul_assoc, hw, one_mul]
  · intro x _
    rw [← mul_assoc, show (r : ZMod n) ^ h * (r : ZMod n) ^ w = 1 by rw [mul_comm]; exact hw, one_mul, neg_neg]
  · intro ρ hρ
    rw [Finset.mem_filter, H11_mem_fib hn2] at hρ
    rw [H24_T0_neg hl (H24_pow_odd hn2 hr h hρ.1.1), H24_T0_pow hn2 hr hl hρ.1.1]

/-- Off the `⟨r,-1⟩`-orbit of `k0`, `P_λ = 1`. -/
theorem H24_support {a r : ℕ} (hn2 : 2 ∣ n) (hr : Odd r) {ρ0 k0 : ZMod n} (hkk : H11_kk a ρ0 = k0)
    {lam : ZMod n → L}
    (hl3 : ∀ ρ : ZMod n, (∀ i : ℕ, ρ ≠ (r : ZMod n) ^ i * ρ0 ∧ ρ ≠ -((r : ZMod n) ^ i * ρ0)) → lam ρ = 1) :
    ∀ k : ZMod n, (∀ i : ℕ, k ≠ (r : ZMod n) ^ i * k0 ∧ k ≠ -((r : ZMod n) ^ i * k0)) → Pmap n a lam k = 1 := by
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
      rw [← hρ.2, he, H24_kk_pow hn2 hr, hkk]
    · intro he
      apply (hk i).2
      rw [← hρ.2, he, H11_kk_neg hn2, H24_kk_pow hn2 hr, hkk]
  · rfl

/-- If the orbit of `k0 ∈ μ_{n_odd} ∖ {1}` is self-inverse, it is so at exactly half its length. -/
theorem H24_half_period {a nodd r : ℕ} (hn : n = 2 ^ a * nodd) (hodd : Odd nodd) (hcop : Nat.Coprime r n)
    {k0 : ZMod n} (hk0 : k0 ∈ layer0' n a) {h0 : ℕ} (hh0 : (r : ZMod n) ^ h0 * k0 = -k0) :
    ∃ h : ℕ, (r : ZMod n) ^ h * k0 = -k0 ∧ 0 < h ∧ 2 * h = H15_per hcop k0 := by
  have hℓ := H15_per_pos hcop k0
  refine ⟨h0 % H15_per hcop k0, by rw [H15_pow_mod_per, hh0], ?_⟩
  generalize hhdef : h0 % H15_per hcop k0 = h
  have hh : (r : ZMod n) ^ h * k0 = -k0 := by rw [← hhdef, H15_pow_mod_per, hh0]
  have hlt : h < H15_per hcop k0 := by rw [← hhdef]; exact Nat.mod_lt _ hℓ
  have hpos : 0 < h := by
    rcases Nat.eq_zero_or_pos h with h' | h'
    · rw [h', pow_zero, one_mul] at hh
      exact absurd hh (H11_layer0_ne_neg hn hodd hk0)
    · exact h'
  refine ⟨hpos, ?_⟩
  have hdvd : H15_per hcop k0 ∣ 2 * h :=
    H24_per_dvd hcop (by rw [two_mul, pow_add, mul_assoc, hh, mul_neg, hh, neg_neg])
  obtain ⟨c, hc⟩ := hdvd
  rcases c with _ | _ | c
  · rw [mul_zero] at hc
    omega
  · rw [zero_add, mul_one] at hc
    exact hc
  · have h1 : H15_per hcop k0 * 2 ≤ H15_per hcop k0 * (c + 1 + 1) := Nat.mul_le_mul_left _ (by omega)
    rw [← hc] at h1
    omega

theorem H24_pow_sub_one_pos {r M : ℕ} (hr2 : 2 ≤ r) (hM : 0 < M) : 0 < r ^ M - 1 := by
  have : 2 ≤ r ^ M := le_trans hr2 (Nat.le_self_pow (Nat.pos_iff_ne_zero.mp hM) r)
  omega

/-- The elementary surjectivity: some `λ ∈ 𝒟^0` has `P_λ(k0) = γ` (any admissible `γ`) and `P_λ = 1` off the
`⟨r,-1⟩`-orbit of `k0`. -/
theorem H24_elem {a nodd r : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (hr : Odd r)
    (hr2 : 2 ≤ r) (hcop : Nat.Coprime r n)
    (hneg : ∀ (i : ℕ) (k : ZMod n), Odd k.val → -k ≠ (r : ZMod n) ^ i * k)
    [IsAlgClosed L] {k0 : ZMod n} (hk0 : k0 ∈ layer0' n a) {γ : L} (hγ0 : γ ≠ 0)
    (hγ1 : ∀ i : ℕ, (r : ZMod n) ^ i * k0 = k0 → γ ^ (r ^ i) = γ)
    (hγ2 : ∀ i : ℕ, (r : ZMod n) ^ i * k0 = -k0 → γ ^ (r ^ i) * γ = 1) :
    ∃ lam ∈ (topData0 n r : Set (ZMod n → L)), Pmap n a lam k0 = γ ∧
      ∀ k : ZMod n, (∀ i : ℕ, k ≠ (r : ZMod n) ^ i * k0 ∧ k ≠ -((r : ZMod n) ^ i * k0)) → Pmap n a lam k = 1 := by
  have h8 := H11_eight_dvd hn ha
  have hn2 : 2 ∣ n := dvd_trans (by norm_num) h8
  have hr1 : 1 ≤ r := by omega
  obtain ⟨ρ0, hρ0, hkk⟩ := H11_exists_rho hn ha hodd hk0
  have hMpos := H15_per_pos hcop ρ0
  have hℓM : H15_per hcop k0 ∣ H15_per hcop ρ0 :=
    H24_per_dvd hcop (by rw [← hkk, ← H24_kk_pow hn2 hr, H15_per_spec])
  have hE := H24_geom hr1 hℓM
  have hEpos : 0 < ∑ j ∈ range (H15_per hcop ρ0 / H15_per hcop k0), r ^ (j * H15_per hcop k0) := by
    rcases Nat.eq_zero_or_pos (∑ j ∈ range (H15_per hcop ρ0 / H15_per hcop k0), r ^ (j * H15_per hcop k0))
      with h0 | h0
    · rw [h0, zero_mul] at hE
      have := H24_pow_sub_one_pos hr2 hMpos
      omega
    · exact h0
  by_cases hcase : ∃ i : ℕ, (r : ZMod n) ^ i * k0 = -k0
  · -- case (ii): the orbit of `k0` is self-inverse
    obtain ⟨h0, hh0⟩ := hcase
    obtain ⟨h, hh, hhpos, h2h⟩ := H24_half_period hn hodd hcop hk0 hh0
    have hγh := hγ2 h hh
    have hpos' := H24_pow_sub_one_pos hr2 hhpos
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq γ⁻¹ hpos'
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [zero_pow hpos'.ne'] at hs
      exact inv_ne_zero hγ0 hs.symm
    have hs1 : s ^ (r ^ H15_per hcop k0 - 1) = 1 := by
      have e : r ^ H15_per hcop k0 - 1 = (r ^ h - 1) * (r ^ h + 1) := by
        rw [← h2h, two_mul, pow_add, H11_sq_sub_one _ (Nat.one_le_pow _ _ hr1)]
      rw [e, pow_mul, hs, inv_pow, pow_succ, hγh, inv_one]
    obtain ⟨t, htE⟩ := IsAlgClosed.exists_pow_nat_eq s hEpos
    have ht : t ^ (r ^ H15_per hcop ρ0 - 1) = 1 := by rw [← hE, pow_mul, htE, hs1]
    obtain ⟨lam, hl, hl1, hl3⟩ := H24_lam_of_t hn2 hr hr2 hcop hneg hρ0 ht
    refine ⟨lam, hl, ?_, H24_support hn2 hr hkk hl3⟩
    rw [H24_split hn2 hcop hneg hk0 hl3, H24_S2_ii hn2 hr hcop hkk hh hl, H24_S1 hn2 hr hcop hρ0 hkk hℓM hl1,
      htE]
    have e : s ^ (r ^ h) = γ⁻¹ * s := by
      rw [← hs, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hr1)]
    rw [e, mul_inv, inv_inv]
    field_simp
  · -- case (i): the orbit of `k0` is not self-inverse
    push Not at hcase
    have hγℓ : γ ^ (r ^ H15_per hcop k0 - 1) = 1 := by
      have h1 := hγ1 _ (H15_per_spec hcop k0)
      have h2 : γ ^ (r ^ H15_per hcop k0 - 1) * γ = 1 * γ := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hr1), h1, one_mul]
      exact mul_right_cancel₀ hγ0 h2
    obtain ⟨t, htE⟩ := IsAlgClosed.exists_pow_nat_eq γ hEpos
    have ht : t ^ (r ^ H15_per hcop ρ0 - 1) = 1 := by rw [← hE, pow_mul, htE, hγℓ]
    obtain ⟨lam, hl, hl1, hl3⟩ := H24_lam_of_t hn2 hr hr2 hcop hneg hρ0 ht
    refine ⟨lam, hl, ?_, H24_support hn2 hr hkk hl3⟩
    rw [H24_split hn2 hcop hneg hk0 hl3, H24_S2_i hn2 hr hkk hcase, H24_S1 hn2 hr hcop hρ0 hkk hℓM hl1, htE,
      mul_one]

open Classical in
/-- Surjectivity of `Π` by induction on the support of `g`. -/
theorem H24_surj {a nodd r : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (hr : Odd r)
    (hr2 : 2 ≤ r) (hcop : Nat.Coprime r n)
    (hneg : ∀ (i : ℕ) (k : ZMod n), Odd k.val → -k ≠ (r : ZMod n) ^ i * k) [IsAlgClosed L] :
    ∀ N : ℕ, ∀ g : ZMod n → L, g ∈ (Ggrp n a r : Set (ZMod n → L)) →
      (univ.filter (fun k => g k ≠ 1)).card ≤ N →
      ∃ lam ∈ (topData0 n r : Set (ZMod n → L)), Pmap n a lam = g := by
  have h8 := H11_eight_dvd hn ha
  have hn2 : 2 ∣ n := dvd_trans (by norm_num) h8
  have h2a : 2 ^ a ∣ n := ⟨nodd, hn⟩
  intro N
  induction N with
  | zero =>
    intro g _ hcard
    refine ⟨1, H24_T0_one, ?_⟩
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
    · exact ⟨1, H24_T0_one, by rw [H11_Pmap_one]; funext k; exact (hall k).symm⟩
    push Not at hall
    obtain ⟨k0, hk0⟩ := hall
    have hk0l : k0 ∈ layer0' n a := by
      by_contra h
      exact hk0 (hg.2 k0 h)
    obtain ⟨lB, hlB, hval, hsupp⟩ := H24_elem hn ha hodd hr hr2 hcop hneg hk0l (H24_G_ne hg k0)
      (fun i hi => by rw [← H24_G_pow hcop h2a hg hk0l, hi])
      (fun i hi => by
        rw [← H24_G_pow hcop h2a hg hk0l, hi, H24_G_neg hg hk0l, inv_mul_cancel₀ (H24_G_ne hg k0)])
    have hpG : Pmap n a lB ∈ (Ggrp n a r : Set (ZMod n → L)) := H24_Pmap_mem hn2 hr hcop h2a hlB
    have hg'G : g * (Pmap n a lB)⁻¹ ∈ (Ggrp n a r : Set (ZMod n → L)) := H24_G_mul hg (H24_G_inv hpG)
    have hg'k0 : (g * (Pmap n a lB)⁻¹) k0 = 1 := by
      rw [Pi.mul_apply, Pi.inv_apply, hval]
      exact mul_inv_cancel₀ (H24_G_ne hg k0)
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
        by_cases horb : ∃ i : ℕ, k = (r : ZMod n) ^ i * k0 ∨ k = -((r : ZMod n) ^ i * k0)
        · exfalso
          obtain ⟨i, hi | hi⟩ := horb
          · apply hk.2
            rw [hi, H24_G_pow hcop h2a hg'G hk0l, hg'k0, one_pow]
          · apply hk.2
            rw [hi, H24_G_neg hg'G (H24_l0_pow hcop h2a i hk0l), H24_G_pow hcop h2a hg'G hk0l, hg'k0,
              one_pow, inv_one]
        · push Not at horb
          have hp1 : Pmap n a lB k = 1 := hsupp k horb
          intro hgk
          apply hk.2
          rw [Pi.mul_apply, Pi.inv_apply, hp1, hgk, inv_one, mul_one]
    have hcard' := lt_of_lt_of_le (Finset.card_lt_card hsub) hcard
    obtain ⟨l', hl', hP'⟩ := ih _ hg'G (Nat.lt_succ_iff.mp hcard')
    refine ⟨l' * lB, H24_T0_mul hl' hlB, ?_⟩
    rw [H11_Pmap_mul, hP']
    funext k
    rw [Pi.mul_apply, Pi.mul_apply, Pi.inv_apply, mul_assoc, inv_mul_cancel₀ (H24_G_ne hpG k), mul_one]

end Surj


/-! ## 4. Step 7, first part: `|(τ-1)G| · |G^τ| = |G|` (the first isomorphism theorem, `G` for `r`) -/

section Part1

variable {n a nodd : ℕ} [NeZero n] {L : Type*} [Field L]

theorem H24_tau_G (hn : n = 2 ^ a * nodd) (hodd : Odd nodd) {r : ℕ} (hcop : Nat.Coprime r n) {g : ZMod n → L}
    (hg : g ∈ (Ggrp n a r : Set (ZMod n → L))) : tauG n a g ∈ (Ggrp n a r : Set (ZMod n → L)) := by
  have h2a : 2 ^ a ∣ n := ⟨nodd, hn⟩
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun k hk => H12_tau_nmem g hk⟩
  · rw [H12_tau_mem g (H24_l0_mul hcop h2a hk), H12_tau_mem g hk, mul_left_comm,
      (hg.1 _ (H12_X_mul2 hn hodd hk)).1]
  · rw [H12_tau_mem g (H12_X_neg hn hk), H12_tau_mem g hk, mul_neg, (hg.1 _ (H12_X_mul2 hn hodd hk)).2]

theorem H24_step7_part1 (hn : n = 2 ^ a * nodd) (hodd : Odd nodd) {r : ℕ} (hcop : Nat.Coprime r n) :
    Nat.card ((fun g => tauG n a g / g) '' (Ggrp n a r : Set (ZMod n → L))) *
        Nat.card {g : ZMod n → L // g ∈ (Ggrp n a r : Set (ZMod n → L)) ∧ tauG n a g = g} =
      Nat.card (Ggrp n a r : Set (ZMod n → L)) :=
  H12_first_iso (Ggrp n a r) (tauG n a) (fun _g hg x => H24_G_ne hg x) (fun _g hg _g' hg' => H24_G_mul hg hg')
    (fun _g hg => H24_G_inv hg) (fun _g hg => H24_tau_G hn hodd hcop hg) H12_tau_mul H12_tau_inv

end Part1

/-! ## 5. Step 7, second part: `|K_n| = 4 ∏_i (r^{L_i}-1)` (the `r = 3` count with `3 ↦ r`) -/

section Count

variable {n a nodd : ℕ} [NeZero n] {L : Type*} [Field L]

/-- The homogeneous laws (h1_r), (h3), (h4) on all of `μ_n` (the set `K_n` for `r`). -/
def H24_K (r : ℕ) (lam : ZMod n → L) : Prop :=
  (∀ k, lam ((r : ZMod n) * k) = lam k ^ r) ∧ (∀ k, lam k * lam (-k) = 1) ∧
    ∀ k, lam k * lam (k + half n) = lam (half n) * lam (2 * k)

/-- `K₁ := {λ ∈ K : λ(-1) = 1}`. -/
def H24_K1 (r : ℕ) : Set (ZMod n → L) := {lam | H24_K r lam ∧ lam (half n) = 1}

theorem H24_pow_odd_sq {r : ℕ} (hr : Odd r) {s : L} (hs : s ^ 2 = 1) : s ^ r = s := by
  obtain ⟨j, hj⟩ := hr
  rw [hj, pow_succ, pow_mul, hs, one_pow, one_mul]

theorem H24_K_ne {r : ℕ} {lam : ZMod n → L} (hK : H24_K r lam) (k : ZMod n) : lam k ≠ 0 :=
  left_ne_zero_of_mul_eq_one (hK.2.1 k)

theorem H24_K1_mul {r : ℕ} {x y : ZMod n → L} (hx : x ∈ (H24_K1 r : Set (ZMod n → L)))
    (hy : y ∈ (H24_K1 r : Set (ZMod n → L))) : x * y ∈ (H24_K1 r : Set (ZMod n → L)) := by
  obtain ⟨⟨x1, x3, x4⟩, xm⟩ := hx
  obtain ⟨⟨y1, y3, y4⟩, ym⟩ := hy
  refine ⟨⟨fun k => ?_, fun k => ?_, fun k => ?_⟩, ?_⟩
  · simp only [Pi.mul_apply]; rw [x1, y1, mul_pow]
  · simp only [Pi.mul_apply]; linear_combination (y k * y (-k)) * x3 k + y3 k
  · simp only [Pi.mul_apply]
    linear_combination (y k * y (k + half n)) * x4 k + (x (half n) * x (2 * k)) * y4 k
  · simp only [Pi.mul_apply]; rw [xm, ym, one_mul]

theorem H24_K1_inv {r : ℕ} {x : ZMod n → L} (hx : x ∈ (H24_K1 r : Set (ZMod n → L))) :
    x⁻¹ ∈ (H24_K1 r : Set (ZMod n → L)) := by
  obtain ⟨⟨x1, x3, x4⟩, xm⟩ := hx
  refine ⟨⟨fun k => ?_, fun k => ?_, fun k => ?_⟩, ?_⟩
  · simp only [Pi.inv_apply]; rw [x1, inv_pow]
  · simp only [Pi.inv_apply]; rw [← mul_inv, x3, inv_one]
  · simp only [Pi.inv_apply]; rw [← mul_inv, ← mul_inv, x4]
  · simp only [Pi.inv_apply]; rw [xm, inv_one]

theorem H24_res_D0 (h2 : 2 ∣ n) {r : ℕ} (hr : Odd r) {lam : ZMod n → L} (hK : H24_K r lam) :
    H12_res lam ∈ (topData0 n r : Set (ZMod n → L)) := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · have hk' : k ∈ topLayer n := (H12_mem_topLayer k).mpr hk
    have hrk : (r : ZMod n) * k ∈ topLayer n := (H12_mem_topLayer _).mpr (H24_odd_mulr h2 hr hk)
    have hnk : -k ∈ topLayer n := (H12_mem_topLayer _).mpr (H11_odd_neg h2 hk)
    simp only [H12_res, ite_eq_left hk', ite_eq_left hrk, ite_eq_left hnk]
    exact ⟨hK.1 k, hK.2.1 k⟩
  · have hk' : k ∉ topLayer n := by rw [H12_mem_topLayer]; exact Nat.not_odd_iff_even.mpr hk
    simp only [H12_res, ite_eq_right hk']

/-! ### The descent (s4_normfree.tex:80-83), for `K` of `r` -/

theorem H24_descent (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (_hodd : Odd nodd) (h2 : 2 ∣ n) {r : ℕ}
    {lam : ZMod n → L} (hK : H24_K r lam) (hm1 : lam (half n) = 1) :
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

theorem H24_C1 (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h2 : 2 ∣ n) {r : ℕ} {lam : ZMod n → L}
    (hK : H24_K r lam) (hm1 : lam (half n) = 1) {α : ZMod n} (hα : (nodd : ZMod n) * α = 0) :
    lam (α + half n) = H12_N lam (a - 1) (α + half n) := by
  have hY : (nodd : ZMod n) * (α + half n) ≠ 0 := by
    rw [mul_add, hα, zero_add, H12_nodd_half hodd h2]; exact H12_half_ne h2
  obtain ⟨i, hi, z, hz, hzk⟩ := H12_decomp hn hodd h2 _ hY
  have hia : i = a - 1 := by
    by_contra hne
    exact H12_T2 hn (by omega) hodd h2 (by omega : i < a - 1) hz hα hzk.symm
  subst hia
  rw [hzk]
  exact H24_descent hn ha hodd h2 hK hm1 (a - 1) le_rfl z hz

theorem H24_C2 (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h2 : 2 ∣ n) {r : ℕ} {lam : ZMod n → L}
    (hK : H24_K r lam) (hm1 : lam (half n) = 1) (h1 : ∀ ρ ∈ topLayer n, lam ρ = 1) {k : ZMod n}
    (hk : (nodd : ZMod n) * k ≠ 0) : lam k = 1 := by
  obtain ⟨i, hi, z, hz, hzk⟩ := H12_decomp hn hodd h2 _ hk
  rw [hzk, H24_descent hn ha hodd h2 hK hm1 i (by omega) z hz, H12_N_allone h1]

/-! ### The extension `λ := M(λ₀)·g`, for `r` -/

theorem H24_N_r (h2 : 2 ∣ n) {r : ℕ} (hr : Odd r) (hcop : Nat.Coprime r n) (lam : ZMod n → L)
    (hlam : ∀ ρ ∈ topLayer n, lam ((r : ZMod n) * ρ) = lam ρ ^ r) (i : ℕ) (k : ZMod n) :
    H12_N lam i ((r : ZMod n) * k) = H12_N lam i k ^ r := by
  obtain ⟨v, hv⟩ : ∃ v : ZMod n, v * (r : ZMod n) = 1 := by
    obtain ⟨u, hu⟩ := H24_unit hcop
    exact ⟨↑u⁻¹, by rw [← hu, Units.inv_mul]⟩
  have hψr : ZMod.castHom h2 (ZMod 2) (r : ZMod n) = 1 := by
    rw [map_natCast]; exact ZMod.natCast_eq_one_iff_odd.mpr hr
  have hψv : ZMod.castHom h2 (ZMod 2) v = 1 := by
    have e := congrArg (ZMod.castHom h2 (ZMod 2)) hv
    rw [map_mul, map_one, hψr, mul_one] at e; exact e
  unfold H12_N
  rw [← Finset.prod_pow]
  apply Finset.prod_nbij' (fun ρ => v * ρ) (fun ρ => (r : ZMod n) * ρ)
  · intro ρ hρ
    rw [Finset.mem_filter, H12_mem_top h2] at hρ ⊢
    refine ⟨by rw [map_mul, hψv, hρ.1, one_mul], ?_⟩
    rw [mul_left_comm, hρ.2, ← mul_assoc, hv, one_mul]
  · intro ρ hρ
    rw [Finset.mem_filter, H12_mem_top h2] at hρ ⊢
    refine ⟨by rw [map_mul, hψr, hρ.1, one_mul], ?_⟩
    rw [mul_left_comm, hρ.2]
  · intro ρ _; rw [← mul_assoc, mul_comm (r : ZMod n) v, hv, one_mul]
  · intro ρ _; rw [← mul_assoc, hv, one_mul]
  · intro ρ hρ
    have hvρ : v * ρ ∈ topLayer n := by
      rw [Finset.mem_filter, H12_mem_top h2] at hρ
      rw [H12_mem_top h2, map_mul, hψv, hρ.1, one_mul]
    rw [← hlam _ hvρ, ← mul_assoc, mul_comm (r : ZMod n) v, hv, one_mul]

theorem H24_M_r (h2 : 2 ∣ n) {r : ℕ} (hr : Odd r) (hcop : Nat.Coprime r n) (lam0 : ZMod n → L)
    (hlam : ∀ ρ ∈ topLayer n, lam0 ((r : ZMod n) * ρ) = lam0 ρ ^ r) (k : ZMod n) :
    H12_M a lam0 ((r : ZMod n) * k) = H12_M a lam0 k ^ r := by
  unfold H12_M
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl (fun i _ => H24_N_r h2 hr hcop lam0 hlam i k)

theorem H24_Grall (hn : n = 2 ^ a * nodd) (hodd : Odd nodd) {r : ℕ} (hcop : Nat.Coprime r n) {g : ZMod n → L}
    (hg : g ∈ (Ggrp n a r : Set (ZMod n → L))) (k : ZMod n) : g ((r : ZMod n) * k) = g k ^ r := by
  by_cases hk : k ∈ layer0' n a
  · exact (hg.1 k hk).1
  · have hrk : (r : ZMod n) * k ∉ layer0' n a := by
      intro h; apply hk
      rw [H12_mem_X' hn hodd] at h ⊢
      obtain ⟨u, hu⟩ := H24_unit hcop
      refine ⟨?_, fun h0 => h.2 (by rw [h0, mul_zero])⟩
      have e : k = ↑u⁻¹ * ((r : ZMod n) * k) := by rw [← mul_assoc, ← hu, Units.inv_mul, one_mul]
      rw [e, mul_left_comm, h.1, mul_zero]
    rw [hg.2 k hk, hg.2 _ hrk, one_pow]

theorem H24_Gnegall (hn : n = 2 ^ a * nodd) {r : ℕ} {g : ZMod n → L} (hg : g ∈ (Ggrp n a r : Set (ZMod n → L)))
    (k : ZMod n) : g k * g (-k) = 1 := by
  by_cases hk : k ∈ layer0' n a
  · rw [mul_comm]; exact (hg.1 k hk).2
  · have hk' : -k ∉ layer0' n a := fun h => hk (by have e := H12_X_neg hn h; rwa [neg_neg] at e)
    rw [hg.2 k hk, hg.2 _ hk', one_mul]

theorem H24_construct (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) {r : ℕ} (hr : Odd r)
    (hcop : Nat.Coprime r n) {lam0 : ZMod n → L} (hD : lam0 ∈ (topData0 n r : Set (ZMod n → L)))
    {g : ZMod n → L} (hg : g ∈ (Ggrp n a r : Set (ZMod n → L))) (hP : Pmap n a lam0 = tauG n a g / g) :
    (fun k => H12_M a lam0 k * g k) ∈ (H24_K1 r : Set (ZMod n → L)) ∧
      H12_res (fun k => H12_M a lam0 k * g k) = lam0 := by
  have ha1 : 1 ≤ a := by omega
  have h2 : 2 ∣ n := H12_two_dvd hn ha1
  have h4 : 4 ∣ n := H12_four_dvd hn (by omega)
  obtain ⟨hD1, hD2⟩ := hD
  have hlr : ∀ ρ ∈ topLayer n, lam0 ((r : ZMod n) * ρ) = lam0 ρ ^ r :=
    fun ρ hρ => (hD1 ρ ((H12_mem_topLayer ρ).mp hρ)).1
  have hlneg : ∀ ρ ∈ topLayer n, lam0 ρ * lam0 (-ρ) = 1 :=
    fun ρ hρ => (hD1 ρ ((H12_mem_topLayer ρ).mp hρ)).2
  have hgY : ∀ k, (nodd : ZMod n) * k ≠ 0 → g k = 1 :=
    fun k hk => hg.2 k (fun hX => hk ((H12_mem_X' hn hodd).mp hX).1)
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
    rw [H12_M_Y hn ha1 h2 lam0 hα, H12_M_Y hn ha1 h2 lam0 (k := 2 * α) (by rw [mul_left_comm, hα, mul_zero]),
      hgY _ hαm, H12_M_half hn ha1 hodd h2 lam0 hα, one_mul, one_mul, mul_one]
    by_cases h0 : α = 0
    · subst h0
      rw [zero_add, hNm, mul_zero, mul_one]
    · have hX : α ∈ layer0' n a := (H12_mem_X' hn hodd).mpr ⟨hα, h0⟩
      rw [← H12_Pmap_eq lam0 hX, hP, Pi.div_apply, H12_tau_mem g hX, mul_div_assoc',
        mul_div_cancel_left₀ _ (H24_G_ne hg α)]
  refine ⟨⟨⟨fun k => ?_, fun k => ?_, fun k => ?_⟩, ?_⟩, ?_⟩
  · show H12_M a lam0 ((r : ZMod n) * k) * g ((r : ZMod n) * k) = (H12_M a lam0 k * g k) ^ r
    rw [H24_M_r h2 hr hcop lam0 hlr, H24_Grall hn hodd hcop hg k, mul_pow]
  · show H12_M a lam0 k * g k * (H12_M a lam0 (-k) * g (-k)) = 1
    calc H12_M a lam0 k * g k * (H12_M a lam0 (-k) * g (-k))
        = (H12_M a lam0 k * H12_M a lam0 (-k)) * (g k * g (-k)) := by ring
      _ = 1 := by rw [H12_M_neg h2 lam0 hlneg, H24_Gnegall hn hg k, one_mul]
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

/-! ### `res(K₁) = Π⁻¹((τ-1)G)` and `ker res ≃ {±1} × G^τ`, for `r` -/

theorem H24_gl_mem (hn : n = 2 ^ a * nodd) {r : ℕ} (hcop : Nat.Coprime r n) {lam : ZMod n → L}
    (hK : H24_K r lam) :
    (fun k => if k ∈ layer0' n a then lam k else 1) ∈ (Ggrp n a r : Set (ZMod n → L)) := by
  have h2a : 2 ^ a ∣ n := ⟨nodd, hn⟩
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun k hk => by simp only [ite_eq_right hk]⟩
  · simp only [ite_eq_left (H24_l0_mul hcop h2a hk), ite_eq_left hk]; exact hK.1 k
  · simp only [ite_eq_left (H12_X_neg hn hk), ite_eq_left hk]; rw [mul_comm]; exact hK.2.1 k

theorem H24_res_Pmap (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) {r : ℕ} (hcop : Nat.Coprime r n)
    {lam : ZMod n → L} (hl : lam ∈ (H24_K1 r : Set (ZMod n → L))) :
    Pmap n a (H12_res lam) ∈ (fun g => tauG n a g / g) '' (Ggrp n a r : Set (ZMod n → L)) := by
  have ha1 : 1 ≤ a := by omega
  have h2 := H12_two_dvd hn ha1
  obtain ⟨hK, hm1⟩ := hl
  refine ⟨fun k => if k ∈ layer0' n a then lam k else 1, H24_gl_mem hn hcop hK, ?_⟩
  funext k
  show tauG n a (fun k => if k ∈ layer0' n a then lam k else 1) k / (if k ∈ layer0' n a then lam k else 1) =
    Pmap n a (H12_res lam) k
  by_cases hk : k ∈ layer0' n a
  · rw [H12_tau_mem _ hk, ite_eq_left hk, H12_Pmap_eq _ hk]
    simp only [ite_eq_left (H12_X_mul2 hn hodd hk)]
    have hY := ((H12_mem_X' hn hodd).mp hk).1
    have e4 := hK.2.2 k
    rw [hm1, one_mul] at e4
    rw [← e4, H12_N_congr (H12_res_top lam), ← H24_C1 hn ha hodd h2 hK hm1 hY,
      mul_div_cancel_left₀ _ (H24_K_ne hK k)]
  · rw [H12_tau_nmem _ hk, ite_eq_right hk, H12_Pmap_off _ hk, div_one]

theorem H24_ker_tau (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) {r : ℕ} {lam : ZMod n → L}
    (hl : lam ∈ (H24_K1 r : Set (ZMod n → L))) (h1 : ∀ ρ ∈ topLayer n, lam ρ = 1) :
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
    rw [← e4, H24_C1 hn ha hodd h2 hK hm1 hY, H12_N_allone h1, mul_one]
  · rw [H12_tau_nmem _ hk]; simp only [ite_eq_right hk]

theorem H24_ker_inv (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) {r : ℕ} (hr : Odd r)
    (hcop : Nat.Coprime r n) {s : L} (hs : s ^ 2 = 1) {g : ZMod n → L} (hg : g ∈ (Ggrp n a r : Set (ZMod n → L)))
    (hτ : tauG n a g = g) :
    (fun k => if k = 0 then s else g k) ∈ (H24_K1 r : Set (ZMod n → L)) ∧
      H12_res (fun k => if k = 0 then s else g k) = 1 := by
  have ha1 : 1 ≤ a := by omega
  have h2 := H12_two_dvd hn ha1
  have hm0 := H12_half_ne h2 (n := n)
  have hg1 : ∀ k, (nodd : ZMod n) * k ≠ 0 → g k = 1 :=
    fun k hk => hg.2 k (fun hX => hk ((H12_mem_X' hn hodd).mp hX).1)
  have hgm : g (half n) = 1 := hg1 _ (by rw [H12_nodd_half hodd h2]; exact hm0)
  have hgY : ∀ α, (nodd : ZMod n) * α = 0 → g (2 * α) = g α := by
    intro α hα
    by_cases h0 : α = 0
    · rw [h0, mul_zero]
    · have hX := (H12_mem_X' hn hodd).mpr ⟨hα, h0⟩
      have e := congrFun hτ α
      rwa [H12_tau_mem g hX] at e
  have hsr : s ^ r = s := H24_pow_odd_sq hr hs
  refine ⟨⟨⟨fun k => ?_, fun k => ?_, fun k => ?_⟩, ?_⟩, ?_⟩
  · show (if (r : ZMod n) * k = 0 then s else g ((r : ZMod n) * k)) = (if k = 0 then s else g k) ^ r
    by_cases hk : k = 0
    · rw [ite_eq_left (by rw [hk, mul_zero]), ite_eq_left hk, hsr]
    · rw [ite_eq_right (fun h => hk ((H24_unit hcop).mul_right_eq_zero.mp h)), ite_eq_right hk,
        H24_Grall hn hodd hcop hg k]
  · show (if k = 0 then s else g k) * (if -k = 0 then s else g (-k)) = 1
    by_cases hk : k = 0
    · rw [ite_eq_left hk, ite_eq_left (by rw [hk, neg_zero]), ← sq, hs]
    · rw [ite_eq_right hk, ite_eq_right (neg_ne_zero.mpr hk), H24_Gnegall hn hg k]
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

theorem H24_ker_card (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) {r : ℕ} (hr : Odd r)
    (hcop : Nat.Coprime r n) :
    Nat.card {lam : ZMod n → L // lam ∈ (H24_K1 r : Set (ZMod n → L)) ∧ H12_res lam = 1} =
      Nat.card {s : L // s ^ 2 = 1} *
        Nat.card {g : ZMod n → L // g ∈ (Ggrp n a r : Set (ZMod n → L)) ∧ tauG n a g = g} := by
  have ha1 : 1 ≤ a := by omega
  have h2 : 2 ∣ n := H12_two_dvd hn ha1
  have kf1 : ∀ lam : ZMod n → L, H12_res lam = 1 → ∀ ρ ∈ topLayer n, lam ρ = 1 := by
    intro lam hr' ρ hρ
    have e := congrFun hr' ρ
    simp only [H12_res, ite_eq_left hρ, Pi.one_apply] at e
    exact e
  rw [← Nat.card_prod]
  apply Nat.card_congr
  exact
    { toFun := fun lam => (⟨lam.1 0, by
          have e := lam.2.1.1.2.1 0
          rw [neg_zero] at e; rw [sq]; exact e⟩,
        ⟨fun k => if k ∈ layer0' n a then lam.1 k else 1, H24_gl_mem hn hcop lam.2.1.1,
          H24_ker_tau hn ha hodd lam.2.1 (kf1 _ lam.2.2)⟩)
      invFun := fun p => ⟨fun k => if k = 0 then p.1.1 else p.2.1 k,
        H24_ker_inv hn ha hodd hr hcop p.1.2 p.2.2.1 p.2.2.2⟩
      left_inv := fun lam => Subtype.ext (funext fun k => by
        show (if k = 0 then lam.1 0 else (if k ∈ layer0' n a then lam.1 k else 1)) = lam.1 k
        by_cases hk0 : k = 0
        · rw [ite_eq_left hk0, hk0]
        · rw [ite_eq_right hk0]
          by_cases hX : k ∈ layer0' n a
          · rw [ite_eq_left hX]
          · rw [ite_eq_right hX]
            have hY : (nodd : ZMod n) * k ≠ 0 := fun h => hX ((H12_mem_X' hn hodd).mpr ⟨h, hk0⟩)
            exact (H24_C2 hn ha hodd h2 lam.2.1.1 lam.2.1.2 (kf1 _ lam.2.2) hY).symm)
      right_inv := fun p => by
        obtain ⟨⟨s, hs⟩, ⟨g, hg, hτ⟩⟩ := p
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext (funext fun k => ?_))
        · show (if (0 : ZMod n) = 0 then s else g 0) = s
          rw [ite_eq_left rfl]
        · show (if k ∈ layer0' n a then (if k = 0 then s else g k) else 1) = g k
          by_cases hX : k ∈ layer0' n a
          · rw [ite_eq_left hX, ite_eq_right ((H12_mem_X' hn hodd).mp hX).2]
          · rw [ite_eq_right hX, hg.2 k hX] }

/-- `K ≃ {±1} × K₁`, `λ ↦ (λ(-1), λ(-1)·λ)`. -/
theorem H24_K_card (h2 : 2 ∣ n) {r : ℕ} (hr : Odd r) :
    Nat.card {lam : ZMod n → L // H24_K r lam} =
      Nat.card {s : L // s ^ 2 = 1} * Nat.card (H24_K1 r : Set (ZMod n → L)) := by
  have hS : ∀ lam : ZMod n → L, H24_K r lam → lam (half n) ^ 2 = 1 := fun lam hl => by
    have e := hl.2.1 (half n); rw [H12_neg_half h2] at e; rw [sq]; exact e
  rw [← Nat.card_prod]
  apply Nat.card_congr
  exact
    { toFun := fun lam => (⟨lam.1 (half n), hS lam.1 lam.2⟩, ⟨fun k => lam.1 (half n) * lam.1 k, by
        obtain ⟨l1, l3, l4⟩ := lam.2
        have hs := hS lam.1 lam.2
        refine ⟨⟨fun k => ?_, fun k => ?_, fun k => ?_⟩, ?_⟩
        · show lam.1 (half n) * lam.1 ((r : ZMod n) * k) = (lam.1 (half n) * lam.1 k) ^ r
          rw [l1 k, mul_pow, H24_pow_odd_sq hr hs]
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
        · show p.1.1 * p.2.1 ((r : ZMod n) * k) = (p.1.1 * p.2.1 k) ^ r
          rw [l1 k, mul_pow, H24_pow_odd_sq hr hs]
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

end Count

/-! ## 6. Row 24d -/

/-- Row 24d — proof of Theorem 6.4, Steps 6-7 (s6_primes.tex:183-184, "word for word"), algebraically closed `L` of
characteristic `r`: `Π : 𝒟^0 → G` is onto, `|(τ-1)G| · |G^τ| = |G|`, and the group of solutions of the homogeneous laws for `r`
has `4 ∏_i (r^{L_i}-1)` elements. -/
theorem thm_6_4_step67_proved (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a)
    (hodd : Odd nodd) (hr : ¬ r ∣ pp n * n) (hr1 : r % 2 ^ a ≠ 2 ^ a - 1) {L : Type*} [Field L] [CharP L r]
    [IsAlgClosed L] :
    Set.SurjOn (Pmap n a) (topData0 n r : Set (ZMod n → L)) (Ggrp n a r) ∧
    Nat.card ((fun g => tauG n a g / g) '' (Ggrp n a r : Set (ZMod n → L))) *
        Nat.card {g : ZMod n → L // g ∈ (Ggrp n a r : Set (ZMod n → L)) ∧ tauG n a g = g} =
      Nat.card (Ggrp n a r : Set (ZMod n → L)) ∧
    Nat.card {lam : ZMod n → L // (∀ k, lam ((r : ZMod n) * k) = lam k ^ r) ∧ (∀ k, lam k * lam (-k) = 1) ∧
      ∀ k, lam k * lam (k + half n) = lam (half n) * lam (2 * k)} = 4 * pairProd n r := by
  have hp : r.Prime := Fact.out
  have ha1 : 1 ≤ a := by omega
  have htwo : 2 ∣ n := H12_two_dvd hn ha1
  have h2a : 2 ^ a ∣ n := ⟨nodd, hn⟩
  have hcop : Nat.Coprime r n :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => hr (Dvd.dvd.mul_left h _))
  have hrodd : Odd r := Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right htwo hcop)
  have hr2 : 2 ≤ r := hp.two_le
  have hneg := H6_hneg hn ha hrodd hr1
  -- Step 6: `Π` is onto `G`
  have hsurj : Set.SurjOn (Pmap n a) (topData0 n r : Set (ZMod n → L)) (Ggrp n a r) := by
    intro g hg
    obtain ⟨lam, hl, he⟩ := H24_surj hn ha hodd hrodd hr2 hcop hneg _ g hg le_rfl
    exact ⟨lam, hl, he⟩
  -- Step 7, first part
  have eG := H24_step7_part1 hn hodd hcop (L := L)
  refine ⟨hsurj, eG, ?_⟩
  -- Step 7, second part
  obtain ⟨ω, hω⟩ : ∃ ω : L, IsPrimitiveRoot ω n := by
    have : NeZero ((n : ℕ) : L) := ⟨H15_n_ne (L := L) hr⟩
    exact HasEnoughRootsOfUnity.exists_isPrimitiveRoot L n
  have hD0card : Nat.card (topData0 n r : Set (ZMod n → L)) = pairProd n r :=
    (thm_6_4_step2_proved n a nodd r hn ha hodd hr hr1 0 ω hω).2
  have h2L : ((2 : ℕ) : L) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff L r]
    intro h
    have := Nat.le_of_dvd two_pos h
    obtain ⟨j, hj⟩ := hrodd
    omega
  have hS2 : Nat.card {s : L // s ^ 2 = 1} = 2 := H12_card_roots 2 h2L
  -- (A) `|K| = 2 |K₁|`
  have eA : Nat.card {lam : ZMod n → L // H24_K r lam} = 2 * Nat.card (H24_K1 r : Set (ZMod n → L)) := by
    rw [H24_K_card htwo hrodd, hS2]
  -- (B) `|K₁| = |ker res| · |res(K₁)|`
  have eB : Nat.card (H24_K1 r : Set (ZMod n → L)) =
      Nat.card {x : ZMod n → L // x ∈ (H24_K1 r : Set (ZMod n → L)) ∧ H12_res x = 1} *
        Nat.card (H12_res '' (H24_K1 r : Set (ZMod n → L))) := by
    rw [← H12_preimage_card (H24_K1 r : Set (ZMod n → L)) H12_res (H12_res '' (H24_K1 r : Set (ZMod n → L)))
      (fun x hx k => H24_K_ne hx.1 k) (fun x hx y hy => H24_K1_mul hx hy) (fun x hx => H24_K1_inv hx)
      (fun x _ y _ => H12_res_mul x y) (fun x _ => H12_res_inv x)
      (fun x hx j => by
        by_cases hj : j ∈ topLayer n
        · rw [H12_res_top x j hj]; exact H24_K_ne hx.1 j
        · simp only [H12_res, ite_eq_right hj]; exact one_ne_zero)
      (subset_refl _)]
    apply Nat.card_congr
    exact
      { toFun := fun x => ⟨x.1, x.2, x.1, x.2, rfl⟩
        invFun := fun x => ⟨x.1, x.2.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  -- (C) `|ker res| = 2 |G^τ|`
  have eC := H24_ker_card hn ha hodd hrodd hcop (L := L)
  rw [hS2] at eC
  -- (D) `res(K₁) = Π⁻¹((τ-1)G)`
  have eD : H12_res '' (H24_K1 r : Set (ZMod n → L)) =
      {lam0 | lam0 ∈ (topData0 n r : Set (ZMod n → L)) ∧
        Pmap n a lam0 ∈ (fun g => tauG n a g / g) '' (Ggrp n a r : Set (ZMod n → L))} := by
    ext lam0
    constructor
    · rintro ⟨lam, hl, rfl⟩
      exact ⟨H24_res_D0 htwo hrodd hl.1, H24_res_Pmap hn ha hodd hcop hl⟩
    · rintro ⟨hD, g, hg, hgP⟩
      exact ⟨_, (H24_construct hn ha hodd hrodd hcop hD hg hgP.symm).1,
        (H24_construct hn ha hodd hrodd hcop hD hg hgP.symm).2⟩
  -- (E), (F): preimages under `Π`
  have h6map : ∀ lam ∈ (topData0 n r : Set (ZMod n → L)), Pmap n a lam ∈ (Ggrp n a r : Set (ZMod n → L)) :=
    fun lam hl => H24_Pmap_mem htwo hrodd hcop h2a hl
  have hPne : ∀ x ∈ (topData0 n r : Set (ZMod n → L)), ∀ j, Pmap n a x j ≠ 0 :=
    fun x hx j => H24_G_ne (h6map x hx) j
  have hHsub : (fun g => tauG n a g / g) '' (Ggrp n a r : Set (ZMod n → L)) ⊆
      Pmap n a '' (topData0 n r : Set (ZMod n → L)) := by
    rintro y ⟨g, hg, rfl⟩
    have hmem : tauG n a g / g ∈ (Ggrp n a r : Set (ZMod n → L)) := by
      rw [div_eq_mul_inv]
      exact H24_G_mul (H24_tau_G hn hodd hcop hg) (H24_G_inv hg)
    exact hsurj hmem
  have eE := H12_preimage_card (topData0 n r : Set (ZMod n → L)) (Pmap n a)
    ((fun g => tauG n a g / g) '' (Ggrp n a r : Set (ZMod n → L))) (fun x hx k => H24_T0_ne hx k)
    (fun x hx y hy => H24_T0_mul hx hy) (fun x hx => H24_T0_inv hx) (fun x _ y _ => H11_Pmap_mul a x y)
    (fun x _ => H12_Pmap_inv x) hPne hHsub
  have eF : Nat.card (topData0 n r : Set (ZMod n → L)) =
      Nat.card {x : ZMod n → L // x ∈ (topData0 n r : Set (ZMod n → L)) ∧ Pmap n a x = 1} *
        Nat.card (Ggrp n a r : Set (ZMod n → L)) := by
    rw [← H12_preimage_card (topData0 n r : Set (ZMod n → L)) (Pmap n a) (Ggrp n a r : Set (ZMod n → L))
      (fun x hx k => H24_T0_ne hx k) (fun x hx y hy => H24_T0_mul hx hy) (fun x hx => H24_T0_inv hx)
      (fun x _ y _ => H11_Pmap_mul a x y) (fun x _ => H12_Pmap_inv x) hPne hsurj]
    apply Nat.card_congr
    exact
      { toFun := fun x => ⟨x.1, x.2, h6map x.1 x.2⟩
        invFun := fun x => ⟨x.1, x.2.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have eIm : Nat.card (H12_res '' (H24_K1 r : Set (ZMod n → L))) =
      Nat.card {x : ZMod n → L // x ∈ (topData0 n r : Set (ZMod n → L)) ∧
        Pmap n a x ∈ (fun g => tauG n a g / g) '' (Ggrp n a r : Set (ZMod n → L))} := by
    rw [eD]; rfl
  show Nat.card {lam : ZMod n → L // H24_K r lam} = 4 * pairProd n r
  rw [← hD0card, eA, eB, eC, eIm, eE, eF, ← eG]
  ring

#print axioms thm_6_4_step67_proved

end Xia.Proofs
