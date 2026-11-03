/- Xia/Proofs/Combinatorics.lean — proofs of the rows thm_5_1_a, thm_5_1_b, thm_4_1_pairs, thm_6_4_pairs, cor_6_3, thm_6_2_step1 of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry

namespace Xia.Proofs

open Xia Finset

set_option linter.unusedSectionVars false

/-! ## Part 0 — small facts about `ZMod n`, `n` even -/

section ZModFacts

variable {n : ℕ} [NeZero n]

lemma H6_pow_dvd {a nodd k : ℕ} (hn : n = 2 ^ a * nodd) (hk : k ≤ a) : 2 ^ k ∣ n := by
  rw [hn]; exact Dvd.dvd.mul_right (pow_dvd_pow 2 hk) _

lemma H6_odd_val_iff (h2 : 2 ∣ n) (x : ZMod n) : Odd x.val ↔ ZMod.castHom h2 (ZMod 2) x = 1 := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_one_iff_odd]

lemma H6_even_val_iff (h2 : 2 ∣ n) (x : ZMod n) : Even x.val ↔ ZMod.castHom h2 (ZMod 2) x = 0 := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff_even]

lemma H6_zmod2_ne_one : ∀ z : ZMod 2, z ≠ 1 → z = 0 := by decide

lemma H6_half_val (n : ℕ) [NeZero n] : (half n : ZMod n).val = n / 2 := by
  unfold half
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.div_lt_self (Nat.pos_of_ne_zero (NeZero.ne n)) one_lt_two)]

lemma H6_even_half (h4 : 4 ∣ n) : Even (n / 2) := by
  obtain ⟨c, hc⟩ := h4; exact ⟨c, by omega⟩

lemma H6_two_mul_half (h2 : 2 ∣ n) : (2 : ZMod n) * half n = 0 := by
  unfold half
  have h : ((2 * (n / 2) : ℕ) : ZMod n) = 0 := by
    rw [Nat.mul_div_cancel' h2]; exact ZMod.natCast_self n
  push_cast at h; exact h

lemma H6_half_add_half (h2 : 2 ∣ n) : half n + half n = (0 : ZMod n) := by
  rw [← two_mul]; exact H6_two_mul_half h2

lemma H6_mul_half_even (h2 : 2 ∣ n) {x : ZMod n} (hx : Even x.val) : x * half n = 0 := by
  obtain ⟨j, hj⟩ := hx
  rw [← ZMod.natCast_zmod_val x, hj]
  push_cast
  linear_combination (j : ZMod n) * H6_two_mul_half h2

lemma H6_mul_half_odd (h2 : 2 ∣ n) {x : ZMod n} (hx : Odd x.val) : x * half n = half n := by
  obtain ⟨j, hj⟩ := hx
  rw [← ZMod.natCast_zmod_val x, hj]
  push_cast
  linear_combination (j : ZMod n) * H6_two_mul_half h2

lemma H6_half_sq (h2 : 2 ∣ n) (h4 : 4 ∣ n) : half n * half n = (0 : ZMod n) :=
  H6_mul_half_even h2 (by rw [H6_half_val]; exact H6_even_half h4)

/-- `u := 1 + n/2` acts as the identity on even residues. -/
lemma H6_u_even (h2 : 2 ∣ n) {t : ZMod n} (ht : Even t.val) : (1 + half n) * t = t := by
  rw [add_mul, one_mul, mul_comm (half n) t, H6_mul_half_even h2 ht, add_zero]

/-- `u := 1 + n/2` adds `n/2` to odd residues. -/
lemma H6_u_odd (h2 : 2 ∣ n) {t : ZMod n} (ht : Odd t.val) : (1 + half n) * t = t + half n := by
  rw [add_mul, one_mul, mul_comm (half n) t, H6_mul_half_odd h2 ht]

/-- `u^2 = 1` (s5_twonorms.tex:112). -/
lemma H6_u_sq (h2 : 2 ∣ n) (h4 : 4 ∣ n) : (1 + half n) * (1 + half n) = (1 : ZMod n) := by
  linear_combination H6_half_sq h2 h4 + H6_two_mul_half h2

lemma H6_u_half (h2 : 2 ∣ n) (h4 : 4 ∣ n) : (1 + half n) * half n = (half n : ZMod n) := by
  linear_combination H6_half_sq h2 h4

lemma H6_u_two (h2 : 2 ∣ n) : (1 + half n) * ((((2 : ℕ) : ℤ)) : ZMod n) = (((2 : ℕ) : ℤ) : ZMod n) := by
  have h : (((2 : ℕ) : ℤ) : ZMod n) = 2 := by norm_num
  rw [h]; linear_combination H6_two_mul_half h2

lemma H6_u_two_sub (h2 : 2 ∣ n) (s t : ZMod n) : (1 + half n) * (2 * s - t) = 2 * s - (1 + half n) * t := by
  linear_combination s * H6_two_mul_half h2

/-- `{us, us + m} = {s, s + m}`. -/
lemma H6_pair (h2 : 2 ∣ n) (s : ZMod n) :
    ((1 + half n) * s + half n = s + half n ∧ (1 + half n) * s = s) ∨
      ((1 + half n) * s + half n = s ∧ (1 + half n) * s = s + half n) := by
  rcases Nat.even_or_odd s.val with he | ho
  · left; rw [H6_u_even h2 he]; exact ⟨rfl, rfl⟩
  · right; rw [H6_u_odd h2 ho, add_assoc, H6_half_add_half h2, add_zero]; exact ⟨rfl, rfl⟩

lemma H6_cast2_half (h2 : 2 ∣ n) (h4 : 4 ∣ n) : ZMod.castHom h2 (ZMod 2) (half n) = 0 := by
  unfold half; rw [map_natCast, ZMod.natCast_eq_zero_iff_even]; exact H6_even_half h4

lemma H6_sum_u {M : Type*} [AddCommMonoid M] (h2 : 2 ∣ n) (h4 : 4 ∣ n) (f : ZMod n → M) :
    ∑ t, f ((1 + half n) * t) = ∑ t, f t := by
  have hinv : Function.Involutive (fun t : ZMod n => (1 + half n) * t) := fun t => by
    show (1 + half n) * ((1 + half n) * t) = t
    rw [← mul_assoc, H6_u_sq h2 h4, one_mul]
  exact Fintype.sum_bijective _ hinv.bijective _ _ (fun _ => rfl)

lemma H6_pow_mod {M : Type*} [Monoid M] {ω : M} (hω : ω ^ n = 1) (a : ℕ) : ω ^ a = ω ^ (a % n) := by
  conv_lhs => rw [← Nat.div_add_mod a n, pow_add, pow_mul, hω, one_pow, one_mul]

lemma H6_pow_val {M : Type*} [Monoid M] {ω : M} (hω : ω ^ n = 1) (a b : ZMod n) :
    (ω ^ a.val) ^ b.val = ω ^ (a * b).val := by
  rw [← pow_mul, ZMod.val_mul, ← H6_pow_mod hω]

end ZModFacts

/-! ## Part 1 — Theorem 5.1(a): the substitution `y ↦ y^{(u)}` -/

section Subst

variable {n : ℕ} [NeZero n] {K : Type*} [CommRing K]

lemma H6_subst_subst (h2 : 2 ∣ n) (h4 : 4 ∣ n) (y : ZMod n → K) : ySubst (ySubst y) = y := by
  funext t
  show y ((1 + half n) * ((1 + half n) * t)) = y t
  rw [← mul_assoc, H6_u_sq h2 h4, one_mul]

lemma H6_sgn_eq {x z : ZMod n} (h : Even x.val ↔ Even z.val) : (sgn x : K) = sgn z := by
  unfold sgn
  rcases Nat.even_or_odd z.val with hz | hz
  · rw [(h.mpr hz).neg_one_pow, hz.neg_one_pow]
  · have hx : Odd x.val := Nat.not_even_iff_odd.mp (fun hx => (Nat.not_even_iff_odd.mpr hz) (h.mp hx))
    rw [hx.neg_one_pow, hz.neg_one_pow]

lemma H6_sgn_u (h2 : 2 ∣ n) (h4 : 4 ∣ n) (t : ZMod n) : (sgn ((1 + half n) * t) : K) = sgn t := by
  apply H6_sgn_eq
  rw [H6_even_val_iff h2, H6_even_val_iff h2, map_mul, map_add, map_one, H6_cast2_half h2 h4, add_zero,
    one_mul]

lemma H6_L1_iter {r : ℕ} {σ : ℤ} {y : ZMod n → K} (h : L1 r σ y) (j : ℕ) (s : ZMod n) :
    y (s + (j : ZMod n) * (σ : ZMod n)) = y s ^ (r ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hs := h (s + (j : ZMod n) * σ)
    rw [ih] at hs
    rw [show s + ((j + 1 : ℕ) : ZMod n) * (σ : ZMod n) = s + (j : ZMod n) * σ + σ by push_cast; ring, hs,
      ← pow_mul, pow_succ]

lemma H6_L1_subst {r : ℕ} {σ : ℤ} (hσ : (1 + half n) * (σ : ZMod n) = σ) {y : ZMod n → K} (h : L1 r σ y) :
    L1 r σ (ySubst y) := by
  intro s
  show y ((1 + half n) * (s + σ)) = y ((1 + half n) * s) ^ r
  rw [mul_add, hσ]
  exact h _

lemma H6_L2_subst (h2 : 2 ∣ n) (h4 : 4 ∣ n) {c : K} {y : ZMod n → K} (h : L2 c y) : L2 c (ySubst y) := by
  intro s hs
  show y ((1 + half n) * s) * y ((1 + half n) * (s + half n)) = c
  rw [mul_add, H6_u_half h2 h4]
  rcases H6_pair h2 s with ⟨e2, e1⟩ | ⟨e2, e1⟩
  · rw [e2, e1]; exact h s hs
  · rw [e2, e1, mul_comm]; exact h s hs

lemma H6_R_neg (y : ZMod n → K) (s : ZMod n) : R y (-s) = R y s := by
  unfold R
  exact (Fintype.sum_equiv (Equiv.addRight s) _ _ (fun t => by simp [mul_comm])).symm

lemma H6_L3_iff {c : K} {y : ZMod n → K} : L3 c y ↔ ∀ s : ZMod n, s.val < n / 2 → R y s = c := by
  have h : ∀ s, ∑ t, y t * y (s + t) = R y s := fun s => Finset.sum_congr rfl (fun t _ => by rw [add_comm])
  simp only [L3, h]

/-- (L3) and `R(-s) = R(s)` give `R(s) = c` for every `s ≠ m`. -/
lemma H6_R_of_L3 (h2 : 2 ∣ n) {c : K} {y : ZMod n → K} (hL3 : L3 c y) (s : ZMod n) (hs : s ≠ half n) :
    R y s = c := by
  rw [H6_L3_iff] at hL3
  by_cases hlt : s.val < n / 2
  · exact hL3 s hlt
  · rw [← H6_R_neg]
    apply hL3
    have hval := ZMod.val_lt s
    have hnpos := Nat.pos_of_ne_zero (NeZero.ne n)
    have hne : s.val ≠ n / 2 := fun h => hs (ZMod.val_injective n (by rw [h, H6_half_val]))
    have hs0 : s ≠ 0 := by intro h0; rw [h0, ZMod.val_zero] at hlt; omega
    simp only [ZMod.neg_val, hs0, ↓reduceIte]
    omega

lemma H6_R_subst (h2 : 2 ∣ n) (h4 : 4 ∣ n) (y : ZMod n → K) (s : ZMod n) :
    R (ySubst y) s = R y ((1 + half n) * s) := by
  calc R (ySubst y) s = ∑ t, y ((1 + half n) * t) * y ((1 + half n) * t + (1 + half n) * s) := by
        simp only [R, ySubst]
        exact Finset.sum_congr rfl (fun t _ => by rw [mul_add])
    _ = R y ((1 + half n) * s) := H6_sum_u h2 h4 (fun t => y t * y (t + (1 + half n) * s))

lemma H6_L3_subst (h2 : 2 ∣ n) (h4 : 4 ∣ n) {c : K} {y : ZMod n → K} (h : L3 c y) : L3 c (ySubst y) := by
  rw [H6_L3_iff]
  intro s hs
  rw [H6_R_subst h2 h4]
  apply H6_R_of_L3 h2 h
  intro hus
  have hs' : s = half n := by
    calc s = (1 + half n) * ((1 + half n) * s) := by rw [← mul_assoc, H6_u_sq h2 h4, one_mul]
      _ = half n := by rw [hus, H6_u_half h2 h4]
  rw [hs', H6_half_val] at hs
  exact lt_irrefl _ hs

lemma H6_S_subst (h2 : 2 ∣ n) (h4 : 4 ∣ n) (y : ZMod n → K) : S (ySubst y) = S y := by
  calc S (ySubst y) = ∑ t, (sgn ((1 + half n) * t) : K) * y ((1 + half n) * t) := by
        simp only [S, ySubst]
        exact Finset.sum_congr rfl (fun t _ => by rw [H6_sgn_u h2 h4])
    _ = S y := H6_sum_u h2 h4 (fun t => (sgn t : K) * y t)

lemma H6_L4_subst (h2 : 2 ∣ n) (h4 : 4 ∣ n) {y : ZMod n → K} (h : L4 y) : L4 (ySubst y) := by
  intro s hs
  rw [H6_S_subst h2 h4]
  have hlhs : ∑ t, (sgn t : K) * ySubst y t * ySubst y (2 * s - t) = ∑ t, (sgn t : K) * y t * y (2 * s - t) := by
    calc ∑ t, (sgn t : K) * ySubst y t * ySubst y (2 * s - t)
        = ∑ t, (sgn ((1 + half n) * t) : K) * y ((1 + half n) * t) * y (2 * s - (1 + half n) * t) := by
          simp only [ySubst]
          exact Finset.sum_congr rfl (fun t _ => by rw [H6_sgn_u h2 h4, H6_u_two_sub h2])
      _ = ∑ t, (sgn t : K) * y t * y (2 * s - t) := H6_sum_u h2 h4 (fun t => (sgn t : K) * y t * y (2 * s - t))
  rw [hlhs, h s hs]
  show (y s + y (s + half n)) * S y = (y ((1 + half n) * s) + y ((1 + half n) * (s + half n))) * S y
  rw [mul_add (1 + half n), H6_u_half h2 h4]
  rcases H6_pair h2 s with ⟨e2, e1⟩ | ⟨e2, e1⟩
  · rw [e2, e1]
  · rw [e2, e1, add_comm (y (s + half n))]

lemma H6_dft_subst {L : Type*} [CommRing L] (h2 : 2 ∣ n) (h4 : 4 ∣ n) {ω : L} (hω : ω ^ n = 1)
    (z : ZMod n → L) (k : ZMod n) :
    dft ω (fun t => z ((1 + half n) * t)) k = dft ω z ((1 + half n) * k) := by
  unfold dft
  calc ∑ t, z ((1 + half n) * t) * (ω ^ k.val) ^ t.val
      = ∑ t, z ((1 + half n) * t) * (ω ^ k.val) ^ ((1 + half n) * ((1 + half n) * t)).val := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [← mul_assoc, H6_u_sq h2 h4, one_mul]
    _ = ∑ t, z t * (ω ^ k.val) ^ ((1 + half n) * t).val :=
        H6_sum_u h2 h4 (fun t => z t * (ω ^ k.val) ^ ((1 + half n) * t).val)
    _ = ∑ t, z t * (ω ^ ((1 + half n) * k).val) ^ t.val := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [H6_pow_val hω, H6_pow_val hω, show k * ((1 + half n) * t) = (1 + half n) * k * t by ring]

lemma H6_dftA_subst {F L : Type*} [CommRing F] [CommRing L] [Algebra F L] (h2 : 2 ∣ n) (h4 : 4 ∣ n) {ω : L}
    (hω : ω ^ n = 1) (y : ZMod n → F) (k : ZMod n) :
    dftA ω (ySubst y) k = dftA ω y ((1 + half n) * k) :=
  H6_dft_subst h2 h4 hω (fun t => algebraMap F L (y t)) k

lemma H6_subst_one (h4 : 4 ∣ n) {y : ZMod n → K} (hL1 : L1 3 ((2 : ℕ) : ℤ) y) : ySubst y 1 = bar n (y 1) := by
  have hit := H6_L1_iter hL1 (n / 4) 1
  have hidx : (1 : ZMod n) + ((n / 4 : ℕ) : ZMod n) * ((((2 : ℕ) : ℤ)) : ZMod n) = (1 + half n) * 1 := by
    rw [mul_one]
    unfold half
    obtain ⟨c, hc⟩ := h4
    have h' : n / 2 = n / 4 * 2 := by omega
    rw [h']
    push_cast; ring
  show y ((1 + half n) * 1) = y 1 ^ (3 ^ (n / 4))
  rw [← hidx, hit]

end Subst

theorem thm_5_1_a_proved (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (_hodd : Odd nodd) (_h3 : ¬ 3 ∣ n)
    {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) :
    (∀ y : ZMod n → GaloisField 3 (n / 2), ySubst (ySubst y) = y) ∧
      (∀ y ∈ XiaSet n 2, ySubst y ∈ XiaSet n 2) ∧
      ∀ y ∈ NFSet n 2, ySubst y ∈ NFSet n 2 ∧ S (ySubst y) = S y ∧
        (∀ k : ZMod n, Even k.val → dftA ω (ySubst y) k = dftA ω y k) ∧
        (∀ k : ZMod n, Odd k.val → dftA ω (ySubst y) k = dftA ω y (k + half n)) ∧
        ySubst y 0 = y 0 ∧ ySubst y 1 = bar n (y 1) := by
  have h4 : 4 ∣ n := by simpa using H6_pow_dvd (k := 2) hn (by omega)
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hσ := H6_u_two (n := n) h2
  refine ⟨fun y => H6_subst_subst h2 h4 y, fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨hL1, hL2, hL3, hL4⟩ := hy
    exact ⟨H6_L1_subst hσ hL1, H6_L2_subst h2 h4 hL2, H6_L3_subst h2 h4 hL3, H6_L4_subst h2 h4 hL4⟩
  · obtain ⟨hL1, hL3, hR, hL4⟩ := hy
    refine ⟨⟨H6_L1_subst hσ hL1, H6_L3_subst h2 h4 hL3, ?_, H6_L4_subst h2 h4 hL4⟩, H6_S_subst h2 h4 y,
      fun k hk => ?_, fun k hk => ?_, ?_, H6_subst_one h4 hL1⟩
    · rw [H6_R_subst h2 h4, H6_u_half h2 h4]; exact hR
    · rw [H6_dftA_subst h2 h4 hω.pow_eq_one, H6_u_even h2 hk]
    · rw [H6_dftA_subst h2 h4 hω.pow_eq_one, H6_u_odd h2 hk]
    · show y ((1 + half n) * 0) = y 0
      rw [mul_zero]

/-! ## Part 2 — orbits of `k ↦ r k` on `ZMod n` -/

section Orbits

variable {n : ℕ} [NeZero n]

lemma H6_mem_orbit {r : ℕ} {k x : ZMod n} : x ∈ orbit r k ↔ ∃ i : ℕ, x = (r : ZMod n) ^ i * k := by
  simp [orbit]

lemma H6_self_mem (r : ℕ) (k : ZMod n) : k ∈ orbit r k := H6_mem_orbit.mpr ⟨0, by simp⟩

lemma H6_neg_mem {r : ℕ} {k z : ZMod n} (h : z ∈ orbit r k) : -z ∈ orbit r (-k) := by
  obtain ⟨i, rfl⟩ := H6_mem_orbit.mp h
  exact H6_mem_orbit.mpr ⟨i, by ring⟩

lemma H6_pow_period {r : ℕ} (hcop : Nat.Coprime r n) : ∃ m : ℕ, (r : ZMod n) ^ (m + 1) = 1 := by
  refine ⟨Nat.totient n - 1, ?_⟩
  have hpos : 0 < Nat.totient n := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  rw [Nat.sub_add_cancel hpos]
  have h := congrArg Units.val (ZMod.pow_totient (ZMod.unitOfCoprime r hcop))
  rwa [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] at h

lemma H6_orbit_eq {r : ℕ} (hcop : Nat.Coprime r n) {k x : ZMod n} (hx : x ∈ orbit r k) :
    orbit r x = orbit r k := by
  obtain ⟨m, hrm⟩ := H6_pow_period hcop
  obtain ⟨i, rfl⟩ := H6_mem_orbit.mp hx
  ext z
  simp only [H6_mem_orbit]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j + i, by rw [pow_add, mul_assoc]⟩
  · rintro ⟨j, rfl⟩
    refine ⟨j + m * i, ?_⟩
    rw [← mul_assoc, ← pow_add, show j + m * i + i = j + (m + 1) * i by ring, pow_add, pow_mul, hrm, one_pow,
      mul_one]

lemma H6_inv_orbit (r : ℕ) (k : ZMod n) : inv (orbit r k) = orbit r (-k) := by
  ext z
  simp only [inv, Finset.mem_image, H6_mem_orbit]
  constructor
  · rintro ⟨x, ⟨i, rfl⟩, rfl⟩; exact ⟨i, by ring⟩
  · rintro ⟨i, rfl⟩; exact ⟨(r : ZMod n) ^ i * k, ⟨i, rfl⟩, by ring⟩

lemma H6_card_inv (O : Finset (ZMod n)) : (inv O).card = O.card :=
  Finset.card_image_of_injective O neg_injective

lemma H6_odd_neg (h2 : 2 ∣ n) {k : ZMod n} (hk : Odd k.val) : Odd (-k).val := by
  rw [H6_odd_val_iff h2] at hk ⊢
  rw [map_neg, hk]; decide

lemma H6_odd_of_mem (h2 : 2 ∣ n) {r : ℕ} (hr : Odd r) {k z : ZMod n} (hk : Odd k.val) (h : z ∈ orbit r k) :
    Odd z.val := by
  obtain ⟨i, rfl⟩ := H6_mem_orbit.mp h
  rw [H6_odd_val_iff h2] at hk ⊢
  rw [map_mul, map_pow, map_natCast, hk, ZMod.natCast_eq_one_iff_odd.mpr hr, one_pow, one_mul]

lemma H6_card_topLayer (h2 : 2 ∣ n) : (topLayer n).card = n / 2 := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := (univ : Finset (ZMod n)))
    (fun k : ZMod n => Odd k.val)
  have hbij : (univ.filter (fun k : ZMod n => Odd k.val)).card =
      (univ.filter (fun k : ZMod n => ¬ Odd k.val)).card := by
    apply Finset.card_nbij' (· + 1) (· - 1)
    · intro x hx
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
      rw [H6_odd_val_iff h2] at hx ⊢
      rw [map_add, map_one, hx]; decide
    · intro x hx
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
      rw [H6_odd_val_iff h2] at hx ⊢
      rw [map_sub, map_one, H6_zmod2_ne_one _ hx]; decide
    · intro x _; simp
    · intro x _; simp
  rw [card_univ, ZMod.card] at hsplit
  unfold topLayer
  omega

/-- The pair `{O, O^{-1}}` of the orbit of `k`, written with `O^{-1} = orbit r (-k)`. -/
noncomputable def H6_pc (r : ℕ) (k : ZMod n) : Finset (Finset (ZMod n)) := {orbit r k, orbit r (-k)}

lemma H6_pc_union (r : ℕ) (k : ZMod n) : (H6_pc r k).biUnion id = orbit r k ∪ orbit r (-k) := by
  simp [H6_pc]

/-- Theorem 4.1 / 6.4 (pairs part) for any `r` prime to `n` with `-1 ∉ ⟨r⟩` on odd residues. -/
theorem H6_pairs_general {r : ℕ} (h4 : 4 ∣ n) (hcop : Nat.Coprime r n)
    (hneg : ∀ (i : ℕ) (k : ZMod n), Odd k.val → -k ≠ (r : ZMod n) ^ i * k) :
    (∀ O ∈ topOrbits n r, inv O ∈ topOrbits n r ∧ inv O ≠ O ∧ (inv O).card = O.card) ∧
      ∑ P ∈ topPairs n r, pairLen P = n / 4 := by
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hr : Odd r := Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right h2 hcop)
  have hne : ∀ k : ZMod n, Odd k.val → orbit r (-k) ≠ orbit r k := by
    intro k hk heq
    have hm : -k ∈ orbit r k := by rw [← heq]; exact H6_self_mem r (-k)
    obtain ⟨i, hi⟩ := H6_mem_orbit.mp hm
    exact hneg i k hk hi
  have hdisj1 : ∀ k : ZMod n, Odd k.val → Disjoint (orbit r k) (orbit r (-k)) := by
    intro k hk
    rw [Finset.disjoint_left]
    intro z hz hz'
    exact hne k hk ((H6_orbit_eq hcop hz').symm.trans (H6_orbit_eq hcop hz))
  constructor
  · intro O hO
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hO
    have hko : Odd k.val := (mem_filter.mp hk).2
    refine ⟨?_, ?_, H6_card_inv _⟩
    · rw [H6_inv_orbit]
      exact mem_image.mpr ⟨-k, mem_filter.mpr ⟨mem_univ _, H6_odd_neg h2 hko⟩, rfl⟩
    · rw [H6_inv_orbit]; exact hne k hko
  · have hpairs : topPairs n r = (topLayer n).image (H6_pc r) := by
      unfold topPairs topOrbits
      rw [Finset.image_image]
      refine Finset.image_congr (fun k _ => ?_)
      simp only [Function.comp, H6_pc, H6_inv_orbit]
    have hkey : ∀ k z : ZMod n, z ∈ (H6_pc r k).biUnion id → H6_pc r z = H6_pc r k := by
      intro k z hz
      rw [H6_pc_union] at hz
      rcases mem_union.mp hz with h | h
      · simp only [H6_pc]
        rw [H6_orbit_eq hcop h, H6_orbit_eq hcop (H6_neg_mem h)]
      · simp only [H6_pc]
        rw [H6_orbit_eq hcop h, H6_orbit_eq hcop (H6_neg_mem h), neg_neg, Finset.pair_comm]
    have hcardT : ∀ k : ZMod n, Odd k.val → ((H6_pc r k).biUnion id).card = 2 * pairLen (H6_pc r k) := by
      intro k hk
      have hc : ((H6_pc r k).biUnion id).card = 2 * (orbit r k).card := by
        rw [H6_pc_union, card_union_of_disjoint (hdisj1 k hk), ← H6_inv_orbit, H6_card_inv]
        ring
      unfold pairLen
      rw [hc]
      omega
    have hdisj : (↑(topPairs n r) : Set (Finset (Finset (ZMod n)))).PairwiseDisjoint (fun P => P.biUnion id) := by
      intro P hP P' hP' hPP'
      show Disjoint (P.biUnion id) (P'.biUnion id)
      rw [Finset.disjoint_left]
      intro z hz hz'
      rw [Finset.mem_coe, hpairs] at hP hP'
      obtain ⟨k, -, rfl⟩ := mem_image.mp hP
      obtain ⟨k', -, rfl⟩ := mem_image.mp hP'
      exact hPP' ((hkey k z hz).symm.trans (hkey k' z hz'))
    have hunion : (topPairs n r).biUnion (fun P => P.biUnion id) = topLayer n := by
      ext z
      rw [mem_biUnion]
      constructor
      · rintro ⟨P, hP, hz⟩
        rw [hpairs] at hP
        obtain ⟨k, hk, rfl⟩ := mem_image.mp hP
        rw [H6_pc_union] at hz
        have hko : Odd k.val := (mem_filter.mp hk).2
        refine mem_filter.mpr ⟨mem_univ _, ?_⟩
        rcases mem_union.mp hz with h | h
        · exact H6_odd_of_mem h2 hr hko h
        · exact H6_odd_of_mem h2 hr (H6_odd_neg h2 hko) h
      · intro hz
        refine ⟨H6_pc r z, ?_, ?_⟩
        · rw [hpairs]; exact mem_image_of_mem _ hz
        · rw [H6_pc_union]; exact mem_union_left _ (H6_self_mem r z)
    have hsum2 : ∑ P ∈ topPairs n r, (P.biUnion id).card = n / 2 := by
      rw [← card_biUnion hdisj, hunion, H6_card_topLayer h2]
    have hsum3 : ∑ P ∈ topPairs n r, (P.biUnion id).card = 2 * ∑ P ∈ topPairs n r, pairLen P := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun P hP => ?_)
      rw [hpairs] at hP
      obtain ⟨k, hk, rfl⟩ := mem_image.mp hP
      exact hcardT k (mem_filter.mp hk).2
    obtain ⟨c, hc⟩ := h4
    omega

end Orbits

/-! ## Part 3 — `-1 ∈ ⟨r⟩ (mod 2^a)` forces `r ≡ -1 (mod 2^a)` (s6_primes.tex:161-163) -/

lemma H6_zmod4_sq : ∀ x : ZMod 4, x ^ 2 ≠ -1 := by decide

lemma H6_mod_of_dvd_succ {M r : ℕ} (hM : 0 < M) (h : M ∣ r + 1) : r % M = M - 1 := by
  obtain ⟨c, hc⟩ := h
  rcases c with _ | d
  · simp at hc
  · have hr : r = (M - 1) + M * d := by
      rw [mul_add, mul_one] at hc
      generalize M * d = X at hc ⊢
      omega
    rw [hr, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

lemma H6_neg_one_pow {a r : ℕ} (ha : 2 ≤ a) (hr : Odd r) (i : ℕ) (h : (r : ZMod (2 ^ a)) ^ i = -1) :
    2 ^ a ∣ r + 1 := by
  have h4 : 4 ∣ 2 ^ a := by
    have := pow_dvd_pow 2 ha; simpa using this
  have hi : Odd i := by
    rcases Nat.even_or_odd i with ⟨j, rfl⟩ | hi
    · exfalso
      have h' := congrArg (ZMod.castHom h4 (ZMod 4)) h
      rw [map_pow, map_natCast, map_neg, map_one, ← two_mul, pow_mul'] at h'
      exact H6_zmod4_sq _ h'
    · exact hi
  have hdvd : ((2 ^ a : ℕ) : ℤ) ∣ (r : ℤ) ^ i + 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h]; ring
  have hfac : (r : ℤ) ^ i + 1 = ((r : ℤ) + 1) * ∑ j ∈ range i, (-(r : ℤ)) ^ j := by
    have e1 := geom_sum_mul (-(r : ℤ)) i
    have e2 := hi.neg_pow (r : ℤ)
    linear_combination e1 + e2
  have hG2 : ¬ (2 : ℤ) ∣ ∑ j ∈ range i, (-(r : ℤ)) ^ j := by
    intro h2G
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (∑ j ∈ range i, (-(r : ℤ)) ^ j) 2).mpr (by exact_mod_cast h2G)
    push_cast at h0
    rw [ZMod.natCast_eq_one_iff_odd.mpr hr, show (-1 : ZMod 2) = 1 from by decide] at h0
    simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at h0
    exact (Nat.not_even_iff_odd.mpr hi) (ZMod.natCast_eq_zero_iff_even.mp h0)
  have hcop : IsCoprime ((2 : ℤ) ^ a) (∑ j ∈ range i, (-(r : ℤ)) ^ j) :=
    (Int.prime_two.coprime_iff_not_dvd.mpr hG2).pow_left
  have h3 : (2 : ℤ) ^ a ∣ (r : ℤ) + 1 := hcop.dvd_of_dvd_mul_right (by rw [← hfac]; exact_mod_cast hdvd)
  exact_mod_cast h3

lemma H6_hneg {n a nodd r : ℕ} [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hr : Odd r)
    (hr1 : r % 2 ^ a ≠ 2 ^ a - 1) : ∀ (i : ℕ) (k : ZMod n), Odd k.val → -k ≠ (r : ZMod n) ^ i * k := by
  intro i k hk heq
  have hdvd : 2 ^ a ∣ n := H6_pow_dvd hn le_rfl
  have hu : IsUnit (ZMod.castHom hdvd (ZMod (2 ^ a)) k) := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hk)
  have h1 := congrArg (ZMod.castHom hdvd (ZMod (2 ^ a))) heq
  rw [map_neg, map_mul, map_pow, map_natCast, ← neg_one_mul] at h1
  have h2 : (r : ZMod (2 ^ a)) ^ i = -1 := (hu.mul_left_inj.mp h1).symm
  exact hr1 (H6_mod_of_dvd_succ (by positivity) (H6_neg_one_pow (by omega) hr i h2))

/-! ## Part 4 — Theorem 5.1(b), Theorem 4.1 (pairs), Theorem 6.4 (pairs) -/

lemma H6_three_pow_mod8 (i : ℕ) : ((3 : ℕ) : ZMod 8) ^ i = 1 ∨ ((3 : ℕ) : ZMod 8) ^ i = 3 := by
  induction i with
  | zero => left; simp
  | succ i ih =>
    rw [pow_succ]
    rcases ih with h | h <;> rw [h] <;> decide

lemma H6_zmod8_B : ∀ kk ee : ZMod 8, kk.val % 2 = 1 → (ee = 1 ∨ ee = 3) → -(ee * kk) ≠ kk + 0 := by decide

lemma H6_zmod8_A : ∀ kk ee : ZMod 8, kk.val % 2 = 1 → (ee = 1 ∨ ee = 3) → ee * kk ≠ kk + 4 := by decide

theorem thm_5_1_b_proved (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (_h3 : ¬ 3 ∣ n) :
    ∀ O ∈ topOrbits n 3, (4 ≤ a → ¬ IsCaseB O) ∧ (a = 3 → ¬ IsCaseA O) := by
  intro O hO
  obtain ⟨k, hk, rfl⟩ := mem_image.mp hO
  have hkodd : Odd k.val := (mem_filter.mp hk).2
  have h8 : 8 ∣ n := by simpa using H6_pow_dvd (k := 3) hn ha
  have hφk : (ZMod.castHom h8 (ZMod 8) k).val % 2 = 1 := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
    have := Nat.odd_iff.mp hkodd
    omega
  have hφh : ZMod.castHom h8 (ZMod 8) (half n) = (((n / 2) % 8 : ℕ) : ZMod 8) := by
    unfold half; rw [map_natCast, ZMod.natCast_mod]
  have hkmem : k ∈ orbit 3 k := H6_self_mem 3 k
  have hmem : k + half n ∈ negO (orbit 3 k) := mem_image.mpr ⟨k, hkmem, rfl⟩
  constructor
  · intro ha4 hB
    have h16 : 16 ∣ n := by simpa using H6_pow_dvd (k := 4) hn ha4
    have hB' : negO (orbit 3 k) = inv (orbit 3 k) := hB
    rw [hB'] at hmem
    obtain ⟨x, hx, hxk⟩ := mem_image.mp hmem
    obtain ⟨i, rfl⟩ := H6_mem_orbit.mp hx
    have hc := congrArg (ZMod.castHom h8 (ZMod 8)) hxk
    rw [map_neg, map_mul, map_pow, map_natCast, map_add, hφh, show n / 2 % 8 = 0 by omega] at hc
    exact H6_zmod8_B _ _ hφk (H6_three_pow_mod8 i) (by simpa using hc)
  · intro ha3 hA
    have hn8 : n = 8 * nodd := by rw [hn, ha3]; norm_num
    have hodd' := Nat.odd_iff.mp hodd
    have hA' : negO (orbit 3 k) = orbit 3 k := hA
    rw [hA'] at hmem
    obtain ⟨i, hi⟩ := H6_mem_orbit.mp hmem
    have hc := congrArg (ZMod.castHom h8 (ZMod 8)) hi
    rw [map_mul, map_pow, map_natCast, map_add, hφh, show n / 2 % 8 = 4 by omega] at hc
    exact H6_zmod8_A _ _ hφk (H6_three_pow_mod8 i) (by simpa using hc.symm)

theorem thm_4_1_pairs_proved (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (_hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n) :
    (∀ O ∈ topOrbits n 3, inv O ∈ topOrbits n 3 ∧ inv O ≠ O ∧ (inv O).card = O.card) ∧
      ∑ P ∈ topPairs n 3, pairLen P = n / 4 := by
  have h4 : 4 ∣ n := by simpa using H6_pow_dvd (k := 2) hn (by omega)
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have h8 : 8 ≤ 2 ^ a := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hr1 : 3 % 2 ^ a ≠ 2 ^ a - 1 := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  exact H6_pairs_general h4 hcop (H6_hneg hn ha ⟨1, rfl⟩ hr1)

theorem thm_6_4_pairs_proved (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a)
    (_hodd : Odd nodd) (hr : ¬ r ∣ pp n * n) (hr1 : r % 2 ^ a ≠ 2 ^ a - 1) :
    (∀ O ∈ topOrbits n r, inv O ∈ topOrbits n r ∧ inv O ≠ O ∧ (inv O).card = O.card) ∧
      ∑ P ∈ topPairs n r, pairLen P = n / 4 := by
  have h4 : 4 ∣ n := by simpa using H6_pow_dvd (k := 2) hn (by omega)
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hcop : Nat.Coprime r n :=
    (Nat.Prime.coprime_iff_not_dvd (Fact.out : r.Prime)).mpr (fun h => hr (Dvd.dvd.mul_left h _))
  have hrodd : Odd r := Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right h2 hcop)
  exact H6_pairs_general h4 hcop (H6_hneg hn ha hrodd hr1)

/-! ## Part 5 — Corollary 6.3 -/

section Cor63

variable {n : ℕ} [NeZero n] {K : Type*} [CommRing K]

lemma H6_L2_all (h2 : 2 ∣ n) {c : K} {y : ZMod n → K} (hL2 : L2 c y) (t : ZMod n) :
    y t * y (t + half n) = c := by
  by_cases ht : t.val < n / 2
  · exact hL2 t ht
  · have hs : (t + half n).val < n / 2 := by
      rw [ZMod.val_add, H6_half_val]
      have := ZMod.val_lt t
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    have h := hL2 (t + half n) hs
    rw [add_assoc, H6_half_add_half h2, add_zero, mul_comm] at h
    exact h

lemma H6_R_of_L2 (h2 : 2 ∣ n) {c : K} {y : ZMod n → K} (hL2 : L2 c y) : R y (half n) = (n : K) * c := by
  unfold R
  rw [Finset.sum_congr rfl (fun t _ => H6_L2_all h2 hL2 t), Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul]

end Cor63

lemma H6_natCast_pow_five {K : Type*} [CommRing K] [Algebra (ZMod 5) K] (m j : ℕ) : (m : K) ^ (5 ^ j) = m := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_mul, ih, ← map_natCast (algebraMap (ZMod 5) K) m, ← map_pow, ZMod.pow_card]

theorem cor_6_3_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (_heo : Odd e) (y : ZMod n → GaloisField 5 n) :
    y ∈ Xia5Set n ↔ y ∈ NF5Set n ∧ Nm5 n (y 0) = (n : GaloisField 5 n) ^ 3 := by
  have h2 : 2 ∣ n := by rw [hne]; exact dvd_pow_self 2 (by omega)
  have hpos : 0 < n / 2 := by
    have := Nat.pos_of_ne_zero (NeZero.ne n)
    omega
  have hNm : L1 5 1 y → Nm5 n (y 0) = y 0 * y (half n) := by
    intro hL1
    have hit := H6_L1_iter hL1 (n / 2) 0
    simp only [Int.cast_one, mul_one, zero_add] at hit
    unfold Nm5 half
    rw [pow_add, pow_one, hit]
  constructor
  · rintro ⟨hL1, hL2, hL3, hL4⟩
    refine ⟨⟨hL1, hL3, ?_, hL4⟩, ?_⟩
    · rw [H6_R_of_L2 h2 hL2]; ring
    · rw [hNm hL1]
      have h0 := hL2 0 (by rw [ZMod.val_zero]; exact hpos)
      rwa [zero_add] at h0
  · rintro ⟨⟨hL1, hL3, hR, hL4⟩, hN⟩
    refine ⟨hL1, ?_, hL3, hL4⟩
    intro s hs
    have hL1s := H6_L1_iter hL1 s.val 0
    have hL1h := H6_L1_iter hL1 s.val (half n)
    simp only [Int.cast_one, mul_one, zero_add, ZMod.natCast_zmod_val] at hL1s hL1h
    rw [add_comm s, hL1s, hL1h, ← mul_pow, ← hNm hL1, hN, ← pow_mul, mul_comm, pow_mul, H6_natCast_pow_five]

/-! ## Part 6 — Theorem 6.2, Step 1 -/

lemma H6_v2_five (k : ℕ) : padicValNat 2 (5 ^ (2 ^ k) - 1) = k + 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · norm_num
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  · have h := padicValNat.pow_two_sub_one (x := 5) (n := 2 ^ k) (by norm_num) (by norm_num)
      (by positivity) (Nat.even_pow.mpr ⟨even_two, hk.ne'⟩)
    rw [padicValNat.prime_pow] at h
    have h6 : padicValNat 2 (5 + 1) = 1 := by
      rw [show (5 + 1 : ℕ) = 2 * 3 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
        padicValNat_base (by norm_num), padicValNat.eq_zero_of_not_dvd (by norm_num)]
    have h4 : padicValNat 2 (5 - 1) = 2 := by
      rw [show (5 - 1 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
    omega

lemma H6_five_pow_eq_one_iff (n N : ℕ) : (5 : ZMod n) ^ N = 1 ↔ n ∣ 5 ^ N - 1 := by
  have h1 : 1 ≤ 5 ^ N := Nat.one_le_pow _ _ (by norm_num)
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1, sub_eq_zero]
  simp

theorem thm_6_2_step1_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (_heo : Odd e) :
    padicValNat 2 (5 ^ (n / 4) - 1) = e ∧ (∀ ξ : GaloisField 5 n, ξ ^ n = 1 → ξ ^ (5 ^ (n / 4)) = ξ) ∧
      orderOf (5 : ZMod n) = n / 4 ∧ (∀ k : ℕ, (-1 : ZMod n) ≠ (5 : ZMod n) ^ k) ∧
      (∀ x : ZMod n, IsUnit x → ∃ k : ℕ, x = (5 : ZMod n) ^ k ∨ x = -(5 : ZMod n) ^ k) ∧
      (∀ x : ZMod n, Odd x.val → orbit 5 x = orbit 5 1 ∨ orbit 5 x = inv (orbit 5 1)) ∧
      Disjoint (orbit 5 (1 : ZMod n)) (inv (orbit 5 1)) := by
  have hn4 : n / 4 = 2 ^ (e - 2) := by
    apply Nat.div_eq_of_eq_mul_left (by norm_num)
    rw [hne, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1; omega
  have hv : padicValNat 2 (5 ^ (n / 4) - 1) = e := by rw [hn4, H6_v2_five]; omega
  have hdvd : n ∣ 5 ^ (n / 4) - 1 := by
    have h := @pow_padicValNat_dvd 2 (5 ^ (n / 4) - 1)
    rwa [hv, ← hne] at h
  have hcop : Nat.Coprime 5 n := by rw [hne]; exact Nat.Coprime.pow_right e (by norm_num)
  have hord : orderOf (5 : ZMod n) = n / 4 := by
    rw [hn4, show e - 2 = (e - 3) + 1 by omega]
    apply orderOf_eq_prime_pow
    · rw [H6_five_pow_eq_one_iff, hne]
      intro hd
      have hv' := H6_v2_five (e - 3)
      have hX : 5 ^ 2 ^ (e - 3) - 1 ≠ 0 := by
        intro h0; rw [h0, padicValNat_zero_right] at hv'; omega
      have := (padicValNat_dvd_iff_le hX).mp hd
      omega
    · rw [H6_five_pow_eq_one_iff, show e - 3 + 1 = e - 2 by omega, ← hn4]
      exact hdvd
  have hneg1 : ∀ k : ℕ, (-1 : ZMod n) ≠ (5 : ZMod n) ^ k := by
    intro k hk
    subst hne
    have h8 : 8 ≤ 2 ^ e := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    have hd := H6_neg_one_pow (a := e) (r := 5) (by omega) ⟨2, by norm_num⟩ k (by exact_mod_cast hk.symm)
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have h5u : IsUnit (5 : ZMod n) := by
    have h := (ZMod.isUnit_iff_coprime 5 n).mpr hcop
    exact_mod_cast h
  have h5N : (5 : ZMod n) ^ (n / 4) = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have hunits : ∀ x : ZMod n, IsUnit x → ∃ k : ℕ, x = (5 : ZMod n) ^ k ∨ x = -(5 : ZMod n) ^ k := by
    intro x hx
    have hinj : Set.InjOn (fun k : ℕ => (5 : ZMod n) ^ k) ↑(range (n / 4)) := by
      rw [coe_range, ← hord]; exact pow_injOn_Iio_orderOf
    have hA : ((range (n / 4)).image (fun k : ℕ => (5 : ZMod n) ^ k)).card = n / 4 := by
      rw [card_image_of_injOn hinj, card_range]
    have hB : ((range (n / 4)).image (fun k : ℕ => -(5 : ZMod n) ^ k)).card = n / 4 := by
      rw [card_image_of_injOn (fun i hi j hj h => hinj hi hj (neg_injective h)), card_range]
    have hAB : Disjoint ((range (n / 4)).image (fun k : ℕ => (5 : ZMod n) ^ k))
        ((range (n / 4)).image (fun k : ℕ => -(5 : ZMod n) ^ k)) := by
      rw [disjoint_left]
      intro z hzA hzB
      obtain ⟨i, -, rfl⟩ := mem_image.mp hzA
      obtain ⟨j, hj, hij⟩ := mem_image.mp hzB
      rw [mem_range] at hj
      apply hneg1 (i + (n / 4 - j))
      calc (-1 : ZMod n) = -((5 : ZMod n) ^ j * 5 ^ (n / 4 - j)) := by
            rw [← pow_add, Nat.add_sub_cancel' hj.le, h5N]
        _ = (5 : ZMod n) ^ i * 5 ^ (n / 4 - j) := by rw [← hij]; ring
        _ = (5 : ZMod n) ^ (i + (n / 4 - j)) := by rw [pow_add]
    have hsub : (range (n / 4)).image (fun k : ℕ => (5 : ZMod n) ^ k) ∪
        (range (n / 4)).image (fun k : ℕ => -(5 : ZMod n) ^ k) ⊆ univ.image (Units.val : (ZMod n)ˣ → ZMod n) := by
      intro z hz
      have hzu : IsUnit z := by
        rcases mem_union.mp hz with h | h
        · obtain ⟨k, -, rfl⟩ := mem_image.mp h; exact h5u.pow k
        · obtain ⟨k, -, rfl⟩ := mem_image.mp h; exact (h5u.pow k).neg
      exact mem_image.mpr ⟨hzu.unit, mem_univ _, hzu.unit_spec⟩
    have hcard : (univ.image (Units.val : (ZMod n)ˣ → ZMod n)).card ≤
        ((range (n / 4)).image (fun k : ℕ => (5 : ZMod n) ^ k) ∪
          (range (n / 4)).image (fun k : ℕ => -(5 : ZMod n) ^ k)).card := by
      rw [card_image_of_injective _ Units.val_injective, card_univ, ZMod.card_units_eq_totient,
        card_union_of_disjoint hAB, hA, hB, hn4, hne, Nat.totient_prime_pow Nat.prime_two (by omega)]
      have h' : 2 ^ (e - 1) = 2 * 2 ^ (e - 2) := by
        rw [← pow_succ']; congr 1; omega
      omega
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    have hxm : x ∈ univ.image (Units.val : (ZMod n)ˣ → ZMod n) := mem_image.mpr ⟨hx.unit, mem_univ _, hx.unit_spec⟩
    rw [← heq] at hxm
    rcases mem_union.mp hxm with h | h
    · obtain ⟨k, -, rfl⟩ := mem_image.mp h; exact ⟨k, Or.inl rfl⟩
    · obtain ⟨k, -, rfl⟩ := mem_image.mp h; exact ⟨k, Or.inr rfl⟩
  have hcast5 : ((5 : ℕ) : ZMod n) = 5 := by norm_num
  refine ⟨hv, ?_, hord, hneg1, hunits, ?_, ?_⟩
  · intro ξ hξ
    have h1 : 1 ≤ 5 ^ (n / 4) := Nat.one_le_pow _ _ (by norm_num)
    obtain ⟨c, hc⟩ := hdvd
    rw [← Nat.sub_add_cancel h1, hc, pow_succ, pow_mul, hξ, one_pow, one_mul]
  · intro x hx
    have hxu : IsUnit x := by
      have h' : Nat.Coprime x.val (2 ^ e) := Nat.Coprime.pow_right e (Nat.coprime_two_right.mpr hx)
      rw [← hne] at h'
      rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime]
      exact h'
    obtain ⟨k, hk | hk⟩ := hunits x hxu
    · left
      apply H6_orbit_eq hcop
      exact H6_mem_orbit.mpr ⟨k, by rw [hk, hcast5, mul_one]⟩
    · right
      rw [H6_inv_orbit]
      apply H6_orbit_eq hcop
      exact H6_mem_orbit.mpr ⟨k, by rw [hk, hcast5]; ring⟩
  · rw [H6_inv_orbit, Finset.disjoint_left]
    intro z hz hz'
    have heq : orbit 5 (-1 : ZMod n) = orbit 5 1 := (H6_orbit_eq hcop hz').symm.trans (H6_orbit_eq hcop hz)
    have hm : (-1 : ZMod n) ∈ orbit 5 1 := by rw [← heq]; exact H6_self_mem 5 (-1)
    obtain ⟨i, hi⟩ := H6_mem_orbit.mp hm
    rw [hcast5, mul_one] at hi
    exact hneg1 i hi

#print axioms thm_5_1_a_proved
#print axioms thm_5_1_b_proved
#print axioms thm_4_1_pairs_proved
#print axioms thm_6_4_pairs_proved
#print axioms cor_6_3_proved
#print axioms thm_6_2_step1_proved

end Xia.Proofs
