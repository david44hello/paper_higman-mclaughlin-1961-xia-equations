/- Xia/Proofs/Sec5.lean — proofs of the rows sec_5_setup, thm_5_1_c_yform, thm_5_1_d_yform, fig1_caption, cor_5_2, thm_B_part and 1 more of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry
import Xia.Proofs.Combinatorics
import Xia.Proofs.Coverage
import Xia.Proofs.Thm31
import Xia.Proofs.Sec22
import Xia.Proofs.Signs
import Xia.Proofs.Pow2Arith
import Xia.Defs.Layer0

namespace Xia.Proofs

open Xia Finset

set_option linter.unusedSectionVars false

/-! ## Part A — parity and `n = 2^a n_odd` arithmetic -/

section Parity

variable {n : ℕ} [NeZero n]

theorem H19_four_dvd {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) : 4 ∣ n := by
  simpa using H6_pow_dvd (k := 2) hn (by omega)

theorem H19_eight_dvd {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) : 8 ∣ n := by
  simpa using H6_pow_dvd (k := 3) hn ha

theorem H19_odd_add_half (h2 : 2 ∣ n) (h4 : 4 ∣ n) {k : ZMod n} (hk : Odd k.val) : Odd (k + half n).val := by
  rw [H6_odd_val_iff h2] at hk ⊢
  rw [map_add, hk, H6_cast2_half h2 h4, add_zero]

theorem H19_even_add_half (h2 : 2 ∣ n) (h4 : 4 ∣ n) {k : ZMod n} (hk : Even k.val) : Even (k + half n).val := by
  rw [H6_even_val_iff h2] at hk ⊢
  rw [map_add, hk, H6_cast2_half h2 h4, add_zero]

theorem H19_even_half (h4 : 4 ∣ n) : Even (half n).val := by
  rw [H6_half_val]; exact H6_even_half h4

theorem H19_even_two_mul (h2 : 2 ∣ n) (k : ZMod n) : Even (2 * k).val := by
  rw [H6_even_val_iff h2, map_mul, map_ofNat]
  exact zero_mul _

theorem H19_odd_three_mul (h2 : 2 ∣ n) {k : ZMod n} (hk : Odd k.val) : Odd (((3 : ℕ) : ZMod n) * k).val := by
  rw [H6_odd_val_iff h2] at hk ⊢
  rw [map_mul, map_natCast, hk, mul_one]
  decide

theorem H19_even_three_mul (h2 : 2 ∣ n) {k : ZMod n} (hk : Even k.val) : Even (((3 : ℕ) : ZMod n) * k).val := by
  rw [H6_even_val_iff h2] at hk ⊢
  rw [map_mul, hk, mul_zero]

theorem H19_even_neg (h2 : 2 ∣ n) {k : ZMod n} (hk : Even k.val) : Even (-k).val := by
  rw [H6_even_val_iff h2] at hk ⊢
  rw [map_neg, hk, neg_zero]

theorem H19_pow_mul_half (hev : Even n) (j : ℕ) : (3 : ZMod n) ^ j * half n = half n := by
  have h := H7_odd_mul_half hev (3 ^ j) (Odd.pow (by decide))
  push_cast at h
  exact h

theorem H19_half_ne_zero (hn2 : 2 ≤ n) : half n ≠ (0 : ZMod n) := by
  intro h0
  have hv := congrArg ZMod.val h0
  rw [H6_half_val, ZMod.val_zero] at hv
  omega

theorem H19_half_val_eq {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) : n / 2 = 2 ^ (a - 1) * nodd := by
  have h : n = 2 * (2 ^ (a - 1) * nodd) := by
    rw [hn, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel ha]
  rw [h, Nat.mul_div_cancel_left _ (by norm_num)]

end Parity

/-! ## Part B — periods of `x ↦ 3x` on `ZMod n` and the orbit lengths -/

section Period

variable {n : ℕ} [NeZero n]

theorem H19_iter (k : ZMod n) (i : ℕ) : (fun x : ZMod n => 3 * x)^[i] k = 3 ^ i * k :=
  mul_left_iterate_apply 3 k

/-- The period of `k` under `x ↦ 3x`. -/
noncomputable def H19_per (k : ZMod n) : ℕ := Function.minimalPeriod (fun x : ZMod n => 3 * x) k

theorem H19_mem_orbit3 {k x : ZMod n} : x ∈ orbit 3 k ↔ ∃ i : ℕ, x = (3 : ZMod n) ^ i * k := by
  rw [H6_mem_orbit]; simp only [Nat.cast_ofNat]

theorem H19_mem_periodic (h3 : Nat.Coprime 3 n) (k : ZMod n) :
    k ∈ Function.periodicPts (fun x : ZMod n => 3 * x) := by
  obtain ⟨m, hm⟩ := H6_pow_period (n := n) h3
  refine Function.mk_mem_periodicPts (Nat.succ_pos m) ?_
  show (fun x : ZMod n => 3 * x)^[m + 1] k = k
  rw [H19_iter]
  simp only [Nat.cast_ofNat] at hm
  rw [hm, one_mul]

theorem H19_per_pos (h3 : Nat.Coprime 3 n) (k : ZMod n) : 0 < H19_per k :=
  Function.minimalPeriod_pos_of_mem_periodicPts (H19_mem_periodic h3 k)

theorem H19_pow_eq_self_iff (k : ZMod n) (j : ℕ) : (3 : ZMod n) ^ j * k = k ↔ H19_per k ∣ j := by
  rw [H19_per, ← Function.isPeriodicPt_iff_minimalPeriod_dvd]
  show _ ↔ (fun x : ZMod n => 3 * x)^[j] k = k
  rw [H19_iter]

theorem H19_pow_mod (k : ZMod n) (j : ℕ) : (3 : ZMod n) ^ (j % H19_per k) * k = 3 ^ j * k := by
  rw [← H19_iter, ← H19_iter]
  exact Function.iterate_mod_minimalPeriod_eq

theorem H19_orbit_eq_image (h3 : Nat.Coprime 3 n) (k : ZMod n) :
    orbit 3 k = (range (H19_per k)).image (fun i => (3 : ZMod n) ^ i * k) := by
  ext x
  rw [H19_mem_orbit3, mem_image]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i % H19_per k, mem_range.mpr (Nat.mod_lt _ (H19_per_pos h3 k)), H19_pow_mod k i⟩
  · rintro ⟨i, -, rfl⟩
    exact ⟨i, rfl⟩

theorem H19_orbit_card (h3 : Nat.Coprime 3 n) (k : ZMod n) : (orbit 3 k).card = H19_per k := by
  rw [H19_orbit_eq_image h3, card_image_of_injOn, card_range]
  intro i hi j hj hij
  rw [coe_range] at hi hj
  have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := fun x : ZMod n => 3 * x) (x := k)
  apply hinj hi hj
  show (fun x : ZMod n => 3 * x)^[i] k = (fun x : ZMod n => 3 * x)^[j] k
  rw [H19_iter, H19_iter]
  exact hij

/-- For `ρ` in an orbit `O`, `3^j ρ = ρ` iff `|O|` divides `j`. -/
theorem H19_pow_eq_self_iff' (h3 : Nat.Coprime 3 n) {k ρ : ZMod n} (hρ : ρ ∈ orbit 3 k) (j : ℕ) :
    (3 : ZMod n) ^ j * ρ = ρ ↔ (orbit 3 k).card ∣ j := by
  rw [← H6_orbit_eq h3 hρ, H19_orbit_card h3, H19_pow_eq_self_iff]

theorem H19_eq_of_dvd_lt {N g : ℕ} (hg0 : g ≠ 0) (hgN : g < N) (hdvd : N ∣ 2 * g) : 2 * g = N := by
  obtain ⟨c, hc⟩ := hdvd
  rcases c with _ | _ | c
  · omega
  · omega
  · nlinarith

/-- Case A: `-ρ = ρ^{q_O}` (exponent model: `ρ + n/2 = 3^{L/2} ρ`). -/
theorem H19_caseA_pow (h3 : Nat.Coprime 3 n) (hev : Even n) (hn2 : 2 ≤ n) {ρ : ZMod n}
    (hA : ρ + half n ∈ orbit 3 ρ) : ρ + half n = (3 : ZMod n) ^ ((orbit 3 ρ).card / 2) * ρ := by
  obtain ⟨i, hi⟩ := H19_mem_orbit3.mp hA
  have hN : (orbit 3 ρ).card = H19_per ρ := H19_orbit_card h3 ρ
  have hNpos : 0 < (orbit 3 ρ).card := hN ▸ H19_per_pos h3 ρ
  have hg : (3 : ZMod n) ^ (i % (orbit 3 ρ).card) * ρ = ρ + half n := by rw [hN, H19_pow_mod, ← hi]
  have hgN : i % (orbit 3 ρ).card < (orbit 3 ρ).card := Nat.mod_lt _ hNpos
  have h2g : (3 : ZMod n) ^ (2 * (i % (orbit 3 ρ).card)) * ρ = ρ := by
    rw [two_mul, pow_add, mul_assoc, hg, mul_add, hg, H19_pow_mul_half hev, add_assoc, H7_two_half hev, add_zero]
  have hdvd : (orbit 3 ρ).card ∣ 2 * (i % (orbit 3 ρ).card) :=
    (H19_pow_eq_self_iff' h3 (H6_self_mem 3 ρ) _).mp h2g
  have hg0 : i % (orbit 3 ρ).card ≠ 0 := by
    intro h0
    rw [h0, pow_zero, one_mul] at hg
    exact H19_half_ne_zero hn2 (by linear_combination -hg)
  have h2 := H19_eq_of_dvd_lt hg0 hgN hdvd
  rw [show (orbit 3 ρ).card / 2 = i % (orbit 3 ρ).card by omega, hg]

/-- Case B: `-ρ = ρ^{-q_O}` (exponent model: `ρ + n/2 = -(3^{L/2} ρ)`). -/
theorem H19_caseB_pow (h3 : Nat.Coprime 3 n) (h8 : 8 ∣ n) {ρ : ZMod n} (hρ : Odd ρ.val)
    (hB : -(ρ + half n) ∈ orbit 3 ρ) : ρ + half n = -((3 : ZMod n) ^ ((orbit 3 ρ).card / 2) * ρ) := by
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h8)
  obtain ⟨i, hi⟩ := H19_mem_orbit3.mp hB
  have hN : (orbit 3 ρ).card = H19_per ρ := H19_orbit_card h3 ρ
  have hNpos : 0 < (orbit 3 ρ).card := hN ▸ H19_per_pos h3 ρ
  have hg : (3 : ZMod n) ^ (i % (orbit 3 ρ).card) * ρ = -(ρ + half n) := by rw [hN, H19_pow_mod, ← hi]
  have hgN : i % (orbit 3 ρ).card < (orbit 3 ρ).card := Nat.mod_lt _ hNpos
  have h2g : (3 : ZMod n) ^ (2 * (i % (orbit 3 ρ).card)) * ρ = ρ := by
    rw [two_mul, pow_add, mul_assoc, hg, mul_neg, mul_add, hg, H19_pow_mul_half hev]
    ring
  have hdvd : (orbit 3 ρ).card ∣ 2 * (i % (orbit 3 ρ).card) :=
    (H19_pow_eq_self_iff' h3 (H6_self_mem 3 ρ) _).mp h2g
  have hg0 : i % (orbit 3 ρ).card ≠ 0 := by
    intro h0
    rw [h0, pow_zero, one_mul] at hg
    have hsum : ((ρ.val + ρ.val + n / 2 : ℕ) : ZMod n) = 0 := by
      rw [Nat.cast_add, Nat.cast_add, ZMod.natCast_zmod_val]
      show ρ + ρ + half n = 0
      linear_combination hg
    have hdvd' := (ZMod.natCast_eq_zero_iff _ _).mp hsum
    have h8' := dvd_trans h8 hdvd'
    rw [Nat.odd_iff] at hρ
    omega
  have h2 := H19_eq_of_dvd_lt hg0 hgN hdvd
  rw [show (orbit 3 ρ).card / 2 = i % (orbit 3 ρ).card by omega, hg, neg_neg]

theorem H19_negO_orbit (hev : Even n) (k : ZMod n) : negO (orbit 3 k) = orbit 3 (k + half n) := by
  ext x
  simp only [negO, mem_image, H19_mem_orbit3]
  constructor
  · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, by rw [mul_add, H19_pow_mul_half hev]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨3 ^ i * k, ⟨i, rfl⟩, by rw [mul_add, H19_pow_mul_half hev]⟩

theorem H19_negO_inv (hev : Even n) (O : Finset (ZMod n)) : negO (inv O) = inv (negO O) := by
  ext x
  simp only [negO, inv, mem_image]
  constructor
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w + half n, ⟨w, hw, rfl⟩, (H7_neg_add_half hev w).symm⟩
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨-w, ⟨w, hw, rfl⟩, H7_neg_add_half hev w⟩

theorem H19_negO_negO (hev : Even n) (O : Finset (ZMod n)) : negO (negO O) = O := by
  ext x
  simp only [negO, mem_image]
  constructor
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    rw [add_assoc, H7_two_half hev, add_zero]; exact hw
  · intro hx
    exact ⟨x + half n, ⟨x, hx, rfl⟩, by rw [add_assoc, H7_two_half hev, add_zero]⟩

end Period

/-! ## Part C — roots in an algebraically closed field of characteristic 3, and `V` -/

section Roots

theorem H19_card_lin {L : Type*} [Field L] [CharP L 3] [IsAlgClosed L] (N : ℕ) (hN : 1 ≤ N) (c : L)
    (hc : c ≠ 0) : Nat.card {t : L // t ^ (3 ^ N) = c * t} = 3 ^ N := by
  classical
  set p : Polynomial L := Polynomial.X ^ (3 ^ N) - Polynomial.C c * Polynomial.X with hp
  have h3N : 1 < 3 ^ N := Nat.one_lt_pow (by omega) (by norm_num)
  have hlin : (Polynomial.C c * Polynomial.X).natDegree = 1 := Polynomial.natDegree_C_mul_X c hc
  have hdeg : p.natDegree = 3 ^ N := by
    rw [hp, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> rw [Polynomial.natDegree_X_pow]
    rw [hlin]; exact h3N
  have hp0 : p ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at hdeg; omega
  have hcast : ((3 ^ N : ℕ) : L) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero L 3, zero_pow (by omega)]
  have hder : Polynomial.derivative p = -Polynomial.C c := by
    rw [hp, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C_mul_X, hcast,
      Polynomial.C_0, zero_mul, zero_sub]
  have hsep : p.Separable := by
    rw [Polynomial.separable_def, hder]
    refine ⟨0, Polynomial.C (-c⁻¹), ?_⟩
    rw [zero_mul, zero_add, mul_neg, ← Polynomial.C_mul, neg_mul, inv_mul_cancel₀ hc, Polynomial.C_neg,
      neg_neg, Polynomial.C_1]
  have hsplit : (p.map (algebraMap L L)).Splits := by
    rw [Algebra.algebraMap_self, Polynomial.map_id]; exact IsAlgClosed.splits p
  have hcard := Polynomial.card_rootSet_eq_natDegree hsep hsplit
  rw [hdeg] at hcard
  have hset : Nat.card {t : L // t ^ (3 ^ N) = c * t} = Nat.card (p.rootSet L) := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight (fun t => ?_)
    rw [Polynomial.mem_rootSet_of_ne hp0, hp]
    simp only [map_sub, map_pow, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_self,
      RingHom.id_apply]
    exact sub_eq_zero.symm
  rw [hset, Nat.card_eq_fintype_card, hcard]

theorem H19_V_eq (n : ℕ) [NeZero n] (h4 : 4 ∣ n) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] :
    {t : L | t ^ (3 ^ (n / 4)) = -t} = algebraMap (GaloisField 3 (n / 2)) L '' (Vsp n) := by
  classical
  let : Fintype (GaloisField 3 (n / 2)) := Fintype.ofFinite _
  have hpos := NeZero.pos n
  have h4' : 4 ≤ n := Nat.le_of_dvd hpos h4
  have hn2 : n / 2 ≠ 0 := by omega
  have hcardF : Fintype.card (GaloisField 3 (n / 2)) = 3 ^ (n / 2) := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 3 (n / 2) hn2]
  have h1q : 1 < Fintype.card (GaloisField 3 (n / 2)) := by
    rw [hcardF]; exact Nat.one_lt_pow hn2 (by norm_num)
  have hinj := (algebraMap (GaloisField 3 (n / 2)) L).injective
  ext t
  constructor
  · intro ht
    simp only [Set.mem_ofPred_eq] at ht
    have hq : t ^ (Fintype.card (GaloisField 3 (n / 2))) = t := by
      rw [hcardF, show n / 2 = n / 4 + n / 4 by omega, pow_add, pow_mul, ht,
        Odd.neg_pow (Odd.pow (by decide)), ht, neg_neg]
    set P : Polynomial L := Polynomial.X ^ (Fintype.card (GaloisField 3 (n / 2))) - Polynomial.X with hP
    have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero L h1q
    have hdegP : P.natDegree = Fintype.card (GaloisField 3 (n / 2)) :=
      FiniteField.X_pow_card_sub_X_natDegree_eq L h1q
    have hroot : ∀ s : L, s ^ (Fintype.card (GaloisField 3 (n / 2))) = s → s ∈ P.roots.toFinset := by
      intro s hs
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def, hP]
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hs, sub_self]
    by_contra hnot
    set A : Finset L := univ.image (algebraMap (GaloisField 3 (n / 2)) L) with hA
    have hAcard : A.card = Fintype.card (GaloisField 3 (n / 2)) := by
      rw [hA, card_image_of_injective _ hinj, card_univ]
    have htA : t ∉ A := by
      intro htA
      obtain ⟨x, -, rfl⟩ := mem_image.mp htA
      apply hnot
      refine ⟨x, ?_, rfl⟩
      show x ^ QQ n = -x
      apply hinj
      rw [map_pow, map_neg]
      exact ht
    have hsub : insert t A ⊆ P.roots.toFinset := by
      intro s hs
      rcases mem_insert.mp hs with rfl | hs
      · exact hroot s hq
      · obtain ⟨x, -, rfl⟩ := mem_image.mp hs
        apply hroot
        rw [← map_pow, FiniteField.pow_card]
    have h1 := card_le_card hsub
    rw [card_insert_of_notMem htA, hAcard] at h1
    have h2 := (Multiset.toFinset_card_le P.roots).trans (Polynomial.card_roots' P)
    omega
  · rintro ⟨x, hx, rfl⟩
    simp only [Set.mem_ofPred_eq]
    have hx' : x ^ QQ n = -x := hx
    unfold QQ at hx'
    rw [← map_pow, hx', map_neg]

end Roots

/-! ## Part D — Fourier helpers on `NF(n)` -/

section FourierHelpers

variable {n : ℕ} [NeZero n]

theorem H19_dftA_half (hev : Even n) (hn2 : 2 ≤ n) {F L : Type*} [Field F] [Field L] [Algebra F L] {ω : L}
    (hω : IsPrimitiveRoot ω n) (y : ZMod n → F) : dftA ω y (half n) = algebraMap F L (S y) := by
  unfold dftA
  rw [H4_S_eq_dft hev hn2 hω]
  unfold S sgn
  rw [map_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [map_mul, map_pow, map_neg, map_one]

/-- `(ω^k)^{n/2} = -1` for odd `k`, `= 1` for even `k`. -/
theorem H19_pow_half_odd {L : Type*} [Field L] (hev : Even n) {ω : L} (hω : IsPrimitiveRoot ω n) {k : ZMod n}
    (hk : Odd k.val) : (ω ^ k.val) ^ (n / 2) = -1 := by
  rw [← pow_mul, mul_comm, pow_mul, H7_pow_half_eq_neg_one hev hω, hk.neg_one_pow]

theorem H19_pow_half_even {L : Type*} [Field L] (hev : Even n) {ω : L} (hω : IsPrimitiveRoot ω n) {k : ZMod n}
    (hk : Even k.val) : (ω ^ k.val) ^ (n / 2) = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, H7_pow_half_eq_neg_one hev hω, hk.neg_one_pow]

end FourierHelpers

/-! ## Row 18d — Section 5 set-up -/

theorem sec_5_setup_of (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (_hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type*} [Field L] [CharP L 3] [IsAlgClosed L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L)
    (hω : IsPrimitiveRoot ω n)
    (hP24 : Set.BijOn (dftA ω) (NFSet n 2) {h | F1 3 2 ω h ∧ F3 ω h ∧ F4 h}) :
    (∀ O ∈ topOrbits n 3, ∀ ρ ∈ O,
      Nat.card {t : L // t ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * t} = 3 ^ O.card ∧
      (∀ t t' : L, t ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * t →
        t' ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * t' →
        (t + t') ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * (t + t')) ∧
      (∀ y ∈ NFSet n 2, (∀ k : ℕ,
          dftA ω y ((3 : ZMod n) ^ k * ρ) = (ω ^ ρ.val) ^ (2 * k * 3 ^ k) * dftA ω y ρ ^ (3 ^ k)) ∧
        dftA ω y ρ ≠ 0 ∧ dftA ω y ρ ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * dftA ω y ρ) ∧
      negO O ∈ topOrbits n 3 ∧ ρ + half n = (1 + half n) * ρ ∧
      (IsCaseA O → ρ + half n = (3 : ZMod n) ^ (O.card / 2) * ρ) ∧
      (IsCaseB O → ρ + half n = -((3 : ZMod n) ^ (O.card / 2) * ρ))) ∧
    (∀ y ∈ NFSet n 2, ∀ k : ZMod n, Odd k.val → dftA ω y (-k) = -1 / dftA ω y k) ∧
    ∀ e : ℕ, n = 2 ^ e → 4 ≤ e → (blocks n).card = 1 ∧ (blocksA n).card = 1 ∧ (∀ B ∈ blocks n, qO B = qq n) ∧
      (ω ^ (1 : ZMod n).val)⁻¹ ^ (2 * (n / 4)) = -1 ∧ ω ^ ((n / 4) * qq n) = ω ^ (n / 4) ∧
      {t : L | t ^ (3 ^ (n / 4)) = -t} = algebraMap (GaloisField 3 (n / 2)) L '' (Vsp n) := by
  have h4 := H19_four_dvd hn ha
  have h8 := H19_eight_dvd hn ha
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hev : Even n := even_iff_two_dvd.mpr h2
  have hn8 : 8 ≤ n := Nat.le_of_dvd (NeZero.pos n) h8
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have hω1 : ω ^ n = 1 := hω.pow_eq_one
  have hω0 : ω ≠ 0 := hω.ne_zero (NeZero.ne n)
  refine ⟨?_, ?_, ?_⟩
  · intro O hO ρ hρ
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hO
    have hko : Odd k.val := (mem_filter.mp hk).2
    have hρo : Odd ρ.val := H7_orbit_odd h2 k hko ρ hρ
    have horb : orbit 3 ρ = orbit 3 k := H6_orbit_eq hcop hρ
    have hNpos : 1 ≤ (orbit 3 k).card := card_pos.mpr ⟨k, H6_self_mem 3 k⟩
    have hwrap : (3 : ZMod n) ^ (orbit 3 k).card * ρ = ρ :=
      (H19_pow_eq_self_iff' hcop hρ _).mpr (dvd_refl _)
    have hc0 : (ω ^ ρ.val)⁻¹ ^ (2 * (orbit 3 k).card) ≠ 0 :=
      pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ hω0))
    have hρpow : (ω ^ ρ.val) ^ (3 ^ (orbit 3 k).card) = ω ^ ρ.val := by
      rw [H4_pow_val_mul_nat hω1 ρ (3 ^ (orbit 3 k).card)]
      congr 2
      push_cast
      rw [mul_comm, hwrap]
    refine ⟨H19_card_lin _ hNpos _ hc0, fun t t' ht ht' => ?_, fun y hy => ?_, ?_, (H6_u_odd h2 hρo).symm,
      fun hA => ?_, fun hB => ?_⟩
    · rw [add_pow_char_pow, ht, ht', mul_add]
    · obtain ⟨hF1, hF3, -⟩ := hP24.mapsTo hy
      have hit := H4_F1_iter hω1 ((H4_F1_iff ω _).mp hF1)
      refine ⟨fun j => hit j ρ, H5_F3_ne hω0 _ hF3 ρ, ?_⟩
      have e := hit (orbit 3 k).card ρ
      rw [hwrap] at e
      have hX : (ω ^ ρ.val) ^ (2 * (orbit 3 k).card * 3 ^ (orbit 3 k).card) =
          (ω ^ ρ.val) ^ (2 * (orbit 3 k).card) := by
        rw [mul_comm (2 * (orbit 3 k).card), pow_mul, hρpow]
      rw [hX] at e
      have hX0 : (ω ^ ρ.val) ^ (2 * (orbit 3 k).card) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hω0)
      rw [inv_pow]
      conv_rhs => rw [e]
      rw [← mul_assoc, inv_mul_cancel₀ hX0, one_mul]
    · rw [H19_negO_orbit hev]
      exact mem_image.mpr ⟨k + half n, mem_filter.mpr ⟨mem_univ _, H19_odd_add_half h2 h4 hko⟩, rfl⟩
    · have hmem : ρ + half n ∈ orbit 3 ρ := by
        rw [horb, ← (show negO (orbit 3 k) = orbit 3 k from hA)]
        exact mem_image_of_mem _ hρ
      rw [H19_caseA_pow hcop hev (by omega) hmem, horb]
    · have hmem : -(ρ + half n) ∈ orbit 3 ρ := by
        have h1 : ρ + half n ∈ inv (orbit 3 k) := by
          rw [← (show negO (orbit 3 k) = inv (orbit 3 k) from hB)]
          exact mem_image_of_mem _ hρ
        obtain ⟨z, hz, hzr⟩ := mem_image.mp h1
        rw [horb, ← hzr, neg_neg]
        exact hz
      rw [H19_caseB_pow hcop h8 hρo hmem, horb]
  · intro y hy k hk
    obtain ⟨-, hF3, -⟩ := hP24.mapsTo hy
    have e := hF3 k
    rw [H19_pow_half_odd hev hω hk] at e
    rw [eq_div_iff (H5_F3_ne hω0 _ hF3 k), mul_comm]
    exact e
  · classical
    intro e hne he
    obtain ⟨j, rfl⟩ : ∃ j, e = j + 3 := ⟨e - 3, by omega⟩
    subst hne
    have hO := H3_topOrbits j
    set O1 : Finset (ZMod (2 ^ (j + 3))) := orbit 3 1 with hO1
    have hB := thm_5_1_b_proved (2 ^ (j + 3)) (j + 3) 1 (by ring) (by omega) odd_one h3
    have hnegmem : negO O1 ∈ topOrbits (2 ^ (j + 3)) 3 := by
      rw [hO1, H19_negO_orbit hev]
      exact mem_image.mpr ⟨1 + half _, mem_filter.mpr ⟨mem_univ _, H19_odd_add_half h2 h4
        (by rw [ZMod.val_one'' (by omega)]; exact odd_one)⟩, rfl⟩
    have hA1 : negO O1 = O1 := by
      rw [hO] at hnegmem
      rcases mem_insert.mp hnegmem with h | h
      · exact h
      · exact absurd (mem_singleton.mp h) ((hB O1 (by rw [hO]; exact mem_insert_self _ _)).1 (by omega))
    have hinvne : inv O1 ≠ O1 := by
      intro h
      have hd := H3_disjoint j
      rw [← hO1, h] at hd
      have h1 : (1 : ZMod (2 ^ (j + 3))) ∈ O1 := H6_self_mem 3 1
      exact Finset.disjoint_left.mp hd h1 h1
    have hbl1 : blockOf O1 = {O1, inv O1} := by
      unfold blockOf
      rw [H19_negO_inv hev, hA1]
      ext x; simp only [mem_insert, mem_singleton]; tauto
    have hbl2 : blockOf (inv O1) = {O1, inv O1} := by
      unfold blockOf
      rw [H3_inv_inv, H19_negO_inv hev, hA1]
      ext x; simp only [mem_insert, mem_singleton]; tauto
    have hblocks : blocks (2 ^ (j + 3)) = {{O1, inv O1}} := by
      unfold blocks
      rw [hO, image_insert, image_singleton, hbl1, hbl2]
      exact insert_eq_of_mem (mem_singleton_self _)
    have hblocksA : blocksA (2 ^ (j + 3)) = {{O1, inv O1}} := by
      unfold blocksA
      rw [hblocks]
      exact filter_true_of_mem (fun B hB => by
        rw [mem_singleton] at hB; subst hB
        exact ⟨O1, mem_insert_self _ _, hA1⟩)
    have hcardO1 : O1.card = 2 ^ (j + 1) := H3_orbit_one_card j
    have hn4 : 2 ^ (j + 3) / 4 = 2 ^ (j + 1) := by
      rw [show 2 ^ (j + 3) = 2 ^ (j + 1) * 4 by ring, Nat.mul_div_cancel _ (by norm_num)]
    refine ⟨by rw [hblocks, card_singleton], by rw [hblocksA, card_singleton], fun B hBm => ?_, ?_, ?_,
      H19_V_eq _ h4⟩
    · rw [hblocks, mem_singleton] at hBm
      subst hBm
      have hu : ({O1, inv O1} : Finset (Finset (ZMod (2 ^ (j + 3))))).biUnion id = O1 ∪ inv O1 := by
        simp
      have hcu : (O1 ∪ inv O1).card = 2 * 2 ^ (j + 1) := by
        rw [card_union_of_disjoint (H3_disjoint j), H3_inv_card, hcardO1]; ring
      have hc2 : ({O1, inv O1} : Finset (Finset (ZMod (2 ^ (j + 3))))).card = 2 :=
        card_pair (Ne.symm hinvne)
      unfold qO blockLen qq
      rw [hu, hcu, hc2, Nat.mul_div_cancel_left _ (by norm_num)]
      congr 1
      rw [show 2 ^ (j + 3) = 2 ^ j * 8 by ring, Nat.mul_div_cancel _ (by norm_num), pow_succ,
        Nat.mul_div_cancel _ (by norm_num)]
    · rw [H4_pow_one_val hω1, inv_pow, show 2 * (2 ^ (j + 3) / 4) = 2 ^ (j + 3) / 2 by omega,
        H7_pow_half_eq_neg_one hev hω, inv_neg, inv_one]
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hq : qq (2 ^ (i + 1 + 3)) % 4 = 1 := by
        unfold qq
        rw [show 2 ^ (i + 1 + 3) / 8 = 2 * 2 ^ i by
          rw [show 2 ^ (i + 1 + 3) = 2 * 2 ^ i * 8 by ring, Nat.mul_div_cancel _ (by norm_num)],
          pow_mul, Nat.pow_mod]
        norm_num
      have hq' : qq (2 ^ (i + 1 + 3)) = 4 * (qq (2 ^ (i + 1 + 3)) / 4) + 1 := by omega
      have h4' : 2 ^ (i + 1 + 3) / 4 * 4 = 2 ^ (i + 1 + 3) := Nat.div_mul_cancel h4
      rw [hq', mul_add, mul_one, ← mul_assoc, h4', pow_add, pow_mul, hω1, one_pow, one_mul]

/-! ## Row 18e — Theorem 5.1(c) in y-form -/

/-- The lower layers are fixed by `S`, layer 0 and the `ν`-data (the induction on the 2-adic layer). -/
theorem H19_lower_eq {n a nodd : ℕ} [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) {L : Type*} [Field L]
    (h h' : ZMod n → L) (hF4 : F4 h) (hF4' : F4 h') (hhalf0 : h (half n) ≠ 0) (hhalf : h (half n) = h' (half n))
    (h0 : ∀ k : ZMod n, 2 ^ a ∣ k.val → h k = h' k)
    (hν : ∀ ρ : ZMod n, Odd ρ.val → h ρ * h (ρ + half n) = h' ρ * h' (ρ + half n)) :
    ∀ k : ZMod n, Even k.val → h k = h' k := by
  have h4 := H19_four_dvd hn ha
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hhv := H19_half_val_eq hn (by omega)
  have key : ∀ d, d ≤ a → ∀ k : ZMod n, Even k.val → ¬ 2 ^ d ∣ k.val → h k = h' k := by
    intro d
    induction d with
    | zero => intro _ k _ hk; exact absurd (by rw [pow_zero]; exact one_dvd _) hk
    | succ d ih =>
      intro hd k hk hkd
      have hxv : (((k.val / 2 : ℕ) : ZMod n)).val = k.val / 2 := H4_hf_val k
      have h2x : 2 * ((k.val / 2 : ℕ) : ZMod n) = k := H4_two_mul_hf k (Nat.not_odd_iff_even.mpr hk)
      have hkv : k.val = 2 * (k.val / 2) := (Nat.mul_div_cancel' (even_iff_two_dvd.mp hk)).symm
      set x : ZMod n := ((k.val / 2 : ℕ) : ZMod n) with hx
      have e1 := hF4 x
      have e2 := hF4' x
      rw [h2x] at e1 e2
      have hprod : h x * h (x + half n) = h' x * h' (x + half n) := by
        rcases Nat.even_or_odd x.val with hxe | hxo
        · have hxd : ¬ 2 ^ d ∣ x.val := by
            intro hdv
            apply hkd
            rw [hxv] at hdv
            rw [hkv, pow_succ']
            exact Nat.mul_dvd_mul_left 2 hdv
          have hdhalf : 2 ^ d ∣ n / 2 := by
            rw [hhv]; exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _
          have hlt : x.val + (half n).val < n := by
            rw [hxv, H6_half_val]
            have := ZMod.val_lt k
            omega
          have hxh : (x + half n).val = x.val + n / 2 := by
            rw [ZMod.val_add_of_lt hlt, H6_half_val]
          have hxhe : Even (x + half n).val := by
            rw [hxh]; exact hxe.add (H6_even_half h4)
          have hxhd : ¬ 2 ^ d ∣ (x + half n).val := by
            rw [hxh]; exact fun hdv => hxd ((Nat.dvd_add_left hdhalf).mp hdv)
          rw [ih (by omega) x hxe hxd, ih (by omega) _ hxhe hxhd]
        · exact hν x hxo
      have hfin : h (half n) * h k = h (half n) * h' k := by
        rw [← e1, hprod, e2, hhalf]
      exact mul_left_cancel₀ hhalf0 hfin
  intro k hk
  by_cases hka : 2 ^ a ∣ k.val
  · exact h0 k hka
  · exact key a le_rfl k hk hka

theorem thm_5_1_c_yform_of (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (hP24 : Set.BijOn (dftA ω) (NFSet n 2) {h | F1 3 2 ω h ∧ F3 ω h ∧ F4 h}) :
    (∀ y ∈ NFSet n 2, ∀ ρ : ZMod n, Odd ρ.val →
      dftA ω (ySubst y) ρ = dftA ω y (ρ + half n) ∧
      dftA ω (ySubst y) ρ * dftA ω (ySubst y) (ρ + half n) = dftA ω y ρ * dftA ω y (ρ + half n)) ∧
    (∀ y ∈ NFSet n 2, ∀ y' ∈ NFSet n 2,
      ((S y = S y' ∧ (∀ k : ZMod n, 2 ^ a ∣ k.val → dftA ω y k = dftA ω y' k) ∧
        ∀ ρ : ZMod n, Odd ρ.val → dftA ω y ρ * dftA ω y (ρ + half n) = dftA ω y' ρ * dftA ω y' (ρ + half n)) ↔
       ∀ k : ZMod n, Even k.val → dftA ω y k = dftA ω y' k)) ∧
    ∀ y ∈ NFSet n 2, ∀ h ∈ topData n 3 2 (1 : L) ω,
      (∀ ρ : ZMod n, Odd ρ.val → h ρ * h (ρ + half n) = dftA ω y ρ * dftA ω y (ρ + half n)) →
      ∃! y' : ZMod n → GaloisField 3 (n / 2), y' ∈ fibre ω y ∧ ∀ ρ : ZMod n, Odd ρ.val → dftA ω y' ρ = h ρ := by
  have h4 := H19_four_dvd hn ha
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hev : Even n := even_iff_two_dvd.mpr h2
  have hn8 : 8 ≤ n := Nat.le_of_dvd (NeZero.pos n) (H19_eight_dvd hn ha)
  have hω0 : ω ≠ 0 := hω.ne_zero (NeZero.ne n)
  have h5a := thm_5_1_a_proved n a nodd hn ha hodd h3 ω hω
  refine ⟨?_, ?_, ?_⟩
  · intro y hy ρ hρ
    have hodd' := (h5a.2.2 y hy).2.2.2.1
    have hρh : Odd (ρ + half n).val := H19_odd_add_half h2 h4 hρ
    refine ⟨hodd' ρ hρ, ?_⟩
    rw [hodd' ρ hρ, hodd' _ hρh, add_assoc, H6_half_add_half h2, add_zero, mul_comm]
  · intro y hy y' hy'
    obtain ⟨-, hF3, hF4⟩ := hP24.mapsTo hy
    obtain ⟨-, -, hF4'⟩ := hP24.mapsTo hy'
    have hSy := H19_dftA_half hev (by omega) hω y
    have hSy' := H19_dftA_half hev (by omega) hω y'
    have hhe := H19_even_half (n := n) h4
    constructor
    · rintro ⟨hS, h0, hν⟩
      have hhalf : dftA ω y (half n) = dftA ω y' (half n) := by rw [hSy, hSy', hS]
      exact H19_lower_eq hn ha _ _ hF4 hF4' (H5_F3_ne hω0 _ hF3 _) hhalf h0 hν
    · intro heven
      refine ⟨?_, fun k hk => heven k ?_, fun ρ _ => ?_⟩
      · apply (algebraMap (GaloisField 3 (n / 2)) L).injective
        rw [← hSy, ← hSy']
        exact heven _ hhe
      · obtain ⟨c, hc⟩ := hk
        rw [hc, show 2 ^ a = 2 * 2 ^ (a - 1) by rw [← pow_succ']; congr 1; omega, mul_assoc]
        exact even_two_mul _
      · rw [hF4 ρ, hF4' ρ, heven _ hhe, heven _ (H19_even_two_mul h2 ρ)]
  · intro y hy h hh hν
    obtain ⟨hF1, hF3, hF4⟩ := hP24.mapsTo hy
    obtain ⟨htop, hzero⟩ := hh
    set H : ZMod n → L := fun k => if Odd k.val then h k else dftA ω y k with hH
    have hHodd : ∀ k : ZMod n, Odd k.val → H k = h k := fun k hk => by rw [hH]; simp only [hk, ite_true]
    have hHeven : ∀ k : ZMod n, Even k.val → H k = dftA ω y k := fun k hk => by
      rw [hH]; simp only [Nat.not_odd_iff_even.mpr hk, ite_false]
    have hHF : H ∈ {h | F1 3 2 ω h ∧ F3 ω h ∧ F4 h} := by
      refine ⟨fun k => ?_, fun k => ?_, fun k => ?_⟩
      · rcases Nat.even_or_odd k.val with hk | hk
        · rw [hHeven _ hk, hHeven _ (H19_even_three_mul h2 hk)]; exact hF1 k
        · rw [hHodd _ hk, hHodd _ (H19_odd_three_mul h2 hk)]; exact (htop k hk).1
      · rcases Nat.even_or_odd k.val with hk | hk
        · rw [hHeven _ hk, hHeven _ (H19_even_neg h2 hk)]; exact hF3 k
        · rw [hHodd _ hk, hHodd _ (H6_odd_neg h2 hk), (htop k hk).2, one_mul]
      · rw [hHeven _ (H19_even_half h4), hHeven _ (H19_even_two_mul h2 k)]
        rcases Nat.even_or_odd k.val with hk | hk
        · rw [hHeven _ hk, hHeven _ (H19_even_add_half h2 h4 hk)]; exact hF4 k
        · rw [hHodd _ hk, hHodd _ (H19_odd_add_half h2 h4 hk), hν k hk]; exact hF4 k
    obtain ⟨y', hy', hy'H⟩ := hP24.surjOn hHF
    refine ⟨y', ⟨⟨hy', fun k hk => ?_⟩, fun ρ hρ => ?_⟩, ?_⟩
    · rw [hy'H, hHeven _ hk]
    · rw [hy'H, hHodd _ hρ]
    · rintro y'' ⟨⟨hy'', hfib⟩, htop''⟩
      apply hP24.injOn hy'' hy'
      rw [hy'H]
      funext k
      rcases Nat.even_or_odd k.val with hk | hk
      · rw [hHeven _ hk, hfib k hk]
      · rw [hHodd _ hk, htop'' k hk]

/-! ## Part E — fibres: differences of two points of a fibre (Theorem 5.1(d), Figure 1) -/

section Fibre

variable {n : ℕ} [NeZero n]

theorem H19_charP (n : ℕ) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] : CharP L 3 :=
  charP_of_injective_algebraMap' (GaloisField 3 (n / 2)) 3

theorem H19_natCast_ne_zero (n : ℕ) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (h3 : ¬ 3 ∣ n) :
    (n : L) ≠ 0 := by
  have := H19_charP n (L := L)
  rw [Ne, CharP.cast_eq_zero_iff L 3]
  exact h3

theorem H19_two_ne_zero (n : ℕ) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] : (2 : L) ≠ 0 := by
  have := H19_charP n (L := L)
  exact H5_two_ne_zero 3 (by norm_num)

/-- (L1) iterated `n/4` times: `ȳ_t = y_{t+m}`. -/
theorem H19_bar_shift (h4 : 4 ∣ n) {K : Type*} [CommRing K] {y : ZMod n → K} (hL1 : L1 3 ((2 : ℕ) : ℤ) y)
    (t : ZMod n) : bar n (y t) = y (t + half n) := by
  have hit := H6_L1_iter hL1 (n / 4) t
  have hidx : ((n / 4 : ℕ) : ZMod n) * ((((2 : ℕ) : ℤ)) : ZMod n) = half n := by
    unfold half
    obtain ⟨c, hc⟩ := h4
    have h' : n / 2 = n / 4 * 2 := by omega
    rw [h']; push_cast; ring
  unfold bar
  rw [← hit, hidx]

theorem H19_delta_step {y1 y2 : ZMod n → GaloisField 3 (n / 2)} (h1 : L1 3 ((2 : ℕ) : ℤ) y1)
    (h2 : L1 3 ((2 : ℕ) : ℤ) y2) (t : ZMod n) : y1 (t + 2) - y2 (t + 2) = (y1 t - y2 t) ^ 3 := by
  have e1 := h1 t
  have e2 := h2 t
  have hc : ((((2 : ℕ) : ℤ)) : ZMod n) = 2 := by norm_num
  rw [hc] at e1 e2
  rw [e1, e2, sub_pow_char]

theorem H19_delta_iter {y1 y2 : ZMod n → GaloisField 3 (n / 2)} (h1 : L1 3 ((2 : ℕ) : ℤ) y1)
    (h2 : L1 3 ((2 : ℕ) : ℤ) y2) (s : ZMod n) (j : ℕ) :
    y1 (s + ((2 * j : ℕ) : ZMod n)) - y2 (s + ((2 * j : ℕ) : ZMod n)) = (y1 s - y2 s) ^ (3 ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show s + ((2 * (j + 1) : ℕ) : ZMod n) = (s + ((2 * j : ℕ) : ZMod n)) + 2 by push_cast; ring,
      H19_delta_step h1 h2, ih, ← pow_mul, pow_succ]

/-- `A(t) := ∑_k (ŷ1(k) - ŷ2(k)) ω^{-kt}`. -/
noncomputable def H19_A {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L)
    (y1 y2 : ZMod n → GaloisField 3 (n / 2)) (t : ZMod n) : L :=
  ∑ k, (dftA ω y1 k - dftA ω y2 k) * ((ω ^ k.val)⁻¹) ^ t.val

variable {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L]

theorem H19_alg_delta
    (hFI : ∀ (ω' : L), IsPrimitiveRoot ω' n → (n : L) ≠ 0 → ∀ y : ZMod n → L,
      (∀ t : ZMod n, y t = (n : L)⁻¹ * ∑ k : ZMod n, dft ω' y k * ((ω' ^ k.val)⁻¹) ^ t.val) ∧
        dft ω' y (half n) = S y)
    {ω : L} (hω : IsPrimitiveRoot ω n) (hnL : (n : L) ≠ 0) (y1 y2 : ZMod n → GaloisField 3 (n / 2))
    (t : ZMod n) : algebraMap _ L (y1 t - y2 t) = (n : L)⁻¹ * H19_A ω y1 y2 t := by
  have e1 : algebraMap _ L (y1 t) = _ := (hFI ω hω hnL (fun s => algebraMap _ L (y1 s))).1 t
  have e2 : algebraMap _ L (y2 t) = _ := (hFI ω hω hnL (fun s => algebraMap _ L (y2 s))).1 t
  rw [map_sub, e1, e2, ← mul_sub, ← sum_sub_distrib]
  unfold H19_A dftA
  congr 1
  refine sum_congr rfl (fun k _ => ?_)
  ring

theorem H19_sum_shift (hev : Even n) {ω : L} (hω : IsPrimitiveRoot ω n) (D : ZMod n → L)
    (hD : ∀ k : ZMod n, Even k.val → D k = 0) (t : ZMod n) :
    ∑ k, D k * ((ω ^ k.val)⁻¹) ^ (t + half n).val = -∑ k, D k * ((ω ^ k.val)⁻¹) ^ t.val := by
  rw [← sum_neg_distrib]
  refine sum_congr rfl (fun k _ => ?_)
  have hw : ((ω ^ k.val)⁻¹) ^ n = 1 := by
    rw [inv_pow, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, inv_one]
  rw [H7_pow_val_add _ hw, H6_half_val]
  rcases Nat.even_or_odd k.val with hk | hk
  · rw [hD k hk]; ring
  · have hh : ((ω ^ k.val)⁻¹) ^ (n / 2) = -1 := by
      rw [inv_pow, H19_pow_half_odd hev hω hk, inv_neg, inv_one]
    rw [hh]; ring

theorem H19_delta_half (hev : Even n) (h3 : ¬ 3 ∣ n)
    (hFI : ∀ (ω' : L), IsPrimitiveRoot ω' n → (n : L) ≠ 0 → ∀ y : ZMod n → L,
      (∀ t : ZMod n, y t = (n : L)⁻¹ * ∑ k : ZMod n, dft ω' y k * ((ω' ^ k.val)⁻¹) ^ t.val) ∧
        dft ω' y (half n) = S y)
    {ω : L} (hω : IsPrimitiveRoot ω n) {y1 y2 : ZMod n → GaloisField 3 (n / 2)}
    (hD : ∀ k : ZMod n, Even k.val → dftA ω y1 k = dftA ω y2 k) (t : ZMod n) :
    y1 (t + half n) - y2 (t + half n) = -(y1 t - y2 t) := by
  have hnL := H19_natCast_ne_zero n (L := L) h3
  apply (algebraMap (GaloisField 3 (n / 2)) L).injective
  rw [map_neg, H19_alg_delta hFI hω hnL, H19_alg_delta hFI hω hnL]
  unfold H19_A
  rw [H19_sum_shift hev hω _ (fun k hk => by rw [hD k hk, sub_self]), mul_neg]

theorem H19_inv_zero
    (hFI : ∀ (ω' : L), IsPrimitiveRoot ω' n → (n : L) ≠ 0 → ∀ y : ZMod n → L,
      (∀ t : ZMod n, y t = (n : L)⁻¹ * ∑ k : ZMod n, dft ω' y k * ((ω' ^ k.val)⁻¹) ^ t.val) ∧
        dft ω' y (half n) = S y)
    {ω : L} (hω : IsPrimitiveRoot ω n) (hnL : (n : L) ≠ 0) (F : ZMod n → L)
    (hF : ∀ t : ZMod n, ∑ k, F k * ((ω ^ k.val)⁻¹) ^ t.val = 0) (k : ZMod n) : F k = 0 := by
  have e := (hFI ω⁻¹ hω.inv hnL F).1 k
  rw [e]
  have h0 : ∀ t : ZMod n, dft ω⁻¹ F t = 0 := by
    intro t
    rw [← hF t]
    unfold dft
    refine sum_congr rfl (fun j _ => ?_)
    congr 1
    simp only [inv_pow, ← pow_mul]
    rw [mul_comm]
  simp [h0]

/-- On a fibre, `y1 - y2` is anti-periodic, so the `y^-` parts differ by `y1 - y2` and the `y^+` parts agree. -/
theorem H19_yMinus_diff (h4 : 4 ∣ n) (h3 : ¬ 3 ∣ n)
    (hFI : ∀ (ω' : L), IsPrimitiveRoot ω' n → (n : L) ≠ 0 → ∀ y : ZMod n → L,
      (∀ t : ZMod n, y t = (n : L)⁻¹ * ∑ k : ZMod n, dft ω' y k * ((ω' ^ k.val)⁻¹) ^ t.val) ∧
        dft ω' y (half n) = S y)
    {ω : L} (hω : IsPrimitiveRoot ω n) {y1 y2 : ZMod n → GaloisField 3 (n / 2)}
    (h1 : L1 3 ((2 : ℕ) : ℤ) y1) (h2 : L1 3 ((2 : ℕ) : ℤ) y2)
    (hD : ∀ k : ZMod n, Even k.val → dftA ω y1 k = dftA ω y2 k) (t : ZMod n) :
    yMinus n (y1 t) - yMinus n (y2 t) = y1 t - y2 t ∧ yPlus n (y1 t) = yPlus n (y2 t) := by
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h4)
  have hs := H19_delta_half hev h3 hFI hω hD t
  have h2F := H3_two_ne_zero (n / 2)
  unfold yMinus yPlus
  rw [H19_bar_shift h4 h1, H19_bar_shift h4 h2]
  constructor
  · rw [div_sub_div_same, div_eq_iff h2F]
    linear_combination (-1 : GaloisField 3 (n / 2)) * hs
  · rw [div_left_inj' h2F]
    linear_combination hs

/-- The core of Theorem 5.1(d): on a fibre, `y1_0 = y2_0` iff the `g_+` data agree, and `y1_1 = y2_1` iff the `g_-`
data agree. -/
theorem H19_d_core (h4 : 4 ∣ n) (h3 : ¬ 3 ∣ n)
    (hFI : ∀ (ω' : L), IsPrimitiveRoot ω' n → (n : L) ≠ 0 → ∀ y : ZMod n → L,
      (∀ t : ZMod n, y t = (n : L)⁻¹ * ∑ k : ZMod n, dft ω' y k * ((ω' ^ k.val)⁻¹) ^ t.val) ∧
        dft ω' y (half n) = S y)
    {ω : L} (hω : IsPrimitiveRoot ω n) {y1 y2 : ZMod n → GaloisField 3 (n / 2)}
    (hL1a : L1 3 ((2 : ℕ) : ℤ) y1) (hL1b : L1 3 ((2 : ℕ) : ℤ) y2)
    (hD : ∀ k : ZMod n, Even k.val → dftA ω y1 k = dftA ω y2 k) :
    (y1 0 - y2 0 = 0 ↔ ∀ ρ : ZMod n, Odd ρ.val →
        dftA ω y1 ρ + dftA ω y1 (ρ + half n) = dftA ω y2 ρ + dftA ω y2 (ρ + half n)) ∧
    (y1 1 - y2 1 = 0 ↔ ∀ ρ : ZMod n, Odd ρ.val →
        dftA ω y1 ρ - dftA ω y1 (ρ + half n) = dftA ω y2 ρ - dftA ω y2 (ρ + half n)) := by
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hev : Even n := even_iff_two_dvd.mpr h2
  have hn4 : 4 ≤ n := Nat.le_of_dvd (NeZero.pos n) h4
  have hnL := H19_natCast_ne_zero n (L := L) h3
  have hninv : (n : L)⁻¹ ≠ 0 := inv_ne_zero hnL
  have h2L := H19_two_ne_zero n (L := L)
  have hω1 := hω.pow_eq_one
  have hZA : ∀ t : ZMod n, y1 t - y2 t = 0 ↔ H19_A ω y1 y2 t = 0 := by
    intro t
    have e := H19_alg_delta hFI hω hnL y1 y2 t
    constructor
    · intro h
      rw [h, map_zero] at e
      exact (mul_eq_zero.mp e.symm).resolve_left hninv
    · intro h
      apply (algebraMap (GaloisField 3 (n / 2)) L).injective
      rw [e, h, mul_zero, map_zero]
  have hZe : ∀ t : ZMod n, Even t.val → y1 t - y2 t = (y1 0 - y2 0) ^ (3 ^ (t.val / 2)) := by
    intro t ht
    have ht' : t = 0 + ((2 * (t.val / 2) : ℕ) : ZMod n) := by
      rw [zero_add, Nat.mul_div_cancel' (even_iff_two_dvd.mp ht), ZMod.natCast_zmod_val]
    conv_lhs => rw [ht']
    exact H19_delta_iter hL1a hL1b 0 _
  have hZo : ∀ t : ZMod n, Odd t.val → y1 t - y2 t = (y1 1 - y2 1) ^ (3 ^ (t.val / 2)) := by
    intro t ht
    have ht' : t = 1 + ((2 * (t.val / 2) : ℕ) : ZMod n) := by
      have hv : 2 * (t.val / 2) + 1 = t.val := by rw [Nat.odd_iff] at ht; omega
      rw [show (1 : ZMod n) + ((2 * (t.val / 2) : ℕ) : ZMod n) = ((2 * (t.val / 2) + 1 : ℕ) : ZMod n) by
        push_cast; ring, hv, ZMod.natCast_zmod_val]
    conv_lhs => rw [ht']
    exact H19_delta_iter hL1a hL1b 1 _
  have hw : ∀ k : ZMod n, (ω ^ (k + half n).val)⁻¹ = -(ω ^ k.val)⁻¹ := by
    intro k
    rw [H7_pow_val_add ω hω1, H6_half_val, H7_pow_half_eq_neg_one hev hω, mul_neg_one, inv_neg]
  have hB : ∀ t : ZMod n, ∑ k, (dftA ω y1 (k + half n) - dftA ω y2 (k + half n)) * ((ω ^ k.val)⁻¹) ^ t.val =
      (-1) ^ t.val * H19_A ω y1 y2 t := by
    intro t
    have hsq : ((-1 : L) ^ t.val) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    have hA' : H19_A ω y1 y2 t = ∑ k, (dftA ω y1 (k + half n) - dftA ω y2 (k + half n)) *
        ((ω ^ (k + half n).val)⁻¹) ^ t.val := by
      unfold H19_A
      exact (Equiv.sum_comp (Equiv.addRight (half n))
        (fun k => (dftA ω y1 k - dftA ω y2 k) * ((ω ^ k.val)⁻¹) ^ t.val)).symm
    rw [hA', mul_sum]
    refine sum_congr rfl (fun k _ => ?_)
    rw [hw, neg_pow]
    linear_combination (-((dftA ω y1 (k + half n) - dftA ω y2 (k + half n)) * ((ω ^ k.val)⁻¹) ^ t.val)) * hsq
  have hE : ∀ t : ZMod n, ∑ k, ((dftA ω y1 k - dftA ω y2 k) + (dftA ω y1 (k + half n) - dftA ω y2 (k + half n))) *
      ((ω ^ k.val)⁻¹) ^ t.val = (1 + (-1) ^ t.val) * H19_A ω y1 y2 t := by
    intro t
    simp only [add_mul, sum_add_distrib]
    rw [hB t]
    unfold H19_A
    ring
  have hE' : ∀ t : ZMod n, ∑ k, ((dftA ω y1 k - dftA ω y2 k) - (dftA ω y1 (k + half n) - dftA ω y2 (k + half n))) *
      ((ω ^ k.val)⁻¹) ^ t.val = (1 - (-1) ^ t.val) * H19_A ω y1 y2 t := by
    intro t
    have hsplit : ∑ k, ((dftA ω y1 k - dftA ω y2 k) - (dftA ω y1 (k + half n) - dftA ω y2 (k + half n))) *
        ((ω ^ k.val)⁻¹) ^ t.val = H19_A ω y1 y2 t -
          ∑ k, (dftA ω y1 (k + half n) - dftA ω y2 (k + half n)) * ((ω ^ k.val)⁻¹) ^ t.val := by
      unfold H19_A
      rw [← sum_sub_distrib]
      exact sum_congr rfl (fun k _ => by ring)
    rw [hsplit, hB t]
    ring
  have h1v : (1 : ZMod n).val = 1 := ZMod.val_one'' (by omega)
  constructor
  · constructor
    · intro h0 ρ hρ
      have hall : ∀ t : ZMod n, ∑ k, ((dftA ω y1 k - dftA ω y2 k) +
          (dftA ω y1 (k + half n) - dftA ω y2 (k + half n))) * ((ω ^ k.val)⁻¹) ^ t.val = 0 := by
        intro t
        rw [hE t]
        rcases Nat.even_or_odd t.val with ht | ht
        · rw [(hZA t).mp (by rw [hZe t ht, h0, zero_pow (pow_ne_zero _ (by norm_num))]), mul_zero]
        · rw [ht.neg_one_pow]; ring
      have := H19_inv_zero hFI hω hnL _ hall ρ
      linear_combination this
    · intro hρ
      rw [hZA 0]
      have hEk : ∀ k : ZMod n, (dftA ω y1 k - dftA ω y2 k) +
          (dftA ω y1 (k + half n) - dftA ω y2 (k + half n)) = 0 := by
        intro k
        rcases Nat.even_or_odd k.val with hk | hk
        · rw [hD k hk, hD _ (H19_even_add_half h2 h4 hk)]; ring
        · linear_combination hρ k hk
      have h := hE 0
      simp only [hEk, zero_mul, sum_const_zero, ZMod.val_zero, pow_zero] at h
      have h' : (2 : L) * H19_A ω y1 y2 0 = 0 := by linear_combination -h
      exact (mul_eq_zero.mp h').resolve_left h2L
  · constructor
    · intro h0 ρ hρ
      have hall : ∀ t : ZMod n, ∑ k, ((dftA ω y1 k - dftA ω y2 k) -
          (dftA ω y1 (k + half n) - dftA ω y2 (k + half n))) * ((ω ^ k.val)⁻¹) ^ t.val = 0 := by
        intro t
        rw [hE' t]
        rcases Nat.even_or_odd t.val with ht | ht
        · rw [ht.neg_one_pow]; ring
        · rw [(hZA t).mp (by rw [hZo t ht, h0, zero_pow (pow_ne_zero _ (by norm_num))]), mul_zero]
      have := H19_inv_zero hFI hω hnL _ hall ρ
      linear_combination this
    · intro hρ
      rw [hZA 1]
      have hEk : ∀ k : ZMod n, (dftA ω y1 k - dftA ω y2 k) -
          (dftA ω y1 (k + half n) - dftA ω y2 (k + half n)) = 0 := by
        intro k
        rcases Nat.even_or_odd k.val with hk | hk
        · rw [hD k hk, hD _ (H19_even_add_half h2 h4 hk)]; ring
        · linear_combination hρ k hk
      have h := hE' 1
      simp only [hEk, zero_mul, sum_const_zero, h1v, pow_one] at h
      have h' : (2 : L) * H19_A ω y1 y2 1 = 0 := by linear_combination -h
      exact (mul_eq_zero.mp h').resolve_left h2L

end Fibre

/-! ## Row 18f — Theorem 5.1(d) in y-form -/

theorem thm_5_1_d_yform_of (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (_hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (y : ZMod n → GaloisField 3 (n / 2)) (_hy : y ∈ NFSet n 2)
    (hFI : ∀ (ω' : L), IsPrimitiveRoot ω' n → (n : L) ≠ 0 → ∀ y : ZMod n → L,
      (∀ t : ZMod n, y t = (n : L)⁻¹ * ∑ k : ZMod n, dft ω' y k * ((ω' ^ k.val)⁻¹) ^ t.val) ∧
        dft ω' y (half n) = S y) :
    ∀ y1 ∈ fibre ω y, ∀ y2 ∈ fibre ω y,
      (yMinus n (y1 0) = yMinus n (y2 0) ↔
        ∀ ρ : ZMod n, Odd ρ.val → dftA ω y1 ρ + dftA ω y1 (ρ + half n) = dftA ω y2 ρ + dftA ω y2 (ρ + half n)) ∧
      (yMinus n (y1 1) = yMinus n (y2 1) ↔
        ∀ ρ : ZMod n, Odd ρ.val → dftA ω y1 ρ - dftA ω y1 (ρ + half n) = dftA ω y2 ρ - dftA ω y2 (ρ + half n)) := by
  have h4 := H19_four_dvd hn ha
  intro y1 hy1 y2 hy2
  obtain ⟨⟨hL1a, -, -, -⟩, hf1⟩ := hy1
  obtain ⟨⟨hL1b, -, -, -⟩, hf2⟩ := hy2
  have hD : ∀ k : ZMod n, Even k.val → dftA ω y1 k = dftA ω y2 k := fun k hk => by rw [hf1 k hk, hf2 k hk]
  have hcore := H19_d_core h4 h3 hFI hω hL1a hL1b hD
  have e0 := (H19_yMinus_diff h4 h3 hFI hω hL1a hL1b hD 0).1
  have e1 := (H19_yMinus_diff h4 h3 hFI hω hL1a hL1b hD 1).1
  constructor
  · rw [← sub_eq_zero, e0]; exact hcore.1
  · rw [← sub_eq_zero, e1]; exact hcore.2

/-! ## Coverage — Figure 1 caption, y-form -/

theorem H19_encard_two {α β γ : Type*} [Field γ] (S : Set α) (g : α → β) (k : α → γ) (c : γ)
    (hk : ∀ a ∈ S, k a ^ 2 = c) (hg : ∀ a ∈ S, ∀ b ∈ S, k a = k b → g a = g b) : (g '' S).encard ≤ 2 := by
  classical
  rcases S.eq_empty_or_nonempty with hS | ⟨a0, ha0⟩
  · rw [hS, Set.image_empty, Set.encard_empty]; simp
  · have hpm : ∀ a ∈ S, k a = k a0 ∨ k a = -k a0 := fun a ha =>
      sq_eq_sq_iff_eq_or_eq_neg.mp (by rw [hk a ha, hk a0 ha0])
    by_cases hw : ∃ b ∈ S, k b = -k a0
    · obtain ⟨b0, hb0, hkb⟩ := hw
      have hsub : g '' S ⊆ {g a0, g b0} := by
        rintro _ ⟨a, ha, rfl⟩
        rcases hpm a ha with h | h
        · exact Or.inl (hg a ha a0 ha0 h)
        · exact Or.inr (hg a ha b0 hb0 (h.trans hkb.symm))
      calc (g '' S).encard ≤ ({g a0, g b0} : Set β).encard := Set.encard_le_encard hsub
        _ ≤ ({g b0} : Set β).encard + 1 := Set.encard_insert_le _ _
        _ = 2 := by rw [Set.encard_singleton]; rfl
    · have hsub : g '' S ⊆ {g a0} := by
        rintro _ ⟨a, ha, rfl⟩
        rcases hpm a ha with h | h
        · exact hg a ha a0 ha0 h
        · exact absurd ⟨a, ha, h⟩ hw
      calc (g '' S).encard ≤ ({g a0} : Set β).encard := Set.encard_le_encard hsub
        _ = 1 := Set.encard_singleton _
        _ ≤ 2 := by norm_num

theorem H19_norm_split (n : ℕ) (h4 : 4 ∣ n) (x : GaloisField 3 (n / 2)) :
    Nm n x = yPlus n x ^ 2 - yMinus n x ^ 2 := by
  have h2F := H3_two_ne_zero (n / 2)
  rw [(sec_2_2_norm_proved n h4 x).1]
  unfold yPlus yMinus
  field_simp
  ring

theorem fig1_caption_of (n : ℕ) [NeZero n] (hn : n % 24 = 8) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L]
    (ω : L) (hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2)
    (hFI : ∀ (ω' : L), IsPrimitiveRoot ω' n → (n : L) ≠ 0 → ∀ y : ZMod n → L,
      (∀ t : ZMod n, y t = (n : L)⁻¹ * ∑ k : ZMod n, dft ω' y k * ((ω' ^ k.val)⁻¹) ^ t.val) ∧
        dft ω' y (half n) = S y) :
    let gp : (ZMod n → GaloisField 3 (n / 2)) → ZMod n → L :=
      fun y' ρ => if Odd ρ.val then dftA ω y' ρ + dftA ω y' (ρ + half n) else 0
    let gm : (ZMod n → GaloisField 3 (n / 2)) → ZMod n → L :=
      fun y' ρ => if Odd ρ.val then dftA ω y' ρ - dftA ω y' (ρ + half n) else 0
    (gp '' {y' | y' ∈ fibre ω y ∧ Nm n (y' 0) = -1}).encard ≤ 2 ∧
      (gm '' {y' | y' ∈ fibre ω y ∧ Nm n (y' 1) = -1}).encard ≤ 2 ∧
      ∀ y' ∈ fibre ω y, gp (ySubst y') = gp y' ∧ gm (ySubst y') = -gm y' := by
  intro gp gm
  have h8 : 8 ∣ n := by omega
  have h4 : 4 ∣ n := dvd_trans (by norm_num) h8
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have h3 : ¬ 3 ∣ n := by omega
  have hyf : y ∈ fibre ω y := ⟨hy, fun _ _ => rfl⟩
  have hfib : ∀ y1 ∈ fibre ω y, ∀ y2 ∈ fibre ω y,
      L1 3 ((2 : ℕ) : ℤ) y1 ∧ L1 3 ((2 : ℕ) : ℤ) y2 ∧ ∀ k : ZMod n, Even k.val → dftA ω y1 k = dftA ω y2 k := by
    rintro y1 ⟨⟨hL1a, -, -, -⟩, hf1⟩ y2 ⟨⟨hL1b, -, -, -⟩, hf2⟩
    exact ⟨hL1a, hL1b, fun k hk => by rw [hf1 k hk, hf2 k hk]⟩
  have hnorm : ∀ t : ZMod n, ∀ y' ∈ fibre ω y, Nm n (y' t) = -1 →
      yMinus n (y' t) ^ 2 = yPlus n (y t) ^ 2 + 1 := by
    intro t y' hy' hN
    obtain ⟨hA, hB, hD⟩ := hfib y' hy' y hyf
    have hp := (H19_yMinus_diff h4 h3 hFI hω hA hB hD t).2
    rw [H19_norm_split n h4, hp] at hN
    linear_combination -hN
  have hdiff : ∀ t : ZMod n, ∀ y1 ∈ fibre ω y, ∀ y2 ∈ fibre ω y,
      yMinus n (y1 t) = yMinus n (y2 t) ↔ y1 t - y2 t = 0 := by
    intro t y1 hy1 y2 hy2
    obtain ⟨hA, hB, hD⟩ := hfib y1 hy1 y2 hy2
    rw [← sub_eq_zero, (H19_yMinus_diff h4 h3 hFI hω hA hB hD t).1]
  refine ⟨?_, ?_, ?_⟩
  · refine H19_encard_two _ gp (fun y' => yMinus n (y' 0)) (yPlus n (y 0) ^ 2 + 1)
      (fun y' hy' => hnorm 0 y' hy'.1 hy'.2) (fun y1 hy1 y2 hy2 hk => ?_)
    obtain ⟨hA, hB, hD⟩ := hfib y1 hy1.1 y2 hy2.1
    have hc := ((H19_d_core h4 h3 hFI hω hA hB hD).1.mp ((hdiff 0 y1 hy1.1 y2 hy2.1).mp hk))
    funext ρ
    simp only [gp]
    split_ifs with hρ
    · exact hc ρ hρ
    · rfl
  · refine H19_encard_two _ gm (fun y' => yMinus n (y' 1)) (yPlus n (y 1) ^ 2 + 1)
      (fun y' hy' => hnorm 1 y' hy'.1 hy'.2) (fun y1 hy1 y2 hy2 hk => ?_)
    obtain ⟨hA, hB, hD⟩ := hfib y1 hy1.1 y2 hy2.1
    have hc := ((H19_d_core h4 h3 hFI hω hA hB hD).2.mp ((hdiff 1 y1 hy1.1 y2 hy2.1).mp hk))
    funext ρ
    simp only [gm]
    split_ifs with hρ
    · exact hc ρ hρ
    · rfl
  · intro y' _
    have hs : ∀ k : ZMod n, Odd k.val → dftA ω (ySubst y') k = dftA ω y' (k + half n) := fun k hk => by
      rw [H6_dftA_subst h2 h4 hω.pow_eq_one, H6_u_odd h2 hk]
    have hs' : ∀ k : ZMod n, Odd k.val → dftA ω (ySubst y') (k + half n) = dftA ω y' k := fun k hk => by
      rw [hs _ (H19_odd_add_half h2 h4 hk), add_assoc, H6_half_add_half h2, add_zero]
    constructor
    · funext ρ
      simp only [gp]
      split_ifs with hρ
      · rw [hs ρ hρ, hs' ρ hρ, add_comm]
      · rfl
    · funext ρ
      simp only [gm, Pi.neg_apply]
      split_ifs with hρ
      · rw [hs ρ hρ, hs' ρ hρ, neg_sub]
      · rw [neg_zero]

/-! ## Part F — blocks: cards, disjointness, the exponent count `∑ ≤ n/8`, the real bound -/

section Blocks

variable {n : ℕ} [NeZero n]

theorem H19_mem_blocks {B : Finset (Finset (ZMod n))} (hB : B ∈ blocks n) :
    ∃ k : ZMod n, Odd k.val ∧ B = blockOf (orbit 3 k) := by
  obtain ⟨O, hO, rfl⟩ := mem_image.mp hB
  obtain ⟨k, hk, rfl⟩ := mem_image.mp hO
  exact ⟨k, (mem_filter.mp hk).2, rfl⟩

theorem H19_blockOf_mem (hev : Even n) (h2 : 2 ∣ n) (h4 : 4 ∣ n) {k : ZMod n} (hk : Odd k.val)
    {O' : Finset (ZMod n)} (hO' : O' ∈ blockOf (orbit 3 k)) : ∃ z : ZMod n, Odd z.val ∧ O' = orbit 3 z := by
  unfold blockOf at hO'
  simp only [mem_insert, mem_singleton] at hO'
  rcases hO' with rfl | rfl | rfl | rfl
  · exact ⟨k, hk, rfl⟩
  · exact ⟨-k, H6_odd_neg h2 hk, H6_inv_orbit 3 k⟩
  · exact ⟨k + half n, H19_odd_add_half h2 h4 hk, H19_negO_orbit hev k⟩
  · refine ⟨-k + half n, H19_odd_add_half h2 h4 (H6_odd_neg h2 hk), ?_⟩
    rw [H6_inv_orbit, H19_negO_orbit hev]

theorem H19_blockOf_closed (hev : Even n) (O O' : Finset (ZMod n)) (hO' : O' ∈ blockOf O) :
    blockOf O' = blockOf O := by
  unfold blockOf at hO' ⊢
  simp only [mem_insert, mem_singleton] at hO'
  rcases hO' with rfl | rfl | rfl | rfl
  · rfl
  all_goals
    simp only [← H19_negO_inv hev, H19_negO_negO hev, H3_inv_inv]
    ext x
    simp only [mem_insert, mem_singleton]
    tauto

theorem H19_top_mem {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {z : ZMod n} (hz : Odd z.val) : inv (orbit 3 z) ≠ orbit 3 z :=
  ((thm_4_1_pairs_proved n a nodd hn ha hodd h3).1 _ (mem_image.mpr ⟨z, mem_filter.mpr ⟨mem_univ _, hz⟩, rfl⟩)).2.1

theorem H19_card_AB {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {B : Finset (Finset (ZMod n))} (hB : B ∈ blocks n) {O' : Finset (ZMod n)} (hO' : O' ∈ B)
    (hAB : IsCaseA O' ∨ IsCaseB O') : B = {O', inv O'} ∧ B.card = 2 ∧ ∃ z : ZMod n, Odd z.val ∧ O' = orbit 3 z := by
  have h4 := H19_four_dvd hn ha
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hev : Even n := even_iff_two_dvd.mpr h2
  obtain ⟨k, hk, rfl⟩ := H19_mem_blocks hB
  obtain ⟨z, hz, rfl⟩ := H19_blockOf_mem hev h2 h4 hk hO'
  have hcl := H19_blockOf_closed hev _ _ hO'
  rw [← hcl]
  have hne := H19_top_mem hn ha hodd h3 hz
  have hBeq : blockOf (orbit 3 z) = {orbit 3 z, inv (orbit 3 z)} := by
    unfold blockOf
    rcases hAB with hA | hB'
    · have hA' : negO (orbit 3 z) = orbit 3 z := hA
      rw [H19_negO_inv hev, hA']
      ext x; simp only [mem_insert, mem_singleton]; tauto
    · have hB'' : negO (orbit 3 z) = inv (orbit 3 z) := hB'
      rw [H19_negO_inv hev, hB'', H3_inv_inv]
      ext x; simp only [mem_insert, mem_singleton]; tauto
  exact ⟨hBeq, by rw [hBeq]; exact card_pair (Ne.symm hne), z, hz, rfl⟩

theorem H19_card_C {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {B : Finset (Finset (ZMod n))} (hB : B ∈ blocksC n) : B.card = 4 := by
  classical
  have h4 := H19_four_dvd hn ha
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hev : Even n := even_iff_two_dvd.mpr h2
  obtain ⟨hBb, hC⟩ := mem_filter.mp hB
  obtain ⟨k, hk, rfl⟩ := H19_mem_blocks hBb
  have hOmem : orbit 3 k ∈ blockOf (orbit 3 k) := by unfold blockOf; simp
  have hinvmem : inv (orbit 3 k) ∈ blockOf (orbit 3 k) := by unfold blockOf; simp
  have hnA : ¬ IsCaseA (orbit 3 k) := (hC _ hOmem).1
  have hnB : ¬ IsCaseB (orbit 3 k) := (hC _ hOmem).2
  have hnAi : ¬ IsCaseA (inv (orbit 3 k)) := (hC _ hinvmem).1
  have hne := H19_top_mem hn ha hodd h3 hk
  have d1 : orbit 3 k ≠ inv (orbit 3 k) := Ne.symm hne
  have d2 : orbit 3 k ≠ negO (orbit 3 k) := fun h => hnA h.symm
  have d3 : orbit 3 k ≠ negO (inv (orbit 3 k)) := by
    intro h
    have h' : inv (orbit 3 k) = inv (negO (inv (orbit 3 k))) := congrArg inv h
    rw [H19_negO_inv hev, H3_inv_inv] at h'
    exact hnB h'.symm
  have d4 : inv (orbit 3 k) ≠ negO (orbit 3 k) := fun h => hnB h.symm
  have d5 : inv (orbit 3 k) ≠ negO (inv (orbit 3 k)) := fun h => hnAi h.symm
  have d6 : negO (orbit 3 k) ≠ negO (inv (orbit 3 k)) := by
    intro h
    apply d1
    have h' := congrArg negO h
    rwa [H19_negO_negO hev, H19_negO_negO hev] at h'
  unfold blockOf
  rw [card_insert_of_notMem, card_insert_of_notMem, card_pair d6]
  all_goals simp only [mem_insert, mem_singleton, not_or]
  all_goals first | exact ⟨d4, d5⟩ | exact ⟨d1, d2, d3⟩

theorem H19_blocks_disj {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (h3 : ¬ 3 ∣ n) :
    ((blocks n : Set (Finset (Finset (ZMod n))))).PairwiseDisjoint (fun B => B.biUnion id) := by
  have h4 := H19_four_dvd hn ha
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hev : Even n := even_iff_two_dvd.mpr h2
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  intro B hB B' hB' hne
  show Disjoint (B.biUnion id) (B'.biUnion id)
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨O1, hO1, hx1⟩ := mem_biUnion.mp hx
  obtain ⟨O2, hO2, hx2⟩ := mem_biUnion.mp hx'
  obtain ⟨k, hk, rfl⟩ := H19_mem_blocks (mem_coe.mp hB)
  obtain ⟨k', hk', rfl⟩ := H19_mem_blocks (mem_coe.mp hB')
  obtain ⟨z1, -, rfl⟩ := H19_blockOf_mem hev h2 h4 hk hO1
  obtain ⟨z2, -, rfl⟩ := H19_blockOf_mem hev h2 h4 hk' hO2
  have heq : orbit 3 z1 = orbit 3 z2 := (H6_orbit_eq hcop hx1).symm.trans (H6_orbit_eq hcop hx2)
  apply hne
  rw [← H19_blockOf_closed hev _ _ hO1, ← H19_blockOf_closed hev _ _ hO2, heq]

theorem H19_sum_union_le {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (h3 : ¬ 3 ∣ n) :
    ∑ B ∈ blocks n, (B.biUnion id).card ≤ n / 2 := by
  have h4 := H19_four_dvd hn ha
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hev : Even n := even_iff_two_dvd.mpr h2
  rw [← card_biUnion (H19_blocks_disj hn ha h3), ← H6_card_topLayer h2]
  apply card_le_card
  intro x hx
  obtain ⟨B, hB, hxB⟩ := mem_biUnion.mp hx
  obtain ⟨O, hO, hxO⟩ := mem_biUnion.mp hxB
  obtain ⟨k, hk, rfl⟩ := H19_mem_blocks hB
  obtain ⟨z, hz, rfl⟩ := H19_blockOf_mem hev h2 h4 hk hO
  exact mem_filter.mpr ⟨mem_univ _, H7_orbit_odd h2 z hz x hxO⟩

theorem H19_AB_disj {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n) :
    Disjoint (blocksA n) (blocksB n) := by
  classical
  have h4 := H19_four_dvd hn ha
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hev : Even n := even_iff_two_dvd.mpr h2
  rw [Finset.disjoint_left]
  intro B hA hB
  obtain ⟨hBb, O1, hO1, hA1⟩ := mem_filter.mp hA
  obtain ⟨-, O2, hO2, hB2⟩ := mem_filter.mp hB
  obtain ⟨hBeq, -, z, hz, rfl⟩ := H19_card_AB hn ha hodd h3 hBb hO1 (Or.inl hA1)
  have hne := H19_top_mem hn ha hodd h3 hz
  have hA1' : negO (orbit 3 z) = orbit 3 z := hA1
  rw [hBeq] at hO2
  rcases mem_insert.mp hO2 with rfl | h
  · exact hne ((show negO (orbit 3 z) = inv (orbit 3 z) from hB2).symm.trans hA1')
  · rw [mem_singleton] at h
    subst h
    have hB2' : negO (inv (orbit 3 z)) = inv (inv (orbit 3 z)) := hB2
    rw [H19_negO_inv hev, hA1', H3_inv_inv] at hB2'
    exact hne hB2'

theorem H19_lenB_ge {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {B : Finset (Finset (ZMod n))} (hB : B ∈ blocksB n) : 1 ≤ blockLen B / 2 := by
  classical
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  obtain ⟨hBb, O', hO', hBO⟩ := mem_filter.mp hB
  obtain ⟨hBeq, hc2, z, hz, rfl⟩ := H19_card_AB hn ha hodd h3 hBb hO' (Or.inr hBO)
  have hne := H19_top_mem hn ha hodd h3 hz
  have hdisj : Disjoint (orbit 3 z) (inv (orbit 3 z)) := by
    rw [H6_inv_orbit] at hne ⊢
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact hne ((H6_orbit_eq hcop hx').symm.trans (H6_orbit_eq hcop hx))
  have hev := caseAB_even_proved n a nodd hn ha hodd h3 (orbit 3 z)
    (mem_image.mpr ⟨z, mem_filter.mpr ⟨mem_univ _, hz⟩, rfl⟩) (Or.inr hBO)
  have hpos : 0 < (orbit 3 z).card := card_pos.mpr ⟨z, H6_self_mem 3 z⟩
  unfold blockLen
  rw [hc2, hBeq]
  have hu : ({orbit 3 z, inv (orbit 3 z)} : Finset (Finset (ZMod n))).biUnion id = orbit 3 z ∪ inv (orbit 3 z) := by
    simp
  rw [hu, card_union_of_disjoint hdisj, H6_card_inv]
  obtain ⟨c, hc⟩ := hev
  omega

theorem H19_sum_le {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n) :
    ∑ B ∈ blocksA n, blockLen B / 2 + ∑ B ∈ blocksB n, blockLen B / 2 + ∑ B ∈ blocksC n, blockLen B ≤ n / 8 := by
  classical
  have hcA : ∀ B ∈ blocksA n, blockLen B / 2 = (B.biUnion id).card / 4 := by
    intro B hB
    obtain ⟨hBb, O, hO, hAO⟩ := mem_filter.mp hB
    have hc := (H19_card_AB hn ha hodd h3 hBb hO (Or.inl hAO)).2.1
    unfold blockLen; rw [hc, Nat.div_div_eq_div_mul]
  have hcB : ∀ B ∈ blocksB n, blockLen B / 2 = (B.biUnion id).card / 4 := by
    intro B hB
    obtain ⟨hBb, O, hO, hBO⟩ := mem_filter.mp hB
    have hc := (H19_card_AB hn ha hodd h3 hBb hO (Or.inr hBO)).2.1
    unfold blockLen; rw [hc, Nat.div_div_eq_div_mul]
  have hcC : ∀ B ∈ blocksC n, blockLen B = (B.biUnion id).card / 4 := by
    intro B hB
    unfold blockLen; rw [H19_card_C hn ha hodd h3 hB]
  have hAC : Disjoint (blocksA n) (blocksC n) := by
    rw [Finset.disjoint_left]
    intro B hA hC
    obtain ⟨-, O, hO, hAO⟩ := mem_filter.mp hA
    exact ((mem_filter.mp hC).2 O hO).1 hAO
  have hBC : Disjoint (blocksB n) (blocksC n) := by
    rw [Finset.disjoint_left]
    intro B hB hC
    obtain ⟨-, O, hO, hBO⟩ := mem_filter.mp hB
    exact ((mem_filter.mp hC).2 O hO).2 hBO
  rw [sum_congr rfl hcA, sum_congr rfl hcB, sum_congr rfl hcC, ← sum_union (H19_AB_disj hn ha hodd h3),
    ← sum_union (disjoint_union_left.mpr ⟨hAC, hBC⟩)]
  have hsub : (blocksA n ∪ blocksB n) ∪ blocksC n ⊆ blocks n :=
    union_subset (union_subset (filter_subset _ _) (filter_subset _ _)) (filter_subset _ _)
  have hdiv : ∑ B ∈ blocks n, (B.biUnion id).card / 4 ≤ (∑ B ∈ blocks n, (B.biUnion id).card) / 4 := by
    rw [Nat.le_div_iff_mul_le (by norm_num), sum_mul]
    exact sum_le_sum (fun B _ => Nat.div_mul_le_self _ 4)
  calc ∑ B ∈ (blocksA n ∪ blocksB n) ∪ blocksC n, (B.biUnion id).card / 4
      ≤ ∑ B ∈ blocks n, (B.biUnion id).card / 4 := sum_le_sum_of_subset hsub
    _ ≤ (∑ B ∈ blocks n, (B.biUnion id).card) / 4 := hdiv
    _ ≤ (n / 2) / 4 := Nat.div_le_div_right (H19_sum_union_le hn ha h3)
    _ = n / 8 := by rw [Nat.div_div_eq_div_mul]

theorem H19_bound {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n) :
    (16 * fibreProd n : ℝ) ≤ 16 * (4 / 3 : ℝ) ^ (blocksB n).card * 3 ^ (n / 8) := by
  have hA : ((∏ B ∈ blocksA n, (qO B - 1) : ℕ) : ℝ) ≤ ∏ B ∈ blocksA n, (3 : ℝ) ^ (blockLen B / 2) := by
    rw [Nat.cast_prod]
    apply prod_le_prod₀ (fun B _ => Nat.cast_nonneg _) (fun B _ => ?_)
    calc ((qO B - 1 : ℕ) : ℝ) ≤ (qO B : ℝ) := Nat.cast_le.mpr (Nat.sub_le _ _)
      _ = 3 ^ (blockLen B / 2) := by unfold qO; push_cast; rfl
  have hB : ((∏ B ∈ blocksB n, (qO B + 1) : ℕ) : ℝ) ≤ ∏ B ∈ blocksB n, ((4 / 3 : ℝ) * 3 ^ (blockLen B / 2)) := by
    rw [Nat.cast_prod]
    apply prod_le_prod₀ (fun B _ => Nat.cast_nonneg _) (fun B hB => ?_)
    have hL := H19_lenB_ge hn ha hodd h3 hB
    have h3le : (3 : ℝ) ≤ 3 ^ (blockLen B / 2) := by
      calc (3 : ℝ) = 3 ^ 1 := (pow_one 3).symm
        _ ≤ 3 ^ (blockLen B / 2) := pow_le_pow_right₀ (by norm_num) hL
    unfold qO; push_cast; linarith
  have hC : ((∏ B ∈ blocksC n, (3 ^ blockLen B - 1) : ℕ) : ℝ) ≤ ∏ B ∈ blocksC n, (3 : ℝ) ^ blockLen B := by
    rw [Nat.cast_prod]
    apply prod_le_prod₀ (fun B _ => Nat.cast_nonneg _) (fun B _ => ?_)
    calc ((3 ^ blockLen B - 1 : ℕ) : ℝ) ≤ ((3 ^ blockLen B : ℕ) : ℝ) := Nat.cast_le.mpr (Nat.sub_le _ _)
      _ = 3 ^ blockLen B := by push_cast; rfl
  have hS := H19_sum_le hn ha hodd h3
  have hpow : (3 : ℝ) ^ (∑ B ∈ blocksA n, blockLen B / 2 + ∑ B ∈ blocksB n, blockLen B / 2 +
      ∑ B ∈ blocksC n, blockLen B) ≤ 3 ^ (n / 8) := pow_le_pow_right₀ (by norm_num) hS
  unfold fibreProd
  rw [Nat.cast_mul, Nat.cast_mul]
  calc (16 : ℝ) * (((∏ B ∈ blocksA n, (qO B - 1) : ℕ) : ℝ) * ((∏ B ∈ blocksB n, (qO B + 1) : ℕ) : ℝ) *
        ((∏ B ∈ blocksC n, (3 ^ blockLen B - 1) : ℕ) : ℝ))
      ≤ 16 * ((∏ B ∈ blocksA n, (3 : ℝ) ^ (blockLen B / 2)) *
          (∏ B ∈ blocksB n, ((4 / 3 : ℝ) * 3 ^ (blockLen B / 2))) * ∏ B ∈ blocksC n, (3 : ℝ) ^ blockLen B) := by
        gcongr
    _ = 16 * (4 / 3 : ℝ) ^ (blocksB n).card * 3 ^ (∑ B ∈ blocksA n, blockLen B / 2 +
          ∑ B ∈ blocksB n, blockLen B / 2 + ∑ B ∈ blocksC n, blockLen B) := by
        rw [prod_mul_distrib, prod_const, prod_pow_eq_pow_sum, prod_pow_eq_pow_sum, prod_pow_eq_pow_sum,
          pow_add, pow_add]
        ring
    _ ≤ 16 * (4 / 3 : ℝ) ^ (blocksB n).card * 3 ^ (n / 8) := by gcongr

/-- `n = 2^{j+3}`, `j ≥ 1`: one block `{O, O^{-1}}`, of case A, with `q_O = q`. -/
theorem H19_pow2_blocks (j : ℕ) (hj : 1 ≤ j) :
    blocks (2 ^ (j + 3)) = {{orbit 3 1, inv (orbit 3 1)}} ∧ blocksA (2 ^ (j + 3)) = {{orbit 3 1, inv (orbit 3 1)}} ∧
      blocksB (2 ^ (j + 3)) = ∅ ∧ blocksC (2 ^ (j + 3)) = ∅ ∧
      qO ({orbit 3 1, inv (orbit 3 1)} : Finset (Finset (ZMod (2 ^ (j + 3))))) = qq (2 ^ (j + 3)) := by
  classical
  have h4 : 4 ∣ 2 ^ (j + 3) := ⟨2 ^ (j + 1), by ring⟩
  have h2 : 2 ∣ 2 ^ (j + 3) := dvd_trans (by norm_num) h4
  have hev : Even (2 ^ (j + 3)) := even_iff_two_dvd.mpr h2
  have h3 := H4_not3_of_pow2 (n := 2 ^ (j + 3)) (e := j + 3) rfl
  have hO := H3_topOrbits j
  have hB := thm_5_1_b_proved (2 ^ (j + 3)) (j + 3) 1 (by ring) (by omega) odd_one h3
  have hO1mem : orbit 3 (1 : ZMod (2 ^ (j + 3))) ∈ topOrbits (2 ^ (j + 3)) 3 := by
    rw [hO]; exact mem_insert_self _ _
  have hnegmem : negO (orbit 3 (1 : ZMod (2 ^ (j + 3)))) ∈ topOrbits (2 ^ (j + 3)) 3 := by
    rw [H19_negO_orbit hev]
    exact mem_image.mpr ⟨1 + half _, mem_filter.mpr ⟨mem_univ _, H19_odd_add_half h2 h4
      (by rw [ZMod.val_one'' (by have : 2 ^ 3 ≤ 2 ^ (j + 3) := Nat.pow_le_pow_right (by norm_num) (by omega); omega)];
          exact odd_one)⟩, rfl⟩
  have hA1 : negO (orbit 3 (1 : ZMod (2 ^ (j + 3)))) = orbit 3 1 := by
    rw [hO] at hnegmem
    rcases mem_insert.mp hnegmem with h | h
    · exact h
    · exact absurd (mem_singleton.mp h) ((hB _ hO1mem).1 (by omega))
  have hinvne : inv (orbit 3 (1 : ZMod (2 ^ (j + 3)))) ≠ orbit 3 1 := by
    intro h
    have hd := H3_disjoint j
    rw [h] at hd
    have h1 : (1 : ZMod (2 ^ (j + 3))) ∈ orbit 3 1 := H6_self_mem 3 1
    exact Finset.disjoint_left.mp hd h1 h1
  have hbl1 : blockOf (orbit 3 (1 : ZMod (2 ^ (j + 3)))) = {orbit 3 1, inv (orbit 3 1)} := by
    unfold blockOf
    rw [H19_negO_inv hev, hA1]
    ext x; simp only [mem_insert, mem_singleton]; tauto
  have hbl2 : blockOf (inv (orbit 3 (1 : ZMod (2 ^ (j + 3))))) = {orbit 3 1, inv (orbit 3 1)} := by
    unfold blockOf
    rw [H3_inv_inv, H19_negO_inv hev, hA1]
    ext x; simp only [mem_insert, mem_singleton]; tauto
  have hblocks : blocks (2 ^ (j + 3)) = {{orbit 3 1, inv (orbit 3 1)}} := by
    unfold blocks
    rw [hO, image_insert, image_singleton, hbl1, hbl2]
    exact insert_eq_of_mem (mem_singleton_self _)
  have hmem1 : orbit 3 (1 : ZMod (2 ^ (j + 3))) ∈
      ({orbit 3 1, inv (orbit 3 1)} : Finset (Finset (ZMod (2 ^ (j + 3))))) := mem_insert_self _ _
  have hnB : ∀ O ∈ ({orbit 3 1, inv (orbit 3 1)} : Finset (Finset (ZMod (2 ^ (j + 3))))), ¬ IsCaseB O := by
    intro O hOm hBO
    rcases mem_insert.mp hOm with rfl | h
    · exact hinvne ((show negO (orbit 3 (1 : ZMod (2 ^ (j + 3)))) = inv (orbit 3 1) from hBO).symm.trans hA1)
    · rw [mem_singleton] at h
      subst h
      have h' : negO (inv (orbit 3 (1 : ZMod (2 ^ (j + 3))))) = inv (inv (orbit 3 1)) := hBO
      rw [H19_negO_inv hev, hA1, H3_inv_inv] at h'
      exact hinvne h'
  refine ⟨hblocks, ?_, ?_, ?_, ?_⟩
  · unfold blocksA
    rw [hblocks]
    exact filter_true_of_mem (fun B hBm => by
      rw [mem_singleton] at hBm; subst hBm
      exact ⟨_, hmem1, hA1⟩)
  · unfold blocksB
    rw [hblocks]
    exact filter_false_of_mem (fun B hBm => by
      rw [mem_singleton] at hBm; subst hBm
      rintro ⟨O, hOm, hBO⟩
      exact hnB O hOm hBO)
  · unfold blocksC
    rw [hblocks]
    exact filter_false_of_mem (fun B hBm => by
      rw [mem_singleton] at hBm; subst hBm
      intro hall
      exact (hall _ hmem1).1 hA1)
  · have hcardO1 : (orbit 3 (1 : ZMod (2 ^ (j + 3)))).card = 2 ^ (j + 1) := H3_orbit_one_card j
    have hu : ({orbit 3 1, inv (orbit 3 1)} : Finset (Finset (ZMod (2 ^ (j + 3))))).biUnion id =
        orbit 3 1 ∪ inv (orbit 3 1) := by simp
    have hcu : (orbit 3 (1 : ZMod (2 ^ (j + 3))) ∪ inv (orbit 3 1)).card = 2 * 2 ^ (j + 1) := by
      rw [card_union_of_disjoint (H3_disjoint j), H3_inv_card, hcardO1]; ring
    have hc2 : ({orbit 3 1, inv (orbit 3 1)} : Finset (Finset (ZMod (2 ^ (j + 3))))).card = 2 :=
      card_pair (Ne.symm hinvne)
    unfold qO blockLen qq
    rw [hu, hcu, hc2, Nat.mul_div_cancel_left _ (by norm_num)]
    congr 1
    rw [show 2 ^ (j + 3) = 2 ^ j * 8 by ring, Nat.mul_div_cancel _ (by norm_num), pow_succ,
      Nat.mul_div_cancel _ (by norm_num)]

end Blocks

/-! ## Part G — Corollary 5.2: at most 4 solutions of Xia's system in a fibre, one orbit of `⟨T, v ↦ -v⟩` -/

section Cor52

variable {n : ℕ} [NeZero n]

theorem H19_sgn_map {F G : Type*} [CommRing F] [CommRing G] (φ : F →+* G) (t : ZMod n) :
    φ (sgn t) = sgn t := by
  unfold sgn; rw [map_pow, map_neg, map_one]

theorem H19_S_map {F G : Type*} [CommRing F] [CommRing G] (φ : F →+* G) (y : ZMod n → F) :
    φ (S y) = S (fun t => φ (y t)) := by
  unfold S; rw [map_sum]
  refine sum_congr rfl (fun t _ => ?_)
  rw [map_mul, H19_sgn_map]

theorem H19_xia_map {F : Type*} [CommRing F] (φ : F →+* F) {σ : ℤ} {y : ZMod n → F} (hy : XiaEqs σ y) :
    XiaEqs σ (fun t => φ (y t)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hy
  refine ⟨fun s => ?_, fun s hs => ?_, fun s hs => ?_, fun s hs => ?_⟩
  · show φ (y (s + σ)) = φ (y s) ^ 3
    rw [h1 s, map_pow]
  · show φ (y s) * φ (y (s + half n)) = -1
    rw [← map_mul, h2 s hs, map_neg, map_one]
  · show ∑ t, φ (y t) * φ (y (s + t)) = 0
    rw [← map_zero φ, ← h3 s hs, map_sum]
    simp only [map_mul]
  · show ∑ t, sgn t * φ (y t) * φ (y (2 * s - t)) = (φ (y s) + φ (y (s + half n))) * S (fun t => φ (y t))
    rw [← H19_S_map, ← map_add, ← map_mul, ← h4 s hs, map_sum]
    refine sum_congr rfl (fun t _ => ?_)
    rw [map_mul, map_mul, H19_sgn_map]

theorem H19_xia_trans (h4 : 4 ∣ n) {y : ZMod n → GaloisField 3 (n / 2)} (hy : y ∈ XiaSet n 2) :
    yTrans (half n) y ∈ XiaSet n 2 := by
  have hL1 : L1 3 ((2 : ℕ) : ℤ) y := hy.1
  have heq : yTrans (half n) y = fun t => (iterateFrobenius (GaloisField 3 (n / 2)) 3 (n / 4)) (y t) := by
    funext t
    show y (t + half n) = (y t) ^ (3 ^ (n / 4))
    exact (H19_bar_shift h4 hL1 t).symm
  rw [heq]
  exact H19_xia_map _ hy

theorem H19_xia_subst (h4 : 4 ∣ n) {y : ZMod n → GaloisField 3 (n / 2)} (hy : y ∈ XiaSet n 2) :
    ySubst y ∈ XiaSet n 2 := by
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  obtain ⟨hL1, hL2, hL3, hL4⟩ := hy
  exact ⟨H6_L1_subst (H6_u_two h2) hL1, H6_L2_subst h2 h4 hL2, H6_L3_subst h2 h4 hL3, H6_L4_subst h2 h4 hL4⟩

theorem H19_nf_subst (h4 : 4 ∣ n) {y : ZMod n → GaloisField 3 (n / 2)} (hy : y ∈ NFSet n 2) :
    ySubst y ∈ NFSet n 2 := by
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  obtain ⟨hL1, hL3, hR, hL4⟩ := hy
  refine ⟨H6_L1_subst (H6_u_two h2) hL1, H6_L3_subst h2 h4 hL3, ?_, H6_L4_subst h2 h4 hL4⟩
  rw [H6_R_subst h2 h4, H6_u_half h2 h4]; exact hR

variable {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L]

theorem H19_dftA_trans (hev : Even n) {ω : L} (hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2))
    (k : ZMod n) : dftA ω (yTrans (half n) y) k = (-1) ^ k.val * dftA ω y k := by
  unfold dftA dft
  have hX : (ω ^ k.val) ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  have hε : (ω ^ k.val) ^ (half n).val = (-1) ^ k.val := by
    rw [H6_half_val, ← pow_mul, mul_comm, pow_mul, H7_pow_half_eq_neg_one hev hω]
  have hsq : ((-1 : L) ^ k.val) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight (half n)) _ _ (fun t => ?_)
  simp only [Equiv.coe_addRight, yTrans]
  rw [H7_pow_val_add _ hX, hε]
  linear_combination (-(algebraMap _ L (y (t + half n)) * (ω ^ k.val) ^ t.val)) * hsq

theorem H19_dftA_ne_zero (hev : Even n) {ω : L} (hω : IsPrimitiveRoot ω n) {z : ZMod n → GaloisField 3 (n / 2)}
    (hz : z ∈ NFSet n 2) (k : ZMod n) : dftA ω z k ≠ 0 := by
  obtain ⟨-, hL3, hRm, -⟩ := hz
  have hL3' : L3 0 (fun t => algebraMap _ L (z t)) := fun s hs => by
    show ∑ t, algebraMap _ L (z t) * algebraMap _ L (z (s + t)) = 0
    rw [← map_zero (algebraMap (GaloisField 3 (n / 2)) L), ← hL3 s hs, map_sum]
    simp only [map_mul]
  have hRm' : R (fun t => algebraMap _ L (z t)) (half n) = 1 := by
    unfold R at hRm ⊢
    rw [← map_one (algebraMap (GaloisField 3 (n / 2)) L), ← hRm, map_sum]
    simp only [map_mul]
  exact H5_F3_ne (hω.ne_zero (NeZero.ne n)) _
    (fun j => H4_F3_of_R hev hω.pow_eq_one _ (H4_R_of_NF hev _ hL3' hRm') j) k

theorem H19_match (h4 : 4 ∣ n) (h3 : ¬ 3 ∣ n)
    (hFI : ∀ (ω' : L), IsPrimitiveRoot ω' n → (n : L) ≠ 0 → ∀ y : ZMod n → L,
      (∀ t : ZMod n, y t = (n : L)⁻¹ * ∑ k : ZMod n, dft ω' y k * ((ω' ^ k.val)⁻¹) ^ t.val) ∧
        dft ω' y (half n) = S y)
    {ω : L} (hω : IsPrimitiveRoot ω n) {z y'' : ZMod n → GaloisField 3 (n / 2)}
    (hz1 : L1 3 ((2 : ℕ) : ℤ) z) (hy1 : L1 3 ((2 : ℕ) : ℤ) y'')
    (hD : ∀ k : ZMod n, Even k.val → dftA ω z k = dftA ω y'' k)
    (h0 : yMinus n (z 0) = yMinus n (y'' 0)) (h1 : yMinus n (z 1) = yMinus n (y'' 1)) : z = y'' := by
  have hc := H19_d_core h4 h3 hFI hω hz1 hy1 hD
  have e0 := (H19_yMinus_diff h4 h3 hFI hω hz1 hy1 hD 0).1
  have e1 := (H19_yMinus_diff h4 h3 hFI hω hz1 hy1 hD 1).1
  have hp := hc.1.mp (by rw [← e0, h0, sub_self])
  have hm := hc.2.mp (by rw [← e1, h1, sub_self])
  have h2L := H19_two_ne_zero n (L := L)
  have hall : ∀ k, dftA ω z k = dftA ω y'' k := by
    intro k
    rcases Nat.even_or_odd k.val with hk | hk
    · exact hD k hk
    · have h2 : (2 : L) * (dftA ω z k - dftA ω y'' k) = 0 := by linear_combination hp k hk + hm k hk
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left h2L)
  funext t
  have hnL := H19_natCast_ne_zero n (L := L) h3
  have e := H19_alg_delta hFI hω hnL z y'' t
  unfold H19_A at e
  simp only [hall, sub_self, zero_mul, sum_const_zero, mul_zero] at e
  exact sub_eq_zero.mp ((algebraMap (GaloisField 3 (n / 2)) L).injective (by rw [e, map_zero]))

theorem H19_cor_part1 (hn : n % 24 = 8) (ω : L) (hω : IsPrimitiveRoot ω n)
    (hFI : ∀ (ω' : L), IsPrimitiveRoot ω' n → (n : L) ≠ 0 → ∀ y : ZMod n → L,
      (∀ t : ZMod n, y t = (n : L)⁻¹ * ∑ k : ZMod n, dft ω' y k * ((ω' ^ k.val)⁻¹) ^ t.val) ∧
        dft ω' y (half n) = S y)
    (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2) :
    (fibre ω y ∩ XiaSet n 2).ncard ∈ ({0, 2, 4} : Set ℕ) ∧
      ∀ y' ∈ fibre ω y ∩ XiaSet n 2,
        fibre ω y ∩ XiaSet n 2 = ({y', ySubst y', yTrans (half n) y', ySubst (yTrans (half n) y')} : Set _) := by
  have h8 : 8 ∣ n := by omega
  have h4 : 4 ∣ n := dvd_trans (by norm_num) h8
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hev : Even n := even_iff_two_dvd.mpr h2
  have h3 : ¬ 3 ∣ n := by omega
  have hsubNF : XiaSet n 2 ⊆ NFSet n 2 := xia_sub_nf_proved n hn 2 h2
  have hyf : y ∈ fibre ω y := ⟨hy, fun _ _ => rfl⟩
  have h2F := H3_two_ne_zero (n / 2)
  have hzero : ∀ x : GaloisField 3 (n / 2), x = -x → x = 0 := by
    intro x hx
    have : (2 : GaloisField 3 (n / 2)) * x = 0 := by linear_combination hx
    exact (mul_eq_zero.mp this).resolve_left h2F
  -- closure under `T = ySubst` and `v ↦ -v` (`= yTrans (half n)`)
  have hT : ∀ z ∈ fibre ω y ∩ XiaSet n 2, ySubst z ∈ fibre ω y ∩ XiaSet n 2 := by
    rintro z ⟨⟨hzN, hzf⟩, hzX⟩
    refine ⟨⟨H19_nf_subst h4 hzN, fun k hk => ?_⟩, H19_xia_subst h4 hzX⟩
    rw [H6_dftA_subst h2 h4 hω.pow_eq_one, H6_u_even h2 hk, hzf k hk]
  have hBar : ∀ z ∈ fibre ω y ∩ XiaSet n 2, yTrans (half n) z ∈ fibre ω y ∩ XiaSet n 2 := by
    rintro z ⟨⟨-, hzf⟩, hzX⟩
    have hX := H19_xia_trans h4 hzX
    refine ⟨⟨hsubNF hX, fun k hk => ?_⟩, hX⟩
    rw [H19_dftA_trans hev hω, hk.neg_one_pow, one_mul, hzf k hk]
  have hL1 : ∀ z ∈ fibre ω y ∩ XiaSet n 2, L1 3 ((2 : ℕ) : ℤ) z := fun z hz => hz.2.1
  -- signatures `(y^-_0, y^-_1)`
  have hyMbar : ∀ x : GaloisField 3 (n / 2), yMinus n (bar n x) = -yMinus n x := by
    intro x
    unfold yMinus
    rw [(sec_2_2_norm_proved n h4 x).2.2]
    ring
  have hs0T : ∀ z : ZMod n → GaloisField 3 (n / 2), yMinus n (ySubst z 0) = yMinus n (z 0) := by
    intro z
    show yMinus n (z ((1 + half n) * 0)) = _
    rw [mul_zero]
  have hs1T : ∀ z ∈ fibre ω y ∩ XiaSet n 2, yMinus n (ySubst z 1) = -yMinus n (z 1) := by
    intro z hz
    rw [H6_subst_one h4 (hL1 z hz), hyMbar]
  have hsB : ∀ z ∈ fibre ω y ∩ XiaSet n 2, ∀ t : ZMod n, yMinus n (yTrans (half n) z t) = -yMinus n (z t) := by
    intro z hz t
    show yMinus n (z (t + half n)) = _
    rw [← H19_bar_shift h4 (hL1 z hz), hyMbar]
  have hmatch : ∀ z1 ∈ fibre ω y ∩ XiaSet n 2, ∀ z2 ∈ fibre ω y ∩ XiaSet n 2,
      yMinus n (z1 0) = yMinus n (z2 0) → yMinus n (z1 1) = yMinus n (z2 1) → z1 = z2 := by
    intro z1 hz1 z2 hz2 e0 e1
    have hD : ∀ k : ZMod n, Even k.val → dftA ω z1 k = dftA ω z2 k := fun k hk => by
      rw [hz1.1.2 k hk, hz2.1.2 k hk]
    exact H19_match h4 h3 hFI hω (hL1 z1 hz1) (hL1 z2 hz2) hD e0 e1
  have hsq : ∀ z ∈ fibre ω y ∩ XiaSet n 2, ∀ t : ZMod n, (t = 0 ∨ t = 1) →
      yMinus n (z t) ^ 2 = yPlus n (y t) ^ 2 + 1 := by
    intro z hz t ht
    have hN := (sec_2_2_L2_iff_proved n hn z (hL1 z hz)).mp hz.2.2.1
    have hNt : Nm n (z t) = -1 := by rcases ht with rfl | rfl; exacts [hN.1, hN.2]
    have hD : ∀ k : ZMod n, Even k.val → dftA ω z k = dftA ω y k := fun k hk => hz.1.2 k hk
    have hp := (H19_yMinus_diff h4 h3 hFI hω (hL1 z hz) hy.1 hD t).2
    rw [H19_norm_split n h4, hp] at hNt
    linear_combination -hNt
  have hpm : ∀ z1 ∈ fibre ω y ∩ XiaSet n 2, ∀ z2 ∈ fibre ω y ∩ XiaSet n 2, ∀ t : ZMod n, (t = 0 ∨ t = 1) →
      yMinus n (z1 t) = yMinus n (z2 t) ∨ yMinus n (z1 t) = -yMinus n (z2 t) := by
    intro z1 hz1 z2 hz2 t ht
    exact sq_eq_sq_iff_eq_or_eq_neg.mp (by rw [hsq z1 hz1 t ht, hsq z2 hz2 t ht])
  have hBne : ∀ z ∈ fibre ω y ∩ XiaSet n 2, yTrans (half n) z ≠ z := by
    intro z hz heq
    have h1v : (1 : ZMod n).val = 1 := ZMod.val_one'' (by omega)
    have e := H19_dftA_trans hev hω z 1
    rw [heq, h1v, pow_one, neg_one_mul] at e
    have h2L := H19_two_ne_zero n (L := L)
    have h0 : (2 : L) * dftA ω z 1 = 0 := by linear_combination e
    exact H19_dftA_ne_zero hev hω (hsubNF hz.2) 1 ((mul_eq_zero.mp h0).resolve_left h2L)
  have horb : ∀ y' ∈ fibre ω y ∩ XiaSet n 2,
      fibre ω y ∩ XiaSet n 2 = ({y', ySubst y', yTrans (half n) y', ySubst (yTrans (half n) y')} : Set _) := by
    intro y' hy'
    have hB' := hBar y' hy'
    ext y''
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hy''
      rcases hpm y'' hy'' y' hy' 0 (Or.inl rfl) with e0 | e0 <;>
        rcases hpm y'' hy'' y' hy' 1 (Or.inr rfl) with e1 | e1
      · exact Or.inl (hmatch _ hy'' _ hy' e0 e1)
      · exact Or.inr (Or.inl (hmatch _ hy'' _ (hT _ hy') (by rw [hs0T, e0]) (by rw [hs1T _ hy', e1])))
      · exact Or.inr (Or.inr (Or.inr (hmatch _ hy'' _ (hT _ hB') (by rw [hs0T, hsB _ hy', e0])
          (by rw [hs1T _ hB', hsB _ hy', neg_neg, e1]))))
      · exact Or.inr (Or.inr (Or.inl (hmatch _ hy'' _ hB' (by rw [hsB _ hy', e0]) (by rw [hsB _ hy', e1]))))
    · rintro (rfl | rfl | rfl | rfl)
      exacts [hy', hT _ hy', hB', hT _ hB']
  refine ⟨?_, horb⟩
  rcases (fibre ω y ∩ XiaSet n 2).eq_empty_or_nonempty with hE | ⟨y', hy'⟩
  · rw [hE, Set.ncard_empty]; simp
  rw [horb y' hy']
  have hB' := hBar y' hy'
  have hT' := hT y' hy'
  have hTB := hT _ hB'
  have hne0 : ∀ z1 z2 : ZMod n → GaloisField 3 (n / 2), yMinus n (z1 0) ≠ yMinus n (z2 0) → z1 ≠ z2 :=
    fun z1 z2 h e => h (by rw [e])
  have hne1 : ∀ z1 z2 : ZMod n → GaloisField 3 (n / 2), yMinus n (z1 1) ≠ yMinus n (z2 1) → z1 ≠ z2 :=
    fun z1 z2 h e => h (by rw [e])
  have hnot00 : ¬ (yMinus n (y' 0) = 0 ∧ yMinus n (y' 1) = 0) := by
    rintro ⟨a0, a1⟩
    exact hBne y' hy' (hmatch _ hB' _ hy' (by rw [hsB _ hy', a0, neg_zero]) (by rw [hsB _ hy', a1, neg_zero]))
  have hnz : ∀ x : GaloisField 3 (n / 2), x ≠ 0 → x ≠ -x := fun x hx h => hx (hzero x h)
  by_cases h0 : yMinus n (y' 0) = 0
  · have h1 : yMinus n (y' 1) ≠ 0 := fun h1 => hnot00 ⟨h0, h1⟩
    have eTB : ySubst (yTrans (half n) y') = y' :=
      hmatch _ hTB _ hy' (by rw [hs0T, hsB _ hy', h0, neg_zero]) (by rw [hs1T _ hB', hsB _ hy', neg_neg])
    have eB : yTrans (half n) y' = ySubst y' :=
      hmatch _ hB' _ hT' (by rw [hsB _ hy', hs0T, h0, neg_zero]) (by rw [hsB _ hy', hs1T _ hy'])
    have hneq : y' ≠ ySubst y' := hne1 _ _ (by rw [hs1T _ hy']; exact hnz _ h1)
    rw [eTB, eB]
    have hset : ({y', ySubst y', ySubst y', y'} : Set (ZMod n → GaloisField 3 (n / 2))) = {y', ySubst y'} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset, Set.ncard_pair hneq]; simp
  · by_cases h1 : yMinus n (y' 1) = 0
    · have eT : ySubst y' = y' := hmatch _ hT' _ hy' (by rw [hs0T]) (by rw [hs1T _ hy', h1, neg_zero])
      have eTB : ySubst (yTrans (half n) y') = yTrans (half n) y' :=
        hmatch _ hTB _ hB' (by rw [hs0T]) (by rw [hs1T _ hB', hsB _ hy', h1, neg_zero, neg_zero])
      have hneq : y' ≠ yTrans (half n) y' := hne0 _ _ (by rw [hsB _ hy']; exact hnz _ h0)
      rw [eTB, eT]
      have hset : ({y', y', yTrans (half n) y', yTrans (half n) y'} : Set (ZMod n → GaloisField 3 (n / 2))) =
          {y', yTrans (half n) y'} := by
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rw [hset, Set.ncard_pair hneq]; simp
    · have hab : y' ≠ ySubst y' := hne1 _ _ (by rw [hs1T _ hy']; exact hnz _ h1)
      have hac : y' ≠ yTrans (half n) y' := hne0 _ _ (by rw [hsB _ hy']; exact hnz _ h0)
      have had : y' ≠ ySubst (yTrans (half n) y') := hne0 _ _ (by rw [hs0T, hsB _ hy']; exact hnz _ h0)
      have hbc : ySubst y' ≠ yTrans (half n) y' := hne0 _ _ (by rw [hs0T, hsB _ hy']; exact hnz _ h0)
      have hbd : ySubst y' ≠ ySubst (yTrans (half n) y') :=
        hne0 _ _ (by rw [hs0T, hs0T, hsB _ hy']; exact hnz _ h0)
      have hcd : yTrans (half n) y' ≠ ySubst (yTrans (half n) y') :=
        hne1 _ _ (by rw [hs1T _ hB', hsB _ hy', neg_neg]; exact (hnz _ h1).symm)
      rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hcd]
      · simp
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]; exact ⟨hbc, hbd⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]; exact ⟨hab, hac, had⟩

end Cor52

/-- `n ≡ 8 (mod 24)` gives `n = 2^a n_odd` with `a ≥ 3`, `n_odd` odd, `3 ∤ n`. -/
theorem H19_decomp (n : ℕ) (hn : n % 24 = 8) : ∃ a nodd : ℕ, n = 2 ^ a * nodd ∧ 3 ≤ a ∧ Odd nodd ∧ ¬ 3 ∣ n := by
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (show n ≠ 0 by omega)
  refine ⟨a, m, hnm, ?_, hm, by omega⟩
  by_contra hlt
  push Not at hlt
  have h8 : 8 ∣ 2 ^ a * m := by rw [← hnm]; omega
  have hcop : Nat.Coprime 8 m := (Nat.coprime_two_left.mpr hm).pow_left 3
  have h8a : 8 ∣ 2 ^ a := hcop.dvd_of_dvd_mul_right h8
  have : 2 ^ a ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := Nat.le_of_dvd (by positivity) h8a
  omega

theorem cor_5_2_of (n : ℕ) [NeZero n] (hn : n % 24 = 8) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L]
    (ω : L) (hω : IsPrimitiveRoot ω n)
    (hFI : ∀ (ω' : L), IsPrimitiveRoot ω' n → (n : L) ≠ 0 → ∀ y : ZMod n → L,
      (∀ t : ZMod n, y t = (n : L)⁻¹ * ∑ k : ZMod n, dft ω' y k * ((ω' ^ k.val)⁻¹) ^ t.val) ∧
        dft ω' y (half n) = S y)
    (hcount : ∀ (a nodd : ℕ), n = 2 ^ a * nodd → 3 ≤ a → Odd nodd → ¬ 3 ∣ n →
      (∀ y ∈ NFSet n 2, Nat.card (fibre ω y) = fibreSize n) ∧
        Nat.card (lowerData ω '' NFSet n 2) = 4 * fibreProd n ∧
        Nat.card (NFSet n 2) = fibreSize n * (4 * fibreProd n)) :
    (∀ y ∈ NFSet n 2, (fibre ω y ∩ XiaSet n 2).ncard ∈ ({0, 2, 4} : Set ℕ) ∧
      ∀ y' ∈ fibre ω y ∩ XiaSet n 2,
        fibre ω y ∩ XiaSet n 2 = ({y', ySubst y', yTrans (half n) y', ySubst (yTrans (half n) y')} : Set _)) ∧
      Nat.card (XiaSet n 2) ≤ 16 * fibreProd n ∧
      (16 * fibreProd n : ℝ) ≤ 16 * (4 / 3 : ℝ) ^ (blocksB n).card * 3 ^ (n / 8) := by
  classical
  obtain ⟨a, nodd, hna, ha, hodd, h3⟩ := H19_decomp n hn
  have h2 : 2 ∣ n := by omega
  have hsubNF : XiaSet n 2 ⊆ NFSet n 2 := xia_sub_nf_proved n hn 2 h2
  have hpart1 := fun y hy => H19_cor_part1 hn ω hω hFI y hy
  refine ⟨hpart1, ?_, H19_bound hna ha hodd h3⟩
  let : Fintype (GaloisField 3 (n / 2)) := Fintype.ofFinite _
  set s : Finset (ZMod n → GaloisField 3 (n / 2)) := univ.filter (fun x => x ∈ XiaSet n 2) with hsdef
  set t : Finset (ZMod n → GaloisField 3 (n / 2)) := univ.filter (fun x => x ∈ NFSet n 2) with htdef
  have hs : (s : Set (ZMod n → GaloisField 3 (n / 2))) = XiaSet n 2 := by ext x; simp [hsdef]
  have ht : (t : Set (ZMod n → GaloisField 3 (n / 2))) = NFSet n 2 := by ext x; simp [htdef]
  have hXc : Nat.card (XiaSet n 2) = s.card := by
    rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset, hs]
  have hVc : Nat.card (lowerData ω '' NFSet n 2) = (t.image (lowerData ω)).card := by
    rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset, coe_image, ht]
  have hld : ∀ x x' : ZMod n → GaloisField 3 (n / 2),
      lowerData ω x = lowerData ω x' ↔ ∀ k : ZMod n, Even k.val → dftA ω x k = dftA ω x' k := by
    intro x x'
    constructor
    · intro h k hk; exact congrFun h ⟨k, hk⟩
    · intro h; funext k; exact h k.1 k.2
  have hfib4 : ∀ v ∈ s.image (lowerData ω), (s.filter (fun x => lowerData ω x = v)).card ≤ 4 := by
    intro v hv
    obtain ⟨y0, hy0, rfl⟩ := mem_image.mp hv
    have hy0X : y0 ∈ XiaSet n 2 := (mem_filter.mp hy0).2
    have hset : ((s.filter (fun x => lowerData ω x = lowerData ω y0)) : Set (ZMod n → GaloisField 3 (n / 2))) =
        fibre ω y0 ∩ XiaSet n 2 := by
      ext x
      simp only [coe_filter, hsdef, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq, Set.mem_inter_iff]
      rw [hld]
      constructor
      · rintro ⟨hx, hl⟩; exact ⟨⟨hsubNF hx, hl⟩, hx⟩
      · rintro ⟨⟨-, hl⟩, hx⟩; exact ⟨hx, hl⟩
    rw [← Set.ncard_coe_finset, hset]
    have h := (hpart1 y0 (hsubNF hy0X)).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    omega
  have himg : s.image (lowerData ω) ⊆ t.image (lowerData ω) :=
    image_subset_image (fun x hx => mem_filter.mpr ⟨mem_univ _, hsubNF (mem_filter.mp hx).2⟩)
  have hV := (hcount a nodd hna ha hodd h3).2.1
  calc Nat.card (XiaSet n 2) = s.card := hXc
    _ ≤ 4 * (s.image (lowerData ω)).card := card_le_mul_card_image s 4 hfib4
    _ ≤ 4 * (t.image (lowerData ω)).card := Nat.mul_le_mul_left 4 (card_le_card himg)
    _ = 4 * (4 * fibreProd n) := by rw [← hVc, hV]
    _ = 16 * fibreProd n := by ring

theorem thm_B_part_of (n : ℕ) [NeZero n] (hn : n % 24 = 8) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L]
    (ω : L) (hω : IsPrimitiveRoot ω n)
    (hFI : ∀ (ω' : L), IsPrimitiveRoot ω' n → (n : L) ≠ 0 → ∀ y : ZMod n → L,
      (∀ t : ZMod n, y t = (n : L)⁻¹ * ∑ k : ZMod n, dft ω' y k * ((ω' ^ k.val)⁻¹) ^ t.val) ∧
        dft ω' y (half n) = S y)
    (hcount : ∀ (a nodd : ℕ), n = 2 ^ a * nodd → 3 ≤ a → Odd nodd → ¬ 3 ∣ n →
      (∀ y ∈ NFSet n 2, Nat.card (fibre ω y) = fibreSize n) ∧
        Nat.card (lowerData ω '' NFSet n 2) = 4 * fibreProd n ∧
        Nat.card (NFSet n 2) = fibreSize n * (4 * fibreProd n))
    (hcount41 : ∀ (a nodd : ℕ), n = 2 ^ a * nodd → 3 ≤ a → Odd nodd → ¬ 3 ∣ n →
      Nat.card (NFSet n 2) = 4 * pairProd n 3 ∧ (NFSet n 2).Nonempty ∧
        (Nat.card (NFSet n 2) : ℚ) = 4 * 3 ^ (n / 4) * ∏ P ∈ topPairs n 3, (1 - (3 : ℚ) ^ (-(pairLen P : ℤ)))) :
    (∀ y ∈ NFSet n 2, ySubst y ∈ NFSet n 2 ∧ ySubst (ySubst y) = y) ∧
      (16 ∣ n → (blocksB n).card = 0) ∧
      (∀ y ∈ NFSet n 2, (fibre ω y ∩ XiaSet n 2).ncard ≤ 4) ∧
      Nat.card (XiaSet n 2) ≤ 16 * fibreProd n ∧
      (16 * fibreProd n : ℝ) ≤ 16 * (4 / 3 : ℝ) ^ (blocksB n).card * 3 ^ (n / 8) ∧
      ∀ e : ℕ, n = 2 ^ e → 5 ≤ e → 16 * fibreProd n = 16 * (3 ^ (n / 8) - 1) ∧
        Nat.card (NFSet n 2) = 4 * (3 ^ (n / 4) - 1) := by
  classical
  obtain ⟨a, nodd, hna, ha, hodd, h3⟩ := H19_decomp n hn
  have h4 := H19_four_dvd hna ha
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hev : Even n := even_iff_two_dvd.mpr h2
  have hcor := cor_5_2_of n hn ω hω hFI hcount
  refine ⟨fun y hy => ⟨H19_nf_subst h4 hy, H6_subst_subst h2 h4 y⟩, fun h16 => ?_, fun y hy => ?_, hcor.2.1,
    hcor.2.2, fun e hne he => ?_⟩
  · have ha4 : 4 ≤ a := by
      by_contra hlt
      push Not at hlt
      have hcop : Nat.Coprime 16 nodd := (Nat.coprime_two_left.mpr hodd).pow_left 4
      have h16a : 16 ∣ 2 ^ a := hcop.dvd_of_dvd_mul_right (hna ▸ h16)
      have : 2 ^ a ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have := Nat.le_of_dvd (by positivity) h16a
      omega
    rw [card_eq_zero]
    unfold blocksB
    rw [filter_eq_empty_iff]
    intro B hB hBO
    obtain ⟨O, hO, hBO⟩ := hBO
    obtain ⟨k, hk, rfl⟩ := H19_mem_blocks hB
    obtain ⟨z, hz, rfl⟩ := H19_blockOf_mem hev h2 h4 hk hO
    exact (thm_5_1_b_proved n a nodd hna ha hodd h3 _ (mem_image.mpr ⟨z, mem_filter.mpr ⟨mem_univ _, hz⟩, rfl⟩)).1
      ha4 hBO
  · have h := (hcor.1 y hy).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    omega
  · obtain ⟨j, rfl⟩ : ∃ j, e = j + 3 := ⟨e - 3, by omega⟩
    subst hne
    obtain ⟨-, hbA, hbB, hbC, hq⟩ := H19_pow2_blocks j (by omega)
    have hNF := (hcount41 (j + 3) 1 (by ring) (by omega) odd_one h3).1
    obtain ⟨hP1, hPlen⟩ := thm_4_1_pow2_proved (2 ^ (j + 3)) (j + 3) rfl (by omega)
    obtain ⟨P, hP⟩ := card_eq_one.mp hP1
    refine ⟨?_, ?_⟩
    · unfold fibreProd
      rw [hbA, hbB, hbC, prod_singleton, prod_empty, prod_empty, hq]
      unfold qq
      ring
    · rw [hNF]
      unfold pairProd
      rw [hP, prod_singleton, hPlen P (by rw [hP]; exact mem_singleton_self _)]

/-! ## Glue for the link lines -/

theorem H19_even_of {n a nodd : ℕ} [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) : Even n :=
  even_iff_two_dvd.mpr (dvd_trans (by norm_num) (H19_four_dvd hn ha))

theorem H19_even_of24 {n : ℕ} (hn : n % 24 = 8) : Even n := Nat.even_iff.mpr (by omega)

end Xia.Proofs

#print axioms Xia.Proofs.sec_5_setup_of
#print axioms Xia.Proofs.thm_5_1_c_yform_of
#print axioms Xia.Proofs.thm_5_1_d_yform_of
#print axioms Xia.Proofs.fig1_caption_of
#print axioms Xia.Proofs.cor_5_2_of
#print axioms Xia.Proofs.thm_B_part_of
