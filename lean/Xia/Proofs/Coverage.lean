/- Xia/Proofs/Coverage.lean — proofs of the rows sec_2_2_norm, sec_3_2_V_card, thm_6_2_sets, caseAB_even, fibre_not_linear, intro_planar_2_8 and 3 more of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry

namespace Xia.Proofs

open Xia Finset

/-! ## Generic helpers on `ℤ/n` and roots of unity -/

/-- Powers of an `x` with `x^n = 1` along `ZMod n` are additive in the exponent. -/
theorem H7_pow_val_add {n : ℕ} [NeZero n] {M : Type*} [Monoid M] (x : M) (hx : x ^ n = 1)
    (a b : ZMod n) : x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hx, pow_add]

/-- `(n/2 : ZMod n).val = n/2`. -/
theorem H7_half_val {n : ℕ} [NeZero n] : (half n : ZMod n).val = n / 2 := by
  unfold half
  rw [ZMod.val_natCast]
  have := NeZero.pos n
  exact Nat.mod_eq_of_lt (by omega)

/-- For even `n`: `m + m = 0` in `ZMod n`. -/
theorem H7_two_half {n : ℕ} [NeZero n] (hn : Even n) : half n + half n = (0 : ZMod n) := by
  unfold half
  rw [← Nat.cast_add]
  have h2 : n % 2 = 0 := Nat.even_iff.mp hn
  have : n / 2 + n / 2 = n := by omega
  rw [this, ZMod.natCast_self]

/-- For even `n` and odd `r`: `r · (n/2) = n/2` in `ZMod n`. -/
theorem H7_odd_mul_half {n : ℕ} [NeZero n] (hn : Even n) (r : ℕ) (hr : Odd r) :
    (r : ZMod n) * half n = half n := by
  obtain ⟨k, rfl⟩ := hr
  have h2 : (2 : ZMod n) * half n = 0 := by rw [two_mul, H7_two_half hn]
  push_cast
  linear_combination (k : ZMod n) * h2

/-- `ω^{n/2} = -1` for a primitive `n`-th root of unity, `n` even. -/
theorem H7_pow_half_eq_neg_one {n : ℕ} [NeZero n] (hn : Even n) {L : Type*} [Field L] {ω : L}
    (hω : IsPrimitiveRoot ω n) : ω ^ (n / 2) = -1 := by
  have h2 : n % 2 = 0 := Nat.even_iff.mp hn
  have hpos := NeZero.pos n
  have hsq : (ω ^ (n / 2)) ^ 2 = 1 := by
    rw [← pow_mul, show n / 2 * 2 = n by omega, hω.pow_eq_one]
  have hne : ω ^ (n / 2) ≠ 1 := by
    intro h1
    have hd := (hω.pow_eq_one_iff_dvd (n / 2)).mp h1
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hprod : (ω ^ (n / 2) - 1) * (ω ^ (n / 2) + 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hprod with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hne
  · exact eq_neg_of_add_eq_zero_left h1

/-- Exponent model: `ξ · (-ξ) = -ξ^2`, i.e. `ω^x · ω^{x+n/2} = -ω^{2x}`. -/
theorem H7_omega_pair {n : ℕ} [NeZero n] (hn : Even n) {L : Type*} [Field L] {ω : L}
    (hω : IsPrimitiveRoot ω n) (x : ZMod n) :
    ω ^ x.val * ω ^ (x + half n).val = -ω ^ (2 * x).val := by
  rw [H7_pow_val_add ω hω.pow_eq_one, H7_half_val, H7_pow_half_eq_neg_one hn hω, two_mul,
    H7_pow_val_add ω hω.pow_eq_one]
  ring

/-- For even `n`: `-x + n/2 = -(x + n/2)` in `ZMod n`. -/
theorem H7_neg_add_half {n : ℕ} [NeZero n] (hn : Even n) (x : ZMod n) : -x + half n = -(x + half n) := by
  have := H7_two_half hn
  linear_combination this

/-- `(-1)^{r σ} = (-1)^{|σ|}` for odd `r` (integer power). -/
theorem H7_neg_one_zpow {L : Type*} [Field L] (r : ℕ) (hr : Odd r) (σ : ℤ) :
    (-1 : L) ^ ((r : ℤ) * σ) = (-1) ^ σ.natAbs := by
  rw [zpow_mul, zpow_natCast, hr.neg_one_pow]
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg σ
  · rw [zpow_natCast, Int.natAbs_natCast]
  · rw [zpow_neg, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast, ← inv_pow, inv_neg_one]

/-! ## Coverage — s2_xia.tex:52-53 (sec_2_2_norm) -/

/-- In `F = F_{3^{n/2}}`, `4 ∣ n`: `(y^Q)^Q = y`, `Q = 3^{n/4}`. -/
theorem H7_pow_QQ (n : ℕ) (h4 : 4 ∣ n) (y : GaloisField 3 (n / 2)) :
    (y ^ 3 ^ (n / 4)) ^ 3 ^ (n / 4) = y := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp
  · let _ := Fintype.ofFinite (GaloisField 3 (n / 2))
    have hc : Fintype.card (GaloisField 3 (n / 2)) = 3 ^ (n / 2) := by
      rw [Fintype.card_eq_nat_card, GaloisField.card 3 (n / 2) (by omega)]
    rw [← pow_mul, ← pow_add, show n / 4 + n / 4 = n / 2 by omega, ← hc, FiniteField.pow_card]

theorem sec_2_2_norm_proved (n : ℕ) (h4 : 4 ∣ n) (x : GaloisField 3 (n / 2)) :
    Nm n x = x * bar n x ∧ bar n (Nm n x) = Nm n x ∧ bar n (bar n x) = x := by
  have hbb : ∀ y : GaloisField 3 (n / 2), bar n (bar n y) = y := fun y => H7_pow_QQ n h4 y
  have hNm : Nm n x = x * bar n x := by
    unfold Nm bar
    rw [pow_add, pow_one]
  have hmul : ∀ a b : GaloisField 3 (n / 2), bar n (a * b) = bar n a * bar n b := fun a b => mul_pow a b _
  refine ⟨hNm, ?_, hbb x⟩
  rw [hNm, hmul, hbb, mul_comm]

/-! ## Coverage — s3_pow2.tex:87 (sec_3_2_V_card) -/

/-- A set of solutions of `x^Q = c x` (`Q ≥ 2`) in a field has at most `Q` elements. -/
theorem H7_card_le {F : Type*} [Field F] (Q : ℕ) (hQ : 2 ≤ Q) (c : F) (s : Set F)
    (hs : ∀ x ∈ s, x ^ Q = c * x) : Nat.card s ≤ Q := by
  classical
  set p : Polynomial F := Polynomial.X ^ Q - Polynomial.C c * Polynomial.X with hp
  have hdeg : p.natDegree = Q := by
    rw [hp, Polynomial.natDegree_sub_eq_left_of_natDegree_lt, Polynomial.natDegree_X_pow]
    rw [Polynomial.natDegree_X_pow]
    exact lt_of_le_of_lt (Polynomial.natDegree_C_mul_le c Polynomial.X) (by rw [Polynomial.natDegree_X]; omega)
  have hp0 : p ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg
    omega
  have hsub : s ⊆ (p.roots.toFinset : Set F) := by
    intro x hx
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot.def, hp]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul,
      Polynomial.eval_C]
    rw [hs x hx, sub_self]
  calc Nat.card s = s.ncard := Nat.card_coe_set_eq s
    _ ≤ (p.roots.toFinset : Set F).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = p.roots.toFinset.card := Set.ncard_coe_finset _
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := Polynomial.card_roots' p
    _ = Q := hdeg

/-- The additive map `x ↦ x^Q + x` on `F_{3^{n/2}}` (`Q = 3^{n/4}`; char 3). -/
noncomputable def H7_trace (n : ℕ) : GaloisField 3 (n / 2) →+ GaloisField 3 (n / 2) where
  toFun x := x ^ 3 ^ (n / 4) + x
  map_zero' := by simp
  map_add' x y := by
    rw [add_pow_char_pow]
    ring

theorem sec_3_2_V_card_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 4 ≤ e) :
    Nat.card (Vsp n : Set (GaloisField 3 (n / 2))) = QQ n := by
  have h16 : 16 ≤ n := by
    rw [hne]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have h4 : 4 ∣ n := by
    rw [hne, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact pow_dvd_pow 2 (by omega)
  have hQ2 : 2 ≤ 3 ^ (n / 4) :=
    calc 2 ≤ 3 ^ 1 := by norm_num
      _ ≤ 3 ^ (n / 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcardF : Nat.card (GaloisField 3 (n / 2)) = 3 ^ (n / 4) * 3 ^ (n / 4) := by
    rw [GaloisField.card 3 (n / 2) (by omega), ← pow_add]
    congr 1
    omega
  set f := H7_trace n with hf
  have hker : (Vsp n : Set (GaloisField 3 (n / 2))) = (f.ker : Set (GaloisField 3 (n / 2))) := by
    ext x
    rw [SetLike.mem_coe, AddMonoidHom.mem_ker]
    show x ^ 3 ^ (n / 4) = -x ↔ x ^ 3 ^ (n / 4) + x = 0
    exact eq_neg_iff_add_eq_zero
  have hk : Nat.card f.ker ≤ 3 ^ (n / 4) := by
    have := H7_card_le (3 ^ (n / 4)) hQ2 (-1 : GaloisField 3 (n / 2)) (Vsp n)
      (fun x hx => by rw [neg_one_mul]; exact hx)
    rw [hker] at this
    exact this
  have hr : Nat.card f.range ≤ 3 ^ (n / 4) := by
    refine H7_card_le (3 ^ (n / 4)) hQ2 (1 : GaloisField 3 (n / 2)) (f.range : Set (GaloisField 3 (n / 2)))
      (fun z hz => ?_)
    rw [SetLike.mem_coe, AddMonoidHom.mem_range] at hz
    obtain ⟨y, rfl⟩ := hz
    show (y ^ 3 ^ (n / 4) + y) ^ 3 ^ (n / 4) = 1 * (y ^ 3 ^ (n / 4) + y)
    rw [add_pow_char_pow, H7_pow_QQ n h4, one_mul, add_comm]
  have hmul : Nat.card f.ker * Nat.card f.range = Nat.card (GaloisField 3 (n / 2)) := by
    rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]
  have hb : Nat.card f.ker * Nat.card f.range ≤ Nat.card f.ker * 3 ^ (n / 4) := Nat.mul_le_mul_left _ hr
  have hge : 3 ^ (n / 4) * 3 ^ (n / 4) ≤ Nat.card f.ker * 3 ^ (n / 4) := by
    rw [← hcardF, ← hmul]
    exact hb
  have hge' := le_of_mul_le_mul_right hge (by positivity)
  rw [hker]
  show Nat.card f.ker = 3 ^ (n / 4)
  omega

/-! ## Coverage — s6_primes.tex:72-74 (thm_6_2_sets) -/

theorem H7_factor (Q : ℕ) (hQ : 1 ≤ Q) : Q ^ 4 - 1 = (Q - 1) * (Q + 1) * (Q ^ 2 + 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, Q = t + 1 := ⟨Q - 1, by omega⟩
  have h : (t + 1) ^ 4 = t * (t + 1 + 1) * ((t + 1) ^ 2 + 1) + 1 := by ring
  rw [h, Nat.add_sub_cancel, Nat.add_sub_cancel]

theorem H7_four_dvd (Q : ℕ) (hQ : Odd Q) : 4 ∣ (Q + 1) * (Q ^ 2 + 1) := by
  have h1 : 2 ∣ Q + 1 := by
    obtain ⟨t, ht⟩ := hQ
    exact ⟨t + 1, by omega⟩
  have h2 : 2 ∣ Q ^ 2 + 1 := by
    obtain ⟨t, ht⟩ := hQ.pow (n := 2)
    exact ⟨t + 1, by omega⟩
  exact Nat.mul_dvd_mul h1 h2

theorem thm_6_2_sets_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (_heo : Odd e) (ξ0 : GaloisField 5 n)
    (hξ0 : IsPrimitiveRoot ξ0 n) :
    4 * (5 ^ (n / 4) - 1) ∣ 5 ^ n - 1 ∧
      5 ^ n - 1 = (5 ^ (n / 4) - 1) * (5 ^ (n / 4) + 1) * ((5 ^ (n / 4)) ^ 2 + 1) ∧
      (fun x : GaloisField 5 n => x ^ (5 ^ (n / 4) - 1)) '' {x | x ^ (4 * (5 ^ (n / 4) - 1)) = 1} = {z | z ^ 4 = 1} ∧
      (-ξ0 ^ (n / 4)) ^ 4 = 1 := by
  have h4 : 4 ∣ n := by
    rw [hne, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact pow_dvd_pow 2 (by omega)
  have hnQ : 5 ^ n = (5 ^ (n / 4)) ^ 4 := by
    rw [← pow_mul]
    congr 1
    omega
  have hQ1 : 1 ≤ 5 ^ (n / 4) := Nat.one_le_pow _ _ (by norm_num)
  have hfact : 5 ^ n - 1 = (5 ^ (n / 4) - 1) * (5 ^ (n / 4) + 1) * ((5 ^ (n / 4)) ^ 2 + 1) := by
    rw [hnQ]
    exact H7_factor _ hQ1
  have hdvd : 4 * (5 ^ (n / 4) - 1) ∣ 5 ^ n - 1 := by
    rw [hfact, mul_assoc, mul_comm 4]
    exact Nat.mul_dvd_mul_left _ (H7_four_dvd _ (Odd.pow (by decide)))
  refine ⟨hdvd, hfact, ?_, ?_⟩
  · ext z
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← pow_mul, mul_comm]
      exact hx
    · intro hz
      obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (GaloisField 5 n)ˣ)
      have hcard : Nat.card (GaloisField 5 n)ˣ = 5 ^ n - 1 := by
        rw [Nat.card_units, GaloisField.card 5 n (NeZero.ne n)]
      have hgp : IsPrimitiveRoot (g : GaloisField 5 n) (5 ^ n - 1) := by
        rw [IsPrimitiveRoot.coe_units_iff, ← hcard, ← hg]
        exact IsPrimitiveRoot.orderOf g
      have : NeZero (5 ^ n - 1) := ⟨by
        have := Nat.one_lt_pow (NeZero.ne n) (by norm_num : 1 < 5)
        omega⟩
      obtain ⟨M, hM⟩ := hdvd
      have hzN : z ^ (5 ^ n - 1) = 1 := by
        rw [hM, pow_mul, pow_mul, hz, one_pow, one_pow]
      obtain ⟨i, -, hi⟩ := hgp.eq_pow_of_pow_eq_one hzN
      have h4i : 5 ^ n - 1 ∣ 4 * i := by
        rw [← hgp.pow_eq_one_iff_dvd, mul_comm, pow_mul, hi, hz]
      obtain ⟨c, hc⟩ := h4i
      have hi' : i = (5 ^ (n / 4) - 1) * M * c := by
        have h' : 4 * i = 4 * ((5 ^ (n / 4) - 1) * M * c) := by
          rw [hc, hM]
          ring
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) h'
      refine ⟨(g : GaloisField 5 n) ^ (M * c), ?_, ?_⟩
      · rw [← pow_mul, show M * c * (4 * (5 ^ (n / 4) - 1)) = (5 ^ n - 1) * c by rw [hM]; ring, pow_mul,
          hgp.pow_eq_one, one_pow]
      · rw [← pow_mul, show M * c * (5 ^ (n / 4) - 1) = i by rw [hi']; ring, hi]
  · rw [Even.neg_pow ⟨2, by norm_num⟩, ← pow_mul, Nat.div_mul_cancel h4, hξ0.pow_eq_one]

/-! ## Coverage — P10s_main.tex:178, s5_twonorms.tex:22 (caseAB_even) -/

/-- A finite set with a fixed-point-free involution has even size. -/
theorem H7_even_card_of_invol {α : Type*} (s : Finset α) (g : α → α)
    (hmem : ∀ a ∈ s, g a ∈ s) (hinv : ∀ a ∈ s, g (g a) = a) (hne : ∀ a ∈ s, g a ≠ a) : Even s.card := by
  have hsum : ∑ _x ∈ s, (1 : ZMod 2) = 0 :=
    Finset.sum_involution (fun a _ => g a) (fun _ _ => by decide) (fun a ha _ => hne a ha)
      (fun a ha => hmem a ha) (fun a ha => hinv a ha)
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  exact ZMod.natCast_eq_zero_iff_even.mp hsum

theorem H7_val_odd_iff {n : ℕ} [NeZero n] (h2 : 2 ∣ n) (j : ZMod n) :
    Odd j.val ↔ ZMod.castHom h2 (ZMod 2) j = 1 := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_one_iff_odd]

/-- Elements of the orbit of an odd `k` under `k ↦ 3k` are odd (`n` even). -/
theorem H7_orbit_odd {n : ℕ} [NeZero n] (h2 : 2 ∣ n) (k : ZMod n) (hk : Odd k.val) :
    ∀ j ∈ orbit 3 k, Odd j.val := by
  intro j hj
  simp only [orbit, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  obtain ⟨i, rfl⟩ := hj
  rw [H7_val_odd_iff h2] at hk ⊢
  rw [map_mul, map_pow, hk, mul_one, map_natCast]
  have h3 : ((3 : ℕ) : ZMod 2) = 1 := by decide
  rw [h3, one_pow]

theorem caseAB_even_proved (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (_hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n) :
    ∀ O ∈ topOrbits n 3, IsCaseA O ∨ IsCaseB O → Even O.card := by
  have h8 : 8 ∣ n := by
    rw [hn, show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 ha) _
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h8
  have hev : Even n := even_iff_two_dvd.mpr h2
  have hpos := NeZero.pos n
  intro O hO hAB
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hO
  have hkodd : Odd k.val := (Finset.mem_filter.mp hk).2
  have hmem_odd := H7_orbit_odd h2 k hkodd
  rcases hAB with hA | hB
  · refine H7_even_card_of_invol (orbit 3 k) (fun j => j + half n) (fun j hj => ?_) (fun j _ => ?_)
      (fun j _ => ?_)
    · rw [← hA]
      exact Finset.mem_image_of_mem _ hj
    · show j + half n + half n = j
      rw [add_assoc, H7_two_half hev, add_zero]
    · intro hfix
      have h0 : half n = (0 : ZMod n) := by
        have : j + half n = j + 0 := by rw [add_zero]; exact hfix
        exact add_left_cancel this
      have hv := congrArg ZMod.val h0
      rw [H7_half_val, ZMod.val_zero] at hv
      omega
  · refine H7_even_card_of_invol (orbit 3 k) (fun j => -(j + half n)) (fun j hj => ?_) (fun j _ => ?_)
      (fun j hj => ?_)
    · have hj' : j + half n ∈ inv (orbit 3 k) := by
        rw [← hB]
        exact Finset.mem_image_of_mem _ hj
      obtain ⟨j', hj'1, hj'2⟩ := Finset.mem_image.mp hj'
      show -(j + half n) ∈ orbit 3 k
      rw [← hj'2, neg_neg]
      exact hj'1
    · show -(-(j + half n) + half n) = j
      ring
    · intro hfix
      have hsum : ((j.val + j.val + n / 2 : ℕ) : ZMod n) = 0 := by
        rw [Nat.cast_add, Nat.cast_add, ZMod.natCast_zmod_val]
        show j + j + half n = 0
        linear_combination -hfix
      have hdvd := (ZMod.natCast_eq_zero_iff _ _).mp hsum
      have h8' := dvd_trans h8 hdvd
      have hjo := hmem_odd j hj
      rw [Nat.odd_iff] at hjo
      omega

/-! ## Coverage — s5_twonorms.tex:4 (fibre_not_linear) -/

theorem fibre_not_linear_proved (n : ℕ) [NeZero n] {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L)
    (y : ZMod n → GaloisField 3 (n / 2)) : (0 : ZMod n → GaloisField 3 (n / 2)) ∉ fibre ω y := by
  rintro ⟨⟨-, -, hR, -⟩, -⟩
  simp [R] at hR

/-! ## Coverage — P10s_main.tex:72-75 (intro_planar_2_8) -/

/-- If the `k`-th roots of unity in `ZMod p` are exactly `H` and every non-zero `d` is a difference of two elements of
`H` in exactly one way (a finite count), then the planar statement holds. -/
theorem H7_planar {p k : ℕ} (H : Finset (ZMod p)) (hH : ∀ h : ZMod p, h ^ k = 1 ↔ h ∈ H)
    (hcount : ∀ d : ZMod p, d ≠ 0 → ((H ×ˢ H).filter (fun hh => hh.1 - hh.2 = d)).card = 1) :
    ∀ d : ZMod p, d ≠ 0 → ∃! hh : ZMod p × ZMod p, hh.1 ^ k = 1 ∧ hh.2 ^ k = 1 ∧ hh.1 - hh.2 = d := by
  intro d hd
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hcount d hd)
  have hmem : ∀ hh : ZMod p × ZMod p, hh ∈ (H ×ˢ H).filter (fun hh => hh.1 - hh.2 = d) ↔
      (hh.1 ^ k = 1 ∧ hh.2 ^ k = 1 ∧ hh.1 - hh.2 = d) := by
    intro hh
    rw [Finset.mem_filter, Finset.mem_product, hH, hH, and_assoc]
  refine ⟨a, (hmem a).mp (by rw [ha]; exact Finset.mem_singleton_self a), fun b hb => ?_⟩
  have hb' := (hmem b).mpr hb
  rw [ha] at hb'
  exact Finset.mem_singleton.mp hb'

theorem intro_planar_2_8_proved :
    (∀ d : ZMod 7, d ≠ 0 → ∃! hh : ZMod 7 × ZMod 7, hh.1 ^ 3 = 1 ∧ hh.2 ^ 3 = 1 ∧ hh.1 - hh.2 = d) ∧
      (∀ d : ZMod 73, d ≠ 0 → ∃! hh : ZMod 73 × ZMod 73, hh.1 ^ 9 = 1 ∧ hh.2 ^ 9 = 1 ∧ hh.1 - hh.2 = d) :=
  ⟨H7_planar {1, 2, 4} (by decide +kernel) (by decide +kernel),
    H7_planar {1, 2, 4, 8, 16, 32, 37, 55, 64} (by decide +kernel) (by decide +kernel)⟩

/-! ## Row 21e — Theorem 6.2, Step 3 (thm_6_2_step3) -/

theorem thm_6_2_step3_proved (n : ℕ) [NeZero n] (h4 : 4 ∣ n) {L : Type*} [Field L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (κ : L) (hκ : κ ^ 2 = -1) (h : ZMod n → L) (s0 : L) (hs : s0 ^ 2 = κ) (x : ZMod n)
    (hF1 : ∀ z ∈ ({x, x + half n} : Set (ZMod n)), h (5 * z) = (ω ^ z.val) ^ 5 * h z ^ 5)
    (hF3 : ∀ z ∈ ({x, x + half n} : Set (ZMod n)), h z * h (-z) = κ * (ω ^ z.val) ^ (n / 2)) :
    h (5 * x) * h (5 * x + half n) / s0 = (ω ^ (2 * x).val) ^ 5 * (h x * h (x + half n) / s0) ^ 5 ∧
      (h x * h (x + half n) / s0) * (h (-x) * h (-x + half n) / s0) = κ * (ω ^ (2 * x).val) ^ (n / 2) := by
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h4)
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    norm_num at hκ
  have hx1 : x ∈ ({x, x + half n} : Set (ZMod n)) := Or.inl rfl
  have hx2 : x + half n ∈ ({x, x + half n} : Set (ZMod n)) := Or.inr rfl
  have h5 : (5 : ZMod n) * half n = half n := by
    have := H7_odd_mul_half hev 5 ⟨2, rfl⟩
    exact_mod_cast this
  have hpair := H7_omega_pair hev hω x
  have hC : ω ^ (2 * x).val = -(ω ^ x.val * ω ^ (x + half n).val) := by rw [hpair, neg_neg]
  have hs4 : s0 ^ 4 = -1 := by
    rw [show s0 ^ 4 = (s0 ^ 2) ^ 2 by ring, hs, hκ]
  have hs5 : s0 ^ 5 = -s0 := by linear_combination s0 * hs4
  constructor
  · have e1 := hF1 x hx1
    have e2 := hF1 (x + half n) hx2
    rw [mul_add, h5] at e2
    rw [e1, e2, hC, div_pow, hs5, div_neg]
    ring
  · rw [H7_neg_add_half hev,
      show h x * h (x + half n) / s0 * (h (-x) * h (-(x + half n)) / s0)
        = (h x * h (-x)) * (h (x + half n) * h (-(x + half n))) / s0 ^ 2 by ring,
      hF3 x hx1, hF3 (x + half n) hx2, hs, div_eq_iff hκ0]
    have he : Even (n / 2) := ⟨n / 4, by omega⟩
    rw [hC, he.neg_pow]
    ring

/-! ## Row 21f — Theorem 6.2, Step 4 (thm_6_2_step4) -/

theorem thm_6_2_step4_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) {L : Type*} [Field L]
    [CharP L 5] (ω : L) (hω : IsPrimitiveRoot ω n) (h : ZMod n → L) (hF3 : F3r (kappa n L) ω h) (s0 : L)
    (hs : s0 ^ 2 = kappa n L) :
    h ((n / 4 : ℕ) : ZMod n) * h (((n / 4 : ℕ) : ZMod n) + half n) = kappa n L ∧ kappa n L / s0 = s0 ∧
      (h 0 = (n : L) ∨ h 0 = -(n : L)) ∧ h 0 = h 0 ^ 5 ∧ s0 = (ω ^ (half n).val) ^ 5 * s0 ^ 5 := by
  have h8 : 8 ∣ n := by
    rw [hne, show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact pow_dvd_pow 2 he
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h8)
  have hpos := NeZero.pos n
  obtain ⟨hF3a, hF3b⟩ := hF3
  -- arithmetic in characteristic 5: `n^2 = -1`, `κ = -n`, `κ^2 = -1`, `S^4 = -1`
  have h5 : (5 : L) = 0 := by exact_mod_cast CharP.cast_eq_zero L 5
  have hn2 : (n : L) ^ 2 = -1 := by
    have h4' : (4 : L) = -1 := by linear_combination h5
    rw [hne, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, mul_comm e 2, pow_mul,
      show (2 : L) ^ 2 = 4 by norm_num, h4', heo.neg_one_pow]
  have hκ : kappa n L = -(n : L) := by
    unfold kappa pp
    push_cast
    linear_combination ((n : L) ^ 2 + (n : L)) * hn2
  have hκ2 : kappa n L ^ 2 = -1 := by rw [hκ, neg_sq, hn2]
  have hs4 : s0 ^ 4 = -1 := by rw [show s0 ^ 4 = (s0 ^ 2) ^ 2 by ring, hs, hκ2]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (F3_5) at `ι_5 = ω^{n/4}`
    have hkv : ((n / 4 : ℕ) : ZMod n).val = n / 4 := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have hk0 : ((n / 4 : ℕ) : ZMod n) ≠ 0 := by
      intro h0
      have := congrArg ZMod.val h0
      rw [hkv, ZMod.val_zero] at this
      omega
    have hneg : -((n / 4 : ℕ) : ZMod n) = ((n / 4 : ℕ) : ZMod n) + half n := by
      have hsum : ((n / 4 : ℕ) : ZMod n) + half n + ((n / 4 : ℕ) : ZMod n) = 0 := by
        unfold half
        rw [← Nat.cast_add, ← Nat.cast_add, show n / 4 + n / 2 + n / 4 = n by omega, ZMod.natCast_self]
      linear_combination -hsum
    have e := hF3a _ hk0
    obtain ⟨m, hm⟩ := h8
    have hexp : n / 4 * (n / 2) = n * m := by
      rw [show n / 4 = 2 * m by omega, show n / 2 = 4 * m by omega, hm]
      ring
    rw [hneg, hkv, ← pow_mul, hexp, pow_mul, hω.pow_eq_one, one_pow, mul_one] at e
    exact e
  · rcases eq_or_ne s0 0 with h0 | h0
    · rw [h0, div_zero]
    · rw [← hs, pow_two, mul_div_assoc, div_self h0, mul_one]
  · have hprod : (h 0 - n) * (h 0 + n) = 0 := by linear_combination hF3b
    rcases mul_eq_zero.mp hprod with h1 | h1
    · left
      linear_combination h1
    · right
      linear_combination h1
  · linear_combination (-(h 0) * (h 0 ^ 2 + (n : L) ^ 2)) * hF3b + (-(h 0) * ((n : L) ^ 2 - 1)) * hn2
  · rw [H7_half_val, H7_pow_half_eq_neg_one hev hω]
    linear_combination s0 * hs4

/-! ## Row 24b — Theorem 6.4, Step 3 (thm_6_4_step3) -/

theorem thm_6_4_step3_proved (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a)
    (_hodd : Odd nodd) (hr : ¬ r ∣ pp n * n) (σr : ℤ) {L : Type*} [Field L] [CharP L r] (ω : L)
    (hω : IsPrimitiveRoot ω n) (h : ZMod n → L) (s0 : L) (hs : s0 ^ 2 = kappa n L) (x : ZMod n)
    (hF1 : ∀ z ∈ ({x, x + half n} : Set (ZMod n)), h ((r : ZMod n) * z) = (ω ^ z.val) ^ ((r : ℤ) * σr) * h z ^ r)
    (hF3 : ∀ z ∈ ({x, x + half n} : Set (ZMod n)), h z * h (-z) = kappa n L * (ω ^ z.val) ^ (n / 2)) :
    s0⁻¹ * h ((r : ZMod n) * x) * h ((r : ZMod n) * x + half n) =
        (-1) ^ σr.natAbs * s0 ^ (r - 1) * (ω ^ (2 * x).val) ^ ((r : ℤ) * σr) * (s0⁻¹ * h x * h (x + half n)) ^ r ∧
      s0 ^ (r - 1) = (legendreSym r (pp n : ℤ) : L) ∧
      (s0⁻¹ * h x * h (x + half n)) * (s0⁻¹ * h (-x) * h (-x + half n)) = kappa n L * (ω ^ (2 * x).val) ^ (n / 2) := by
  have hp : r.Prime := Fact.out
  have hn4 : 4 ∣ n := by
    rw [hn, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) hn4)
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact hr (dvd_mul_of_dvd_right (even_iff_two_dvd.mp hev) _)
  have hrodd : Odd r := hp.odd_of_ne_two hr2
  -- κ ≠ 0, hence S ≠ 0
  have hκ : kappa n L ≠ 0 := by
    have hc : ((n ^ 2 * pp n : ℕ) : L) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff L r]
      intro hd
      rcases (Nat.Prime.dvd_mul hp).mp hd with hd1 | hd1
      · exact hr (dvd_mul_of_dvd_right (hp.dvd_of_dvd_pow hd1) _)
      · exact hr (dvd_mul_of_dvd_left hd1 _)
    unfold kappa
    exact_mod_cast hc
  have hs0 : s0 ≠ 0 := by
    rintro rfl
    apply hκ
    rw [← hs]
    ring
  have hx1 : x ∈ ({x, x + half n} : Set (ZMod n)) := Or.inl rfl
  have hx2 : x + half n ∈ ({x, x + half n} : Set (ZMod n)) := Or.inr rfl
  have hrh : (r : ZMod n) * half n = half n := H7_odd_mul_half hev r hrodd
  have hpair := H7_omega_pair hev hω x
  -- Euler's criterion pushed from `ZMod r` into `L`
  obtain ⟨k, hk⟩ := hrodd
  have hnr : ((n : ℤ) : ZMod r) ≠ 0 := by
    rw [Int.cast_natCast, Ne, CharP.cast_eq_zero_iff (ZMod r) r]
    exact fun hd => hr (dvd_mul_of_dvd_right hd _)
  have hleg : (kappa n L) ^ k = ((legendreSym r (pp n : ℤ) : ℤ) : L) := by
    have e1 := legendreSym.eq_pow r ((n : ℤ) ^ 2 * (pp n : ℤ))
    rw [show r / 2 = k by omega, legendreSym.mul, legendreSym.sq_one' r hnr, one_mul] at e1
    have e2 := congrArg (ZMod.castHom (dvd_refl r) L) e1
    simp only [map_pow, map_intCast] at e2
    rw [e2]
    unfold kappa
    push_cast
    ring
  have hsr : s0 ^ (r - 1) = kappa n L ^ k := by
    rw [hk, Nat.add_sub_cancel, pow_mul, hs]
  refine ⟨?_, by rw [hsr, hleg], ?_⟩
  · have e1 := hF1 x hx1
    have e2 := hF1 (x + half n) hx2
    rw [mul_add, hrh] at e2
    rw [e1, e2]
    have hsq : ((-1 : L) ^ σr.natAbs) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    have hCz : (ω ^ (2 * x).val) ^ ((r : ℤ) * σr) =
        (-1) ^ σr.natAbs * ((ω ^ x.val) ^ ((r : ℤ) * σr) * (ω ^ (x + half n).val) ^ ((r : ℤ) * σr)) := by
      rw [← mul_zpow, hpair, show -ω ^ (2 * x).val = (-1) * ω ^ (2 * x).val by ring, mul_zpow,
        H7_neg_one_zpow r ⟨k, hk⟩]
      linear_combination (-(ω ^ (2 * x).val) ^ ((r : ℤ) * σr)) * hsq
    have hinv : s0 ^ (r - 1) * s0⁻¹ ^ r = s0⁻¹ := by
      rw [hk, Nat.add_sub_cancel, pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hs0, one_pow, one_mul]
    rw [hCz, mul_pow, mul_pow]
    linear_combination (-(s0 ^ (r - 1) * s0⁻¹ ^ r * (ω ^ x.val) ^ ((r : ℤ) * σr) *
        (ω ^ (x + half n).val) ^ ((r : ℤ) * σr) * h x ^ r * h (x + half n) ^ r)) * hsq -
      ((ω ^ x.val) ^ ((r : ℤ) * σr) * (ω ^ (x + half n).val) ^ ((r : ℤ) * σr) * h x ^ r *
        h (x + half n) ^ r) * hinv
  · rw [H7_neg_add_half hev,
      show s0⁻¹ * h x * h (x + half n) * (s0⁻¹ * h (-x) * h (-(x + half n)))
        = (h x * h (-x)) * (h (x + half n) * h (-(x + half n))) / s0 ^ 2 by ring,
      hF3 x hx1, hF3 (x + half n) hx2, hs, div_eq_iff hκ]
    have he : Even (n / 2) := ⟨n / 4, by omega⟩
    rw [show (ω ^ (2 * x).val) = -(ω ^ x.val * ω ^ (x + half n).val) by rw [hpair, neg_neg], he.neg_pow]
    ring

#print axioms sec_3_2_V_card_proved
#print axioms sec_2_2_norm_proved
#print axioms thm_6_2_sets_proved
#print axioms caseAB_even_proved
#print axioms fibre_not_linear_proved
#print axioms intro_planar_2_8_proved
#print axioms thm_6_4_step3_proved
#print axioms thm_6_2_step3_proved
#print axioms thm_6_2_step4_proved

end Xia.Proofs
