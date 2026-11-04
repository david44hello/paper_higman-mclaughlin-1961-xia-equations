/- Xia/Proofs/Thm34bc.lean — proofs of the rows eq_top_all_V, thm_3_4_b, thm_3_4_c, cor_3_5_i, cor_3_5_ii of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry
import Xia.Proofs.Thm31
import Xia.Proofs.Pow2Arith
import Xia.Proofs.Decoupling34
import Xia.Proofs.FourierSteps
import Xia.Proofs.Coverage
import Xia.Proofs.Signs
import Xia.Proofs.Prop24

namespace Xia.Proofs

open Xia Finset

set_option linter.unusedSectionVars false

/-! ## 1. Generic facts: (F1) from (L1), the top layer as `{±3^j}`, the `±`-parts by inversion -/

section Generic

variable {n : ℕ} [NeZero n]

/-- (F1) for `ŷ` from (L1) with `σ = 2` (Frobenius in characteristic 3, re-indexing `t ↦ t + 2`). -/
theorem H13_F1 {K : Type*} [Field K] [CharP K 3] {ω : K} (hω1 : ω ^ n = 1) (y : ZMod n → K)
    (hL1 : L1 3 ((2 : ℕ) : ℤ) y) (k : ZMod n) : dft ω y (3 * k) = (ω ^ k.val) ^ 6 * dft ω y k ^ 3 := by
  have hexp : ∀ t : ZMod n, (ω ^ (3 * k).val) ^ (t + 2).val = (ω ^ k.val) ^ 6 * ((ω ^ k.val) ^ t.val) ^ 3 := by
    intro t
    rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
    apply H4_pow_congr hω1
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, ZMod.natCast_zmod_val]
    ring
  unfold dft
  rw [sum_pow_char, Finset.mul_sum, ← Equiv.sum_comp (Equiv.addRight (2 : ZMod n))]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Equiv.coe_addRight]
  have h2 : y (t + 2) = y t ^ 3 := by
    have := hL1 t; push_cast at this; exact this
  rw [h2, hexp t]; ring

/-- The top layer `{k odd}` is the disjoint union of `{3^j : j < n/4}` and `{-3^j : j < n/4}` (Step 1). -/
theorem H13_top_sum {M : Type*} [AddCommMonoid M] {e : ℕ} (hne : n = 2 ^ e) (he : 3 ≤ e) (f : ZMod n → M) :
    ∑ k ∈ univ.filter (fun k : ZMod n => Odd k.val), f k =
      ∑ j ∈ range (n / 4), (f ((3 : ZMod n) ^ j) + f (-(3 : ZMod n) ^ j)) := by
  obtain ⟨-, -, hord, -, -, horb, hdisj, -⟩ := thm_3_1_step1_proved n e hne he
  have hn : Even n := H4_even_of_pow2 hne he
  obtain ⟨t8, ht1, hnt⟩ := H4_shape hne he
  have hpos : 0 < n / 4 := by omega
  have hord' : orderOf (3 : ZMod n) = n / 4 := by
    rw [hord]
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 3 := ⟨e - 3, by omega⟩
    rw [show k + 3 - 2 = k + 1 by omega, hne, show 2 ^ (k + 3) = 2 ^ (k + 1) * 4 by ring,
      Nat.mul_div_cancel _ (by norm_num)]
  have hfin : IsOfFinOrder (3 : ZMod n) := orderOf_pos_iff.mp (by rw [hord']; exact hpos)
  have hinj : Set.InjOn (fun j : ℕ => (3 : ZMod n) ^ j) (range (n / 4) : Set ℕ) := by
    intro i hi j hj hij
    have := hfin.pow_inj_mod.mp hij
    rw [hord', Nat.mod_eq_of_lt (Finset.mem_range.mp hi), Nat.mod_eq_of_lt (Finset.mem_range.mp hj)] at this
    exact this
  have hinj' : Set.InjOn (fun j : ℕ => -(3 : ZMod n) ^ j) (range (n / 4) : Set ℕ) := by
    intro i hi j hj hij
    exact hinj hi hj (neg_inj.mp hij)
  have hdisj' := H4_neg_ne hdisj
  have hAB : Disjoint ((range (n / 4)).image (fun j : ℕ => (3 : ZMod n) ^ j))
      ((range (n / 4)).image (fun j : ℕ => -(3 : ZMod n) ^ j)) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hxA
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hxB
    exact hdisj' i j hj
  have hmod : ∀ j : ℕ, (3 : ZMod n) ^ (j % (n / 4)) = 3 ^ j := fun j =>
    hfin.pow_inj_mod.mpr (by rw [hord', Nat.mod_mod])
  have hU : univ.filter (fun k : ZMod n => Odd k.val) =
      (range (n / 4)).image (fun j : ℕ => (3 : ZMod n) ^ j) ∪
        (range (n / 4)).image (fun j : ℕ => -(3 : ZMod n) ^ j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image,
      Finset.mem_range]
    constructor
    · intro hx
      obtain ⟨j, hj | hj⟩ := H4_odd_cases horb x hx
      · exact Or.inl ⟨j % (n / 4), Nat.mod_lt _ hpos, by rw [hj, hmod]⟩
      · exact Or.inr ⟨j % (n / 4), Nat.mod_lt _ hpos, by rw [hj, hmod]⟩
    · rintro (⟨j, -, rfl⟩ | ⟨j, -, rfl⟩)
      · exact H4_odd_val_pow3 hn j
      · exact H4_odd_val_neg hn _ (H4_odd_val_pow3 hn j)
  rw [hU, Finset.sum_union hAB, Finset.sum_image hinj, Finset.sum_image hinj', Finset.sum_add_distrib]

variable {F : Type*} [Field F]

/-- `((ω^k)^{-1})^{n/2} = (-1)^k` and the shift by `n/2` in the inversion weight. -/
theorem H13_weight_half {ω : F} (hω1 : ω ^ n = 1) (hhalf : ω ^ (n / 2) = -1) (t k : ZMod n) :
    ((ω ^ k.val)⁻¹) ^ (t + half n).val = ((ω ^ k.val)⁻¹) ^ t.val * (-1) ^ k.val := by
  have hwn : ((ω ^ k.val)⁻¹) ^ n = 1 := by
    rw [inv_pow, ← pow_mul, mul_comm, pow_mul, hω1, one_pow, inv_one]
  have hm : ((ω ^ k.val)⁻¹) ^ (n / 2) = (-1) ^ k.val := by
    rw [inv_pow, ← pow_mul, mul_comm, pow_mul, hhalf, ← inv_pow, inv_neg, inv_one]
  rw [H4_pow_val_add hwn, H4_half_val, hm]

/-- The sum over all `k` of `g k (1 ∓ (-1)^k)` is twice the sum over the odd (resp. even) `k`. -/
theorem H13_split_sub (g : ZMod n → F) :
    ∑ k, g k - ∑ k, g k * (-1) ^ k.val = 2 * ∑ k ∈ univ.filter (fun k : ZMod n => Odd k.val), g k := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_filter_add_sum_filter_not univ (fun k : ZMod n => Odd k.val),
    Finset.mul_sum]
  rw [Finset.sum_eq_zero (s := univ.filter (fun k : ZMod n => ¬ Odd k.val)), add_zero]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [(Finset.mem_filter.mp hk).2.neg_one_pow]; ring
  · intro k hk
    rw [(Nat.not_odd_iff_even.mp (Finset.mem_filter.mp hk).2).neg_one_pow]; ring

theorem H13_split_add (g : ZMod n → F) :
    ∑ k, g k + ∑ k, g k * (-1) ^ k.val = 2 * ∑ k ∈ univ.filter (fun k : ZMod n => ¬ Odd k.val), g k := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_filter_add_sum_filter_not univ (fun k : ZMod n => Odd k.val),
    Finset.mul_sum]
  rw [Finset.sum_eq_zero (s := univ.filter (fun k : ZMod n => Odd k.val)), zero_add]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [(Nat.not_odd_iff_even.mp (Finset.mem_filter.mp hk).2).neg_one_pow]; ring
  · intro k hk
    rw [(Finset.mem_filter.mp hk).2.neg_one_pow]; ring

/-- Orthogonality: `∑_k ω^{kd} = n [d = 0]` for a primitive `n`-th root `ω` (shift trick: the sum is fixed by `ω^d`). -/
theorem H13_orth {ω : F} (hω : IsPrimitiveRoot ω n) (d : ZMod n) :
    ∑ k : ZMod n, ω ^ ((k * d).val) = if d = 0 then (n : F) else 0 := by
  have hω1 := hω.pow_eq_one
  split_ifs with hd
  · subst hd
    simp only [mul_zero, ZMod.val_zero, pow_zero, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
      mul_one]
  · have hz : ω ^ d.val ≠ 1 :=
      hω.pow_ne_one_of_pos_of_lt (fun h => hd ((ZMod.val_eq_zero d).mp h)) (ZMod.val_lt d)
    have hshift : ∑ k : ZMod n, ω ^ ((k * d).val) = ω ^ d.val * ∑ k : ZMod n, ω ^ ((k * d).val) := by
      rw [Finset.mul_sum, ← (Equiv.sum_comp (Equiv.addRight (1 : ZMod n)) (fun k => ω ^ ((k * d).val)))]
      apply Finset.sum_congr rfl
      intro k _
      simp only [Equiv.coe_addRight]
      rw [add_mul, one_mul, H4_pow_val_add hω1]
      ring
    have h0 : (ω ^ d.val - 1) * ∑ k : ZMod n, ω ^ ((k * d).val) = 0 := by
      rw [sub_mul, one_mul, ← hshift, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hz)

/-- Fourier inversion `y_t = n^{-1} ∑_ξ ŷ(ξ) ξ^{-t}` (the instance of row `fourier_inversion` used here). -/
theorem H13_inversion {ω : F} (hω : IsPrimitiveRoot ω n) (hnF : (n : F) ≠ 0) (y : ZMod n → F) (t : ZMod n) :
    y t = (n : F)⁻¹ * ∑ k : ZMod n, dft ω y k * ((ω ^ k.val)⁻¹) ^ t.val := by
  have hω1 := hω.pow_eq_one
  have hω0 : ω ≠ 0 := hω.ne_zero (NeZero.ne n)
  have hterm : ∀ k s : ZMod n, y s * (ω ^ k.val) ^ s.val * ((ω ^ k.val)⁻¹) ^ t.val =
      y s * ω ^ ((k * (s - t)).val) := by
    intro k s
    rw [inv_pow, H4_pow_val_mul hω1, H4_pow_val_mul hω1]
    have h := H4_pow_val_add hω1 (k * (s - t)) (k * t)
    rw [show k * (s - t) + k * t = k * s by ring] at h
    rw [h, mul_assoc, mul_inv_cancel_right₀ (pow_ne_zero _ hω0)]
  have key : ∑ k : ZMod n, dft ω y k * ((ω ^ k.val)⁻¹) ^ t.val = (n : F) * y t := by
    unfold dft
    simp_rw [Finset.sum_mul, hterm]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, H13_orth hω]
    rw [Finset.sum_eq_single t (fun s _ hs => by rw [ite_eq_right (sub_ne_zero.mpr hs), mul_zero])
      (fun h => absurd (Finset.mem_univ t) h), ite_eq_left (sub_self t), mul_comm]
  rw [key, ← mul_assoc, inv_mul_cancel₀ hnF, one_mul]

/-- By inversion, `(y_t - y_{t+m})/2 = n^{-1} ∑_{k odd} ŷ(k) ξ^{-t}` (the top-layer part). -/
theorem H13_minus_sum (h2 : (2 : F) ≠ 0) {ω : F} (hω1 : ω ^ n = 1) (hhalf : ω ^ (n / 2) = -1)
    (y : ZMod n → F)
    (hinv : ∀ t : ZMod n, y t = (n : F)⁻¹ * ∑ k : ZMod n, dft ω y k * ((ω ^ k.val)⁻¹) ^ t.val) (t : ZMod n) :
    (y t - y (t + half n)) / 2 = (n : F)⁻¹ *
      ∑ k ∈ univ.filter (fun k : ZMod n => Odd k.val), dft ω y k * ((ω ^ k.val)⁻¹) ^ t.val := by
  have e2 := hinv (t + half n)
  simp_rw [H13_weight_half hω1 hhalf t, ← mul_assoc] at e2
  rw [hinv t, e2, ← mul_sub, H13_split_sub, mul_div_assoc, mul_div_cancel_left₀ _ h2]

/-- By inversion, `(y_t + y_{t+m})/2 = n^{-1} ∑_{k even} ŷ(k) ξ^{-t}` (the lower-layer part). -/
theorem H13_plus_sum (h2 : (2 : F) ≠ 0) {ω : F} (hω1 : ω ^ n = 1) (hhalf : ω ^ (n / 2) = -1)
    (y : ZMod n → F)
    (hinv : ∀ t : ZMod n, y t = (n : F)⁻¹ * ∑ k : ZMod n, dft ω y k * ((ω ^ k.val)⁻¹) ^ t.val) (t : ZMod n) :
    (y t + y (t + half n)) / 2 = (n : F)⁻¹ *
      ∑ k ∈ univ.filter (fun k : ZMod n => ¬ Odd k.val), dft ω y k * ((ω ^ k.val)⁻¹) ^ t.val := by
  have e2 := hinv (t + half n)
  simp_rw [H13_weight_half hω1 hhalf t, ← mul_assoc] at e2
  rw [hinv t, e2, ← mul_add, H13_split_add, mul_div_assoc, mul_div_cancel_left₀ _ h2]

/-- For even `n`, `s ↦ 2s` is 2-to-1 onto the even residues: `∑_s g(2s) = 2 ∑_v g(v)` when `g` vanishes on odd `v`. -/
theorem H13_sum_two_mul {M : Type*} [AddCommMonoid M] (hn : Even n) (g : ZMod n → M)
    (hg : ∀ v : ZMod n, Odd v.val → g v = 0) : ∑ s : ZMod n, g (2 * s) = 2 • ∑ v : ZMod n, g v := by
  classical
  rw [← Finset.sum_fiberwise univ (fun s : ZMod n => 2 * s) (fun s => g (2 * s)), Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_congr rfl (fun s hs => by rw [(Finset.mem_filter.mp hs).2]), Finset.sum_const]
  by_cases hv : Odd v.val
  · rw [hg v hv, smul_zero, smul_zero]
  · have hw := H4_two_mul_hf v hv
    have hfil : univ.filter (fun s : ZMod n => 2 * s = v) =
        {((v.val / 2 : ℕ) : ZMod n), ((v.val / 2 : ℕ) : ZMod n) + half n} := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      have := H9_two_mul_eq_iff hn s ((v.val / 2 : ℕ) : ZMod n)
      rw [hw] at this
      exact this
    have hne : ((v.val / 2 : ℕ) : ZMod n) ≠ ((v.val / 2 : ℕ) : ZMod n) + half n := by
      intro h; apply H9_half_ne_zero hn; linear_combination -h
    rw [hfil, Finset.card_pair hne]

/-- (F4) for `ŷ` from (L4) (the direction (L4) ⇒ (F4) of Prop 2.4), `n` even, `2 ≠ 0`:
`ŷ(ξ)ŷ(-ξ) = ∑_v ξ^v C(v)` with `C(v) = ∑_u (-1)^u y_u y_{v-u}`; `C` vanishes at odd `v` and `C(2s) = (y_s + y_{s+m})S`. -/
theorem H13_F4 {K : Type*} [Field K] (hn : Even n) (h2 : (2 : K) ≠ 0) {ω : K} (hω : IsPrimitiveRoot ω n)
    (y : ZMod n → K) (hL4 : L4 y) : F4 (dft ω y) := by
  have hω1 := hω.pow_eq_one
  have h2n : 2 ≤ n := by obtain ⟨r, hr⟩ := hn; have := NeZero.ne n; omega
  have hm : ω ^ (half n).val = -1 := H4_pow_val_half hω hn h2n
  intro k
  rw [H4_S_eq_dft hn h2n hω]
  -- Step A: the product as a sum over `v = t + u`
  have hA : dft ω y k * dft ω y (k + half n) =
      ∑ v : ZMod n, ω ^ ((k * v).val) * ∑ u : ZMod n, sgn u * y u * y (v - u) := by
    unfold dft
    have hshift : ∀ u : ZMod n, (ω ^ (k + half n).val) ^ u.val = sgn u * ω ^ ((k * u).val) := by
      intro u
      rw [H4_pow_val_mul hω1, add_mul, H4_pow_val_add hω1, ← H4_pow_val_mul hω1 (half n) u, hm]
      unfold sgn; ring
    simp_rw [hshift, H4_pow_val_mul hω1]
    rw [Finset.sum_mul_sum, Finset.sum_comm]
    have hinner : ∀ u : ZMod n, ∑ t : ZMod n, y t * ω ^ ((k * t).val) * (y u * (sgn u * ω ^ ((k * u).val))) =
        ∑ v : ZMod n, sgn u * y u * y (v - u) * ω ^ ((k * v).val) := by
      intro u
      refine Fintype.sum_equiv (Equiv.addRight u) _ _ (fun t => ?_)
      simp only [Equiv.coe_addRight, add_sub_cancel_right]
      rw [mul_add, H4_pow_val_add hω1]
      ring
    rw [Finset.sum_congr rfl (fun u _ => hinner u), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring
  -- Step B: `C(v) = 0` for odd `v`, `C(2s) = (y_s + y_{s+m}) S` for every `s`
  have hCodd : ∀ v : ZMod n, Odd v.val → ∑ u : ZMod n, sgn u * y u * y (v - u) = 0 := by
    intro v hv
    have hsv : (sgn v : K) = -1 := by unfold sgn; exact hv.neg_one_pow
    apply H9_eq_zero_of_eq_neg h2
    rw [← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv (Equiv.subLeft v) _ _ (fun u => ?_)
    simp only [Equiv.subLeft_apply, sub_sub_cancel]
    rw [sub_eq_add_neg v u, H5_sgn_add hn, H5_sgn_neg hn, hsv]
    ring
  have hC2 : ∀ s : ZMod n, ∑ u : ZMod n, sgn u * y u * y (2 * s - u) = (y s + y (s + half n)) * S y := by
    intro s
    by_cases hs : s.val < n / 2
    · exact hL4 s hs
    · have h4 := hL4 (s + half n) (H9_add_half_val_lt hn s hs)
      rw [show 2 * (s + half n) = 2 * s by rw [mul_add, H4_two_mul_half hn, add_zero], add_assoc,
        H4_half_add_half hn, add_zero] at h4
      rw [h4]; ring
  -- Step C: the 2-to-1 map `s ↦ 2s`
  have hC' : ∑ s : ZMod n, ω ^ ((k * (2 * s)).val) * ∑ u : ZMod n, sgn u * y u * y (2 * s - u) =
      2 • ∑ v : ZMod n, ω ^ ((k * v).val) * ∑ u : ZMod n, sgn u * y u * y (v - u) :=
    H13_sum_two_mul hn (fun v => ω ^ ((k * v).val) * ∑ u : ZMod n, sgn u * y u * y (v - u))
      (fun v hv => by rw [hCodd v hv, mul_zero])
  -- Step D: `∑_s ξ^{2s} (y_s + y_{s+m}) S = 2 S ŷ(ξ^2)`
  have hdft : dft ω y (2 * k) = ∑ s : ZMod n, y s * ω ^ ((2 * k * s).val) := by
    unfold dft; simp_rw [H4_pow_val_mul hω1]
  have hsh : ∑ s : ZMod n, ω ^ ((k * (2 * s)).val) * y (s + half n) = ∑ s : ZMod n, y s * ω ^ ((2 * k * s).val) := by
    refine Fintype.sum_equiv (Equiv.addRight (half n)) _ _ (fun s => ?_)
    simp only [Equiv.coe_addRight]
    rw [show 2 * k * (s + half n) = k * (2 * s) + k * (2 * half n) by ring, H4_two_mul_half hn, mul_zero, add_zero]
    ring
  have e1 : ∀ s : ZMod n, ω ^ ((k * (2 * s)).val) = ω ^ ((2 * k * s).val) := fun s => by
    rw [show k * (2 * s) = 2 * k * s by ring]
  have hD : ∑ s : ZMod n, ω ^ ((k * (2 * s)).val) * ((y s + y (s + half n)) * S y) = 2 * (S y * dft ω y (2 * k)) := by
    rw [hdft]
    calc ∑ s : ZMod n, ω ^ ((k * (2 * s)).val) * ((y s + y (s + half n)) * S y)
        = S y * ∑ s : ZMod n, y s * ω ^ ((2 * k * s).val) +
            S y * ∑ s : ZMod n, ω ^ ((k * (2 * s)).val) * y (s + half n) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro s _
          rw [e1]; ring
      _ = 2 * (S y * ∑ s : ZMod n, y s * ω ^ ((2 * k * s).val)) := by rw [hsh]; ring
  have key : (2 : K) * (dft ω y k * dft ω y (k + half n)) = 2 * (S y * dft ω y (2 * k)) := by
    calc (2 : K) * (dft ω y k * dft ω y (k + half n))
        = 2 • ∑ v : ZMod n, ω ^ ((k * v).val) * ∑ u : ZMod n, sgn u * y u * y (v - u) := by
          rw [hA, two_nsmul, two_mul]
      _ = ∑ s : ZMod n, ω ^ ((k * (2 * s)).val) * ∑ u : ZMod n, sgn u * y u * y (2 * s - u) := hC'.symm
      _ = ∑ s : ZMod n, ω ^ ((k * (2 * s)).val) * ((y s + y (s + half n)) * S y) :=
          Finset.sum_congr rfl (fun s _ => by rw [hC2 s])
      _ = 2 * (S y * dft ω y (2 * k)) := hD
  exact mul_left_cancel₀ h2 key

end Generic

/-! ## 2. eq:top-all-V (row 11e), EXACT -/

/-- Row 11e — equation (eq:top-all-V) (s3_pow2.tex:168-173), `n = 2^e`, `e ≥ 4`: for `ν` with `ν^{q-1} = -1` and every `x ∈ V`,
with `h_x(ξ_0^{3^k}) := ξ_0^{2k3^k} x^{3^k}` and `h_x(ξ_0^{-3^k}) := -ξ_0^{-2k3^k} ν^{-3^k} x^{q3^k}` on `O ∪ O^{-1}`
(`k < m/2`): `n^{-1} ∑ h_x(ξ) = n^{-1} Λ_ν(x + Tx)` and `n^{-1} ∑ h_x(ξ) ξ^{-1} = n^{-1} Λ'_ν(x - Tx)`; and for a parameter
`θ` with `θ^{1+q} = ν`, `h_θ = ŷ` on `O ∪ O^{-1}` (any solution `y` with `ŷ(ξ_0) = θ`). -/
theorem eq_top_all_V_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 4 ≤ e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) (ν : GaloisField 3 (n / 2)) (hν : ν ^ (qq n - 1) = -1) :
    (∀ x ∈ (Vsp n : Set (GaloisField 3 (n / 2))),
      (n : GaloisField 3 (n / 2))⁻¹ * ∑ k ∈ range (n / 4),
          (ξ0 ^ (2 * k * 3 ^ k) * x ^ (3 ^ k) - (ξ0⁻¹) ^ (2 * k * 3 ^ k) * (ν⁻¹) ^ (3 ^ k) * x ^ (qq n * 3 ^ k)) =
        (n : GaloisField 3 (n / 2))⁻¹ * Lam n ξ0 ν (x + Tmap n ξ0 x) ∧
      (n : GaloisField 3 (n / 2))⁻¹ * ∑ k ∈ range (n / 4),
          (ξ0 ^ (2 * k * 3 ^ k) * x ^ (3 ^ k) * (ξ0 ^ (3 ^ k))⁻¹ -
            (ξ0⁻¹) ^ (2 * k * 3 ^ k) * (ν⁻¹) ^ (3 ^ k) * x ^ (qq n * 3 ^ k) * ξ0 ^ (3 ^ k)) =
        (n : GaloisField 3 (n / 2))⁻¹ * Lam' n ξ0 ν (x - Tmap n ξ0 x)) ∧
    ∀ y ∈ NFSet n 2, dft ξ0 y 1 ^ (1 + qq n) = ν → ∀ k : ℕ,
      dft ξ0 y ((3 : ZMod n) ^ k) = ξ0 ^ (2 * k * 3 ^ k) * dft ξ0 y 1 ^ (3 ^ k) ∧
      dft ξ0 y (-(3 : ZMod n) ^ k) = -((ξ0⁻¹) ^ (2 * k * 3 ^ k) * (ν⁻¹) ^ (3 ^ k) * dft ξ0 y 1 ^ (qq n * 3 ^ k)) := by
  obtain ⟨hQ, hqodd, hQodd, hι2, hιq, hξq, hξQ, hhalf, hξ, hnd8, hnd, h8, hq9, hn, hnpos⟩ :=
    H8_setup n e hne he ξ0 hξ0
  have hι0 : iota n ξ0 ≠ 0 := by
    intro h; rw [h] at hι2; norm_num at hι2
  have hν0 : ν ≠ 0 := by
    intro h; rw [h, zero_pow (by omega)] at hν; exact one_ne_zero (neg_eq_zero.mp hν.symm)
  have hνq : ν ^ qq n = -ν := by rw [H8_pow_pred ν _ (by omega), hν]; ring
  refine ⟨fun x hx => ⟨?_, ?_⟩, ?_⟩
  · have hx' : x ^ QQ n = -x := hx
    rw [← H8_Y0 n ξ0 ν x h8 hnd8 hξq hξ hν0 hνq hx' hQ hι0]
    unfold H8_Y
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    unfold H8_term
    rw [pow_mul x (qq n) (3 ^ k), inv_pow, inv_pow]
    simp
  · have hx' : x ^ QQ n = -x := hx
    rw [← H8_Y1 n ξ0 ν x h8 hnd8 hξq hξ hν0 hνq hx' hQ hι0]
    unfold H8_Y
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    unfold H8_term
    rw [pow_mul x (qq n) (3 ^ k), inv_pow, inv_pow]
    simp
  · intro y hy hθν k
    obtain ⟨hL1, hL3, hRm, _⟩ := hy
    have hω1 := hξ0.pow_eq_one
    have hF1 : ∀ k : ZMod n, dft ξ0 y (3 * k) = (ξ0 ^ k.val) ^ 6 * dft ξ0 y k ^ 3 := H13_F1 hω1 y hL1
    have hF3 := H4_NF_F3 hne (by omega) hξ0 y hL3 hRm
    have hpos : dft ξ0 y ((3 : ZMod n) ^ k) = ξ0 ^ (2 * k * 3 ^ k) * dft ξ0 y 1 ^ (3 ^ k) := by
      have := H4_F1_iter hω1 hF1 k 1
      rwa [mul_one, H4_pow_one_val hω1] at this
    refine ⟨hpos, ?_⟩
    have h3 := hF3 ((3 : ZMod n) ^ k)
    rw [H4_E3 hω1, H4_pow3_half hhalf, hpos] at h3
    have hθ0 : dft ξ0 y 1 ≠ 0 := by
      intro h0; rw [h0, zero_pow (by omega)] at hθν; exact hν0 hθν.symm
    have hprod : dft ξ0 y 1 * (dft ξ0 y 1 ^ qq n * ν⁻¹) = 1 := by
      rw [← mul_assoc, ← pow_succ', add_comm, hθν, mul_inv_cancel₀ hν0]
    have hθinv : (dft ξ0 y 1)⁻¹ = dft ξ0 y 1 ^ qq n * ν⁻¹ := (eq_inv_of_mul_eq_one_right hprod).symm
    have hA : ξ0 ^ (2 * k * 3 ^ k) * dft ξ0 y 1 ^ (3 ^ k) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hξ) (pow_ne_zero _ hθ0)
    have hX : dft ξ0 y (-(3 : ZMod n) ^ k) =
        -((ξ0 ^ (2 * k * 3 ^ k))⁻¹ * (dft ξ0 y 1 ^ (3 ^ k))⁻¹) := by
      calc dft ξ0 y (-(3 : ZMod n) ^ k)
          = (ξ0 ^ (2 * k * 3 ^ k) * dft ξ0 y 1 ^ (3 ^ k))⁻¹ *
              (ξ0 ^ (2 * k * 3 ^ k) * dft ξ0 y 1 ^ (3 ^ k) * dft ξ0 y (-(3 : ZMod n) ^ k)) := by
            rw [← mul_assoc, inv_mul_cancel₀ hA, one_mul]
        _ = -((ξ0 ^ (2 * k * 3 ^ k))⁻¹ * (dft ξ0 y 1 ^ (3 ^ k))⁻¹) := by
            rw [h3, mul_inv]; ring
    rw [hX, inv_pow ξ0, ← inv_pow (dft ξ0 y 1), hθinv, mul_pow, ← pow_mul]
    ring

/-! ## 3. Theorem 3.4(b) (row 11b), EXACT -/

section B

variable {n : ℕ} [NeZero n]

/-- The two inversion weights on the top layer at `t = 0` and `t = 1`. -/
theorem H13_w0 {F : Type*} [Field F] (ξ0 : F) (k : ZMod n) : ((ξ0 ^ k.val)⁻¹) ^ (0 : ZMod n).val = 1 := by
  rw [ZMod.val_zero, pow_zero]

theorem H13_w1 {F : Type*} [Field F] (h1n : 1 < n) (ξ0 : F) (k : ZMod n) :
    ((ξ0 ^ k.val)⁻¹) ^ (1 : ZMod n).val = (ξ0 ^ k.val)⁻¹ := by
  rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt h1n, pow_one]

/-- `x^- = (x - x^Q)/2 = (y_t - y_{t+m})/2` and `x^+ = (y_t + y_{t+m})/2` for `x = y_t` (via (L1): `y_{t+m} = y_t^Q`). -/
theorem H13_yMinus_eq {e : ℕ} (hne : n = 2 ^ e) (he : 3 ≤ e) (y : ZMod n → GaloisField 3 (n / 2))
    (hL1 : L1 3 ((2 : ℕ) : ℤ) y) (t : ZMod n) : yMinus n (y t) = (y t - y (t + half n)) / 2 := by
  unfold yMinus bar; rw [H4_L1_half hne he y hL1 t]

theorem H13_yPlus_eq {e : ℕ} (hne : n = 2 ^ e) (he : 3 ≤ e) (y : ZMod n → GaloisField 3 (n / 2))
    (hL1 : L1 3 ((2 : ℕ) : ℤ) y) (t : ZMod n) : yPlus n (y t) = (y t + y (t + half n)) / 2 := by
  unfold yPlus bar; rw [H4_L1_half hne he y hL1 t]

end B

/-- Row 11b — Theorem 3.4(b) (s3_pow2.tex:108-111): for every solution, with `θ = ŷ(ξ_0)` and `ν = θ^{1+q}`,
`y_0^- = n^{-1} Λ_ν(θ + Tθ)` and `y_1^- = n^{-1} Λ'_ν(θ - Tθ)`. EXACT (Fourier inversion proved here, H13_inversion). -/
theorem thm_3_4_b_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 4 ≤ e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2) :
    yMinus n (y 0) = (n : GaloisField 3 (n / 2))⁻¹ *
        Lam n ξ0 (dft ξ0 y 1 ^ (1 + qq n)) (dft ξ0 y 1 + Tmap n ξ0 (dft ξ0 y 1)) ∧
      yMinus n (y 1) = (n : GaloisField 3 (n / 2))⁻¹ *
        Lam' n ξ0 (dft ξ0 y 1 ^ (1 + qq n)) (dft ξ0 y 1 - Tmap n ξ0 (dft ξ0 y 1)) := by
  have hn : Even n := H4_even_of_pow2 hne (by omega)
  obtain ⟨-, -, -, -, -, -, hξ0Q, hhalf, hξ, -, -, -, -, hnF, hnpos⟩ := H8_setup n e hne he ξ0 hξ0
  have h1n : 1 < n := by obtain ⟨t8, ht1, hnt⟩ := H4_shape hne (by omega); omega
  have h2 := H9_two_ne_zero_GF (n / 2)
  have hω1 := hξ0.pow_eq_one
  have hNF := hy
  obtain ⟨hL1, hL3, hRm, _⟩ := hy
  obtain ⟨-, hθQ1⟩ := H4_NF_theta hne (by omega) hξ0 y hL1 hL3 hRm
  obtain ⟨-, -, -, -, -, hVθ, -, -, -, hνfacts, -⟩ := sec_3_2_setup_proved n e hne he ξ0 hξ0
  have hν := (hνfacts _ hθQ1).1
  have hθV : dft ξ0 y 1 ∈ (Vsp n : Set (GaloisField 3 (n / 2))) := ((hVθ _).mpr hθQ1).1
  obtain ⟨hTopV, hTopY⟩ := eq_top_all_V_proved n e hne he ξ0 hξ0 _ hν
  obtain ⟨hY0, hY1⟩ := hTopV _ hθV
  have hvals := hTopY y hNF rfl
  have hinv := H13_inversion hξ0 hnF y
  constructor
  · rw [H13_yMinus_eq hne (by omega) y hL1, H13_minus_sum h2 hω1 hhalf y hinv, H13_top_sum hne (by omega),
      ← hY0]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [H13_w0, H13_w0, (hvals j).1, (hvals j).2]
    ring
  · rw [H13_yMinus_eq hne (by omega) y hL1, H13_minus_sum h2 hω1 hhalf y hinv, H13_top_sum hne (by omega),
      ← hY1]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [H13_w1 h1n, H13_w1 h1n, (hvals j).1, (hvals j).2, H4_pow_val_neg hω1, inv_inv, H4_E3 hω1]
    ring

/-! ## 4. Theorem 3.4(c) (row 11c), EXACT -/

section C

/-- (eq:qmodn) as a cast: `q ≡ 1 + n/2 (mod n)`. -/
theorem H13_qq_cast {n e : ℕ} [NeZero n] (hne : n = 2 ^ e) (he : 4 ≤ e) :
    ((qq n : ℕ) : ZMod n) = 1 + half n := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 4 := ⟨e - 4, by omega⟩
  obtain ⟨m, hm⟩ := H3_three_pow k
  have hdivs := H3_divs (k + 1) n hne
  have hq : qq n = 1 + n / 2 + n * m := by
    rw [qq, hdivs.2.2, hm, hdivs.1, hne]; ring
  rw [hq]
  show ((1 + n / 2 + n * m : ℕ) : ZMod n) = 1 + ((n / 2 : ℕ) : ZMod n)
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero, Nat.cast_one]

/-- `3^j + n/2 = 3^{j + n/8}` in `ℤ/n` (the point `-ξ` of `ξ = ξ_0^{3^j}` lies in the same orbit, at `q ξ`). -/
theorem H13_pow_add_half {n e : ℕ} [NeZero n] (hne : n = 2 ^ e) (he : 4 ≤ e) (j : ℕ) :
    (3 : ZMod n) ^ j + half n = 3 ^ (j + n / 8) := by
  have hn : Even n := H4_even_of_pow2 hne (by omega)
  have h3 : (3 : ZMod n) ^ (n / 8) = 1 + half n := by
    rw [← H13_qq_cast hne he, qq, Nat.cast_pow, Nat.cast_ofNat]
  have hodd := H7_odd_mul_half hn (3 ^ j) (Odd.pow (by decide))
  rw [Nat.cast_pow, Nat.cast_ofNat] at hodd
  rw [pow_add, h3, mul_add, mul_one, hodd]

theorem H13_pair_pos {F : Type*} [Field F] (n : ℕ) (θ : F) (j : ℕ) :
    θ ^ (3 ^ j) * θ ^ (3 ^ (j + n / 8)) = (θ ^ (1 + qq n)) ^ (3 ^ j) := by
  rw [← pow_add, ← pow_mul]; congr 1; unfold qq; ring

theorem H13_pair_neg {F : Type*} [Field F] (n : ℕ) (θ : F) (j : ℕ) :
    θ ^ (qq n * 3 ^ j) * θ ^ (qq n * 3 ^ (j + n / 8)) = (θ ^ (1 + qq n)) ^ (qq n * 3 ^ j) := by
  rw [← pow_add, ← pow_mul]; congr 1; unfold qq; ring

/-- `1/2 = -1` in characteristic 3. -/
theorem H13_div_two {m : ℕ} (x : GaloisField 3 m) : x / 2 = -x := by
  rw [H8_two_eq_neg_one, div_neg, div_one]

/-- `x̄ = x^+ - x^-`. -/
theorem H13_bar_eq {m : ℕ} (n : ℕ) (x : GaloisField 3 m) : bar n x = yPlus n x - yMinus n x := by
  linear_combination H9_split n x - H9_two_yPlus n x

/-- The lower-layer values `ŷ(k)`, `k` even, depend only on `(ν, S, ŷ(1))` (proof of Thm 3.4(c), s3_pow2.tex:179-184):
the top-layer values enter the layer recursion only through `ŷ(ρ)ŷ(-ρ) = ŷ(ρ)ŷ(ρ^q)`, a function of `ν`. Formally:
`k ↦ (ŷ' on odd k, ŷ on even k)` is a fixed point of the recursion of `y'`, hence equals `ŷ'` (H4_fix_unique). -/
theorem H13_even_agree (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 4 ≤ e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n)
    (y y' : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2) (hy' : y' ∈ NFSet n 2)
    (hν : dft ξ0 y 1 ^ (1 + qq n) = dft ξ0 y' 1 ^ (1 + qq n)) (hS : S y = S y')
    (hc : dft ξ0 y 0 = dft ξ0 y' 0) : ∀ k : ZMod n, ¬ Odd k.val → dft ξ0 y k = dft ξ0 y' k := by
  classical
  obtain ⟨-, -, hord, -, -, horb, hdisj, -⟩ := thm_3_1_step1_proved n e hne (by omega)
  obtain ⟨t8, ht1, hnt⟩ := H4_shape hne (by omega)
  have hn : Even n := ⟨4 * t8, by omega⟩
  have h4 : 4 ∣ n := ⟨2 * t8, by omega⟩
  have hm2 : Even (n / 2) := ⟨2 * t8, by omega⟩
  have hω1 := hξ0.pow_eq_one
  have hm : ξ0 ^ (n / 2) = -1 := H4_pow_half hξ0 hn (by omega)
  have hdisj' := H4_neg_ne hdisj
  have hord' : orderOf (3 : ZMod n) = n / 4 := by
    rw [hord]
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 3 := ⟨e - 3, by omega⟩
    rw [show k + 3 - 2 = k + 1 by omega, hne, show 2 ^ (k + 3) = 2 ^ (k + 1) * 4 by ring,
      Nat.mul_div_cancel _ (by norm_num)]
  have hwd : ∀ θ : GaloisField 3 (n / 2), θ ^ (QQ n - 1) = -1 →
      ∀ i j : ℕ, (3 : ZMod n) ^ i = 3 ^ j → H4_t ξ0 θ i = H4_t ξ0 θ j := fun θ hθ =>
    H4_t_wd hord' (by omega) (fun k => H4_step2b h4 hω1 hm (H4_three_pow_quarter hne (by omega)) hθ k)
  have h2 := H9_two_ne_zero_GF (n / 2)
  have hNF := hy
  have hNF' := hy'
  obtain ⟨hL1, hL3, hRm, hL4⟩ := hy
  obtain ⟨hL1', hL3', hRm', hL4'⟩ := hy'
  have a1 : F1 3 2 ξ0 (dft ξ0 y) := (H4_F1_iff _ _).mpr (H13_F1 hω1 y hL1)
  have a3 : F3 ξ0 (dft ξ0 y) := H4_NF_F3 hne (by omega) hξ0 y hL3 hRm
  have a4 : F4 (dft ξ0 y) := H13_F4 hn h2 hξ0 y hL4
  have b1 : F1 3 2 ξ0 (dft ξ0 y') := (H4_F1_iff _ _).mpr (H13_F1 hω1 y' hL1')
  have b3 : F3 ξ0 (dft ξ0 y') := H4_NF_F3 hne (by omega) hξ0 y' hL3' hRm'
  have b4 : F4 (dft ξ0 y') := H13_F4 hn h2 hξ0 y' hL4'
  have fx := H4_G_fixed hne (by omega) hξ0 horb hdisj'
    (hwd _ (H4_G_theta hne (by omega) hξ0 ((H4_F1_iff _ _).mp a1) a3)) a1 a3 a4
  have fx' := H4_G_fixed hne (by omega) hξ0 horb hdisj'
    (hwd _ (H4_G_theta hne (by omega) hξ0 ((H4_F1_iff _ _).mp b1) b3)) b1 b3 b4
  -- the pair products `ŷ(z) ŷ(z + m)`, `z` odd, depend only on `ν`
  obtain ⟨-, -, -, -, -, -, -, -, -, hνfacts, -⟩ := sec_3_2_setup_proved n e hne he ξ0 hξ0
  have hθQ1 := (H4_NF_theta hne (by omega) hξ0 y hL1 hL3 hRm).2
  obtain ⟨-, hTopY⟩ := eq_top_all_V_proved n e hne he ξ0 hξ0 _ (hνfacts _ hθQ1).1
  have hv := hTopY y hNF rfl
  have hv' := hTopY y' hNF' hν.symm
  have hpair : ∀ z : ZMod n, Odd z.val →
      dft ξ0 y z * dft ξ0 y (z + half n) = dft ξ0 y' z * dft ξ0 y' (z + half n) := by
    intro z hz
    obtain ⟨j, hj | hj⟩ := H4_odd_cases horb z hz
    · rw [hj, H13_pow_add_half hne he, (hv j).1, (hv (j + n / 8)).1, (hv' j).1, (hv' (j + n / 8)).1]
      have e1 := H13_pair_pos n (dft ξ0 y 1) j
      have e2 := H13_pair_pos n (dft ξ0 y' 1) j
      have e3 : (dft ξ0 y 1 ^ (1 + qq n)) ^ (3 ^ j) = (dft ξ0 y' 1 ^ (1 + qq n)) ^ (3 ^ j) := by rw [hν]
      linear_combination (ξ0 ^ (2 * j * 3 ^ j) * ξ0 ^ (2 * (j + n / 8) * 3 ^ (j + n / 8))) * (e1 - e2 + e3)
    · have hzm : -(3 : ZMod n) ^ j + half n = -(3 : ZMod n) ^ (j + n / 8) := by
        rw [← H13_pow_add_half hne he, neg_add, H4_neg_half hn]
      rw [hj, hzm, (hv j).2, (hv (j + n / 8)).2, (hv' j).2, (hv' (j + n / 8)).2]
      have e1 := H13_pair_neg n (dft ξ0 y 1) j
      have e2 := H13_pair_neg n (dft ξ0 y' 1) j
      have e3 : (dft ξ0 y 1 ^ (1 + qq n)) ^ (qq n * 3 ^ j) = (dft ξ0 y' 1 ^ (1 + qq n)) ^ (qq n * 3 ^ j) := by
        rw [hν]
      linear_combination ((ξ0⁻¹) ^ (2 * j * 3 ^ j) * ((dft ξ0 y 1 ^ (1 + qq n))⁻¹) ^ (3 ^ j) *
        (ξ0⁻¹) ^ (2 * (j + n / 8) * 3 ^ (j + n / 8)) * ((dft ξ0 y 1 ^ (1 + qq n))⁻¹) ^ (3 ^ (j + n / 8))) *
          (e1 - e2 + e3)
  have hSm : dft ξ0 y (half n) = dft ξ0 y' (half n) := by
    rw [H4_S_eq_dft hn (by omega) hξ0, H4_S_eq_dft hn (by omega) hξ0, hS]
  -- the mixed function is a fixed point of the recursion of `y'`
  let g : ZMod n → GaloisField 3 (n / 2) := fun k => if Odd k.val then dft ξ0 y' k else dft ξ0 y k
  have hg : H4_Gam (H4_top ξ0 (dft ξ0 y' 1)) (dft ξ0 y' (half n)) (dft ξ0 y' 0) g = g := by
    funext k
    rw [H4_Gam_apply]
    by_cases hodd : Odd k.val
    · have := congrFun fx' k
      rw [H4_Gam_apply, ite_eq_left hodd] at this
      simp only [g, ite_eq_left hodd]
      exact this
    · rw [ite_eq_right hodd]
      by_cases hk0 : k = 0
      · rw [ite_eq_left hk0]
        simp only [g, ite_eq_right hodd]
        rw [hk0, hc]
      · rw [ite_eq_right hk0]
        have hk := congrFun fx k
        rw [H4_Gam_apply, ite_eq_right hodd, ite_eq_right hk0] at hk
        have hpar : Odd (((k.val / 2 : ℕ) : ZMod n) + half n).val ↔ Odd ((k.val / 2 : ℕ) : ZMod n).val :=
          H9_odd_add_half hn hm2 _
        simp only [g, ite_eq_right hodd]
        by_cases hz : Odd ((k.val / 2 : ℕ) : ZMod n).val
        · rw [ite_eq_left hz, ite_eq_left (hpar.mpr hz), ← hk, hSm, mul_assoc, mul_assoc, hpair _ hz]
        · rw [ite_eq_right hz, ite_eq_right (fun h => hz (hpar.mp h)), ← hk, hSm]
  have e1 := H4_fix_unique hne (by omega) _ _ _ g hg
  have e2 := H4_fix_unique hne (by omega) _ _ _ _ fx'
  intro k hk
  have := congrFun (e1.trans e2.symm) k
  simp only [g, ite_eq_right hk] at this
  exact this

/-- Part (A) of row 11c: the conic identity and the components `θ_± = (θ ± Tθ)/2 = -(θ ± Tθ)`. -/
theorem H13_c_A (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 4 ≤ e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) :
    ∀ x ∈ (Vsp n : Set (GaloisField 3 (n / 2))), x ^ (1 + qq n) = -iota n ξ0 * x * Tmap n ξ0 x ∧
      ((x + Tmap n ξ0 x) / 2) ^ 2 - ((x - Tmap n ξ0 x) / 2) ^ 2 = iota n ξ0 * x ^ (1 + qq n) ∧
      (x + Tmap n ξ0 x) / 2 ∈ Vplus n ξ0 ∧ (x - Tmap n ξ0 x) / 2 ∈ Vminus n ξ0 ∧
      x + Tmap n ξ0 x = -((x + Tmap n ξ0 x) / 2) ∧ x - Tmap n ξ0 x = -((x - Tmap n ξ0 x) / 2) := by
  intro x hx
  obtain ⟨hQ, hqodd, hQodd, hι2, hιq, -, -, -, -, -, -, -, -, -, -⟩ := H8_setup n e hne he ξ0 hξ0
  obtain ⟨hp, hm⟩ := H8_dec_mem n hQ hqodd hQodd ξ0 hι2 hιq x hx
  rw [H13_div_two, H13_div_two]
  refine ⟨?_, ?_, hp, hm, by rw [neg_neg], by rw [neg_neg]⟩
  · unfold Tmap; rw [pow_add, pow_one]; linear_combination (x * x ^ qq n) * hι2
  · unfold Tmap; rw [pow_add, pow_one]
    linear_combination (iota n ξ0 * x * x ^ qq n) * (H8_three_eq_zero (F := GaloisField 3 (n / 2)))

/-- Part (C) of row 11c: `T` maps parameters to parameters and keeps `ν`. -/
theorem H13_c_C (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 4 ≤ e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) : ∀ x : GaloisField 3 (n / 2), x ^ (QQ n - 1) = -1 →
      Tmap n ξ0 x ^ (QQ n - 1) = -1 ∧ Tmap n ξ0 x ^ (1 + qq n) = x ^ (1 + qq n) := by
  intro x hx
  obtain ⟨hQ, hqodd, hQodd, hι2, hιq, -, -, -, -, -, -, -, hq9, -, -⟩ := H8_setup n e hne he ξ0 hξ0
  obtain ⟨-, -, -, -, -, hVθ, -⟩ := sec_3_2_setup_proved n e hne he ξ0 hξ0
  have hxV := (hVθ x).mpr hx
  have hTV := H8_T_mem n hQ hqodd ξ0 hιq x hxV.1
  have hTT := H8_TT n hQ ξ0 hι2 hιq x hxV.1
  have hT0 : Tmap n ξ0 x ≠ 0 := by
    intro h0; apply hxV.2; rw [← hTT, h0]; unfold Tmap; rw [zero_pow (by omega), mul_zero]
  refine ⟨(hVθ _).mp ⟨hTV, hT0⟩, ?_⟩
  have hxQ : x ^ QQ n = -x := hxV.1
  have hxqq : (x ^ qq n) ^ qq n = -x := by rw [← pow_mul, ← sq, ← hQ, hxQ]
  have hιqq : iota n ξ0 ^ (1 + qq n) = -1 := by rw [pow_add, pow_one, hιq, ← sq, hι2]
  unfold Tmap
  rw [mul_pow, hιqq, pow_add (x ^ qq n), pow_one, hxqq, pow_add x, pow_one]
  ring

/-- Part (B) of row 11c: `y_0^+, y_1^+` depend only on `(ν, S, ŷ(1))`, `y_0` only on these and `θ_+`, `y_1` only on
these and `θ_-`. -/
theorem H13_c_B (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 4 ≤ e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) :
    ∀ y ∈ NFSet n 2, ∀ y' ∈ NFSet n 2, dft ξ0 y 1 ^ (1 + qq n) = dft ξ0 y' 1 ^ (1 + qq n) → S y = S y' →
      dft ξ0 y 0 = dft ξ0 y' 0 →
        yPlus n (y 0) = yPlus n (y' 0) ∧ yPlus n (y 1) = yPlus n (y' 1) ∧
        ((dft ξ0 y 1 + Tmap n ξ0 (dft ξ0 y 1)) / 2 = (dft ξ0 y' 1 + Tmap n ξ0 (dft ξ0 y' 1)) / 2 → y 0 = y' 0) ∧
        ((dft ξ0 y 1 - Tmap n ξ0 (dft ξ0 y 1)) / 2 = (dft ξ0 y' 1 - Tmap n ξ0 (dft ξ0 y' 1)) / 2 →
          y 1 = y' 1) := by
  intro y hy y' hy' hν hS hc
  have hn : Even n := H4_even_of_pow2 hne (by omega)
  obtain ⟨-, -, -, -, -, -, -, hhalf, -, -, -, -, -, hnF, -⟩ := H8_setup n e hne he ξ0 hξ0
  have h2 := H9_two_ne_zero_GF (n / 2)
  have hω1 := hξ0.pow_eq_one
  have hagree := H13_even_agree n e hne he ξ0 hξ0 y y' hy hy' hν hS hc
  have hb := thm_3_4_b_proved n e hne he ξ0 hξ0 y hy
  have hb' := thm_3_4_b_proved n e hne he ξ0 hξ0 y' hy'
  obtain ⟨hL1, -, -, -⟩ := hy
  obtain ⟨hL1', -, -, -⟩ := hy'
  have hplus : ∀ t, yPlus n (y t) = yPlus n (y' t) := by
    intro t
    rw [H13_yPlus_eq hne (by omega) y hL1, H13_yPlus_eq hne (by omega) y' hL1',
      H13_plus_sum h2 hω1 hhalf y (H13_inversion hξ0 hnF y), H13_plus_sum h2 hω1 hhalf y' (H13_inversion hξ0 hnF y')]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [hagree k (Finset.mem_filter.mp hk).2]
  refine ⟨hplus 0, hplus 1, fun hθp => ?_, fun hθm => ?_⟩
  · rw [← H9_split n (y 0), ← H9_split n (y' 0), hplus 0, hb.1, hb'.1, hν, (div_left_inj' h2).mp hθp]
  · rw [← H9_split n (y 1), ← H9_split n (y' 1), hplus 1, hb.2, hb'.2, hν, (div_left_inj' h2).mp hθm]

/-- Part (D) of row 11c: the parameter `Tθ` (same signs) gives `y_0(Tθ) = y_0(θ)`, `y_1(Tθ) = \overline{y_1(θ)}`. -/
theorem H13_c_D (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 4 ≤ e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) :
    ∀ y ∈ NFSet n 2, ∀ y' ∈ NFSet n 2, paramMap n ξ0 y' = (Tmap n ξ0 (dft ξ0 y 1), S y, dft ξ0 y 0) →
      y' 0 = y 0 ∧ y' 1 = bar n (y 1) := by
  intro y hy y' hy' hpm
  simp only [paramMap, Prod.mk.injEq] at hpm
  obtain ⟨hθ', hS', hc'⟩ := hpm
  obtain ⟨hQ, -, -, hι2, hιq, -, -, -, -, -, -, -, -, -, -⟩ := H8_setup n e hne he ξ0 hξ0
  obtain ⟨-, -, -, -, -, hVθ, -⟩ := sec_3_2_setup_proved n e hne he ξ0 hξ0
  have hNF := hy
  obtain ⟨hL1, hL3, hRm, -⟩ := hy
  have hθQ1 := (H4_NF_theta hne (by omega) hξ0 y hL1 hL3 hRm).2
  have hθV := ((hVθ _).mpr hθQ1).1
  have hTT := H8_TT n hQ ξ0 hι2 hιq _ hθV
  have hν' : dft ξ0 y' 1 ^ (1 + qq n) = dft ξ0 y 1 ^ (1 + qq n) := by
    rw [hθ']; exact (H13_c_C n e hne he ξ0 hξ0 _ hθQ1).2
  obtain ⟨hp0, hp1, -, -⟩ := H13_c_B n e hne he ξ0 hξ0 y' hy' y hNF hν' hS' hc'
  have hb := thm_3_4_b_proved n e hne he ξ0 hξ0 y hNF
  have hb' := thm_3_4_b_proved n e hne he ξ0 hξ0 y' hy'
  constructor
  · rw [← H9_split n (y' 0), ← H9_split n (y 0), hp0, hb'.1, hb.1, hν', hθ', hTT,
      add_comm (Tmap n ξ0 (dft ξ0 y 1)) (dft ξ0 y 1)]
  · rw [H13_bar_eq, ← H9_split n (y' 1), hp1, hb'.2, hb.2, hν', hθ', hTT, H8_Lam'_sub, H8_Lam'_sub]
    ring

end C

/-- Row 11c — Theorem 3.4(c) (s3_pow2.tex:112-115) and its proof's identity (:175, :204): `θ^{1+q} = -ι θ T(θ)` for
every `θ ∈ V`, i.e. `θ_+^2 - θ_-^2 = ιν` with `θ_± = (θ ± Tθ)/2 ∈ V_±` (and `θ + Tθ = -θ_+`, `θ - Tθ = -θ_-`, :121);
`y_0^+`, `y_1^+` depend only on `(ν, S, ŷ(1))`; `y_0` only on `(ν, S, ŷ(1), θ_+)`, `y_1` only on `(ν, S, ŷ(1), θ_-)`;
`T` sends parameters to parameters and keeps `ν`; `y_0(Tθ) = y_0(θ)` and `y_1(Tθ) = \overline{y_1(θ)}` (same signs).
EXACT ((F1), (F3), (F4) of `ŷ` are derived here from (L1), (L3)+`R(m)=1`, (L4); inversion is proved here). -/
theorem thm_3_4_c_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 4 ≤ e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) :
    let T := Tmap n ξ0
    let θ : (ZMod n → GaloisField 3 (n / 2)) → GaloisField 3 (n / 2) := fun y => dft ξ0 y 1
    (∀ x ∈ Vsp n, x ^ (1 + qq n) = -iota n ξ0 * x * T x ∧
      ((x + T x) / 2) ^ 2 - ((x - T x) / 2) ^ 2 = iota n ξ0 * x ^ (1 + qq n) ∧
      (x + T x) / 2 ∈ Vplus n ξ0 ∧ (x - T x) / 2 ∈ Vminus n ξ0 ∧
      x + T x = -((x + T x) / 2) ∧ x - T x = -((x - T x) / 2)) ∧
    (∀ y ∈ NFSet n 2, ∀ y' ∈ NFSet n 2, θ y ^ (1 + qq n) = θ y' ^ (1 + qq n) → S y = S y' →
      dft ξ0 y 0 = dft ξ0 y' 0 →
        yPlus n (y 0) = yPlus n (y' 0) ∧ yPlus n (y 1) = yPlus n (y' 1) ∧
        ((θ y + T (θ y)) / 2 = (θ y' + T (θ y')) / 2 → y 0 = y' 0) ∧
        ((θ y - T (θ y)) / 2 = (θ y' - T (θ y')) / 2 → y 1 = y' 1)) ∧
    (∀ x : GaloisField 3 (n / 2), x ^ (QQ n - 1) = -1 →
      T x ^ (QQ n - 1) = -1 ∧ T x ^ (1 + qq n) = x ^ (1 + qq n)) ∧
    (∀ y ∈ NFSet n 2, ∀ y' ∈ NFSet n 2, paramMap n ξ0 y' = (T (θ y), S y, dft ξ0 y 0) →
      y' 0 = y 0 ∧ y' 1 = bar n (y 1)) := by
  intro T θ
  exact ⟨H13_c_A n e hne he ξ0 hξ0, H13_c_B n e hne he ξ0 hξ0, H13_c_C n e hne he ξ0 hξ0,
    H13_c_D n e hne he ξ0 hξ0⟩

/-! ## 5. Corollary 3.5 (rows 12a, 12b), parametrized by `prop_2_4_bij` (surjectivity of `y ↦ (θ, S, ŷ(1))`) -/

section Cor

theorem H13_Lam_neg (n : ℕ) (ξ0 ν u : GaloisField 3 (n / 2)) : Lam n ξ0 ν (-u) = -Lam n ξ0 ν u := by
  have h := H8_Lam_sub n ξ0 ν 0 u
  rw [zero_sub, H8_Lam_zero, zero_sub] at h
  exact h

theorem H13_Lam'_neg (n : ℕ) (ξ0 ν u : GaloisField 3 (n / 2)) : Lam' n ξ0 ν (-u) = -Lam' n ξ0 ν u := by
  have h := H8_Lam'_sub n ξ0 ν 0 u
  rw [zero_sub, H8_Lam'_zero, zero_sub] at h
  exact h

/-- The orbit `{±θ, ±Tθ}` of `⟨T, θ ↦ -θ⟩`, read on the components: `θ' ∈ {θ, -θ, Tθ, -Tθ}` iff
`θ' ± Tθ' = ±(θ ± Tθ)` (independent signs). -/
theorem H13_P_iff (n : ℕ) (hqodd : Odd (qq n)) (ξ0 θ θ' : GaloisField 3 (n / 2))
    (hTT : Tmap n ξ0 (Tmap n ξ0 θ) = θ) :
    θ' ∈ ({θ, -θ, Tmap n ξ0 θ, -Tmap n ξ0 θ} : Set (GaloisField 3 (n / 2))) ↔
      ((θ' + Tmap n ξ0 θ' = θ + Tmap n ξ0 θ ∨ θ' + Tmap n ξ0 θ' = -(θ + Tmap n ξ0 θ)) ∧
        (θ' - Tmap n ξ0 θ' = θ - Tmap n ξ0 θ ∨ θ' - Tmap n ξ0 θ' = -(θ - Tmap n ξ0 θ))) := by
  have h3 := H8_three_eq_zero (F := GaloisField 3 (n / 2))
  have hTn := H8_T_neg n hqodd ξ0
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h | h | h) <;> rw [h]
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · exact ⟨Or.inr (by rw [hTn]; ring), Or.inr (by rw [hTn]; ring)⟩
    · exact ⟨Or.inl (by rw [hTT]; ring), Or.inr (by rw [hTT]; ring)⟩
    · exact ⟨Or.inr (by rw [hTn, hTT]; ring), Or.inl (by rw [hTn, hTT]; ring)⟩
  · rintro ⟨h0 | h0, h1 | h1⟩
    · left; linear_combination (-1 : GaloisField 3 (n / 2)) * (h0 + h1) + (θ' - θ) * h3
    · right; right; left
      linear_combination (-1 : GaloisField 3 (n / 2)) * (h0 + h1) + (θ' - Tmap n ξ0 θ) * h3
    · right; right; right
      linear_combination (-1 : GaloisField 3 (n / 2)) * (h0 + h1) + (θ' + Tmap n ξ0 θ) * h3
    · right; left; linear_combination (-1 : GaloisField 3 (n / 2)) * (h0 + h1) + (θ' + θ) * h3

/-- Every point of `{±θ, ±Tθ}` is a parameter with the same `ν`. -/
theorem H13_nu_of_mem (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 4 ≤ e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) (θ θ' : GaloisField 3 (n / 2)) (hθ : θ ^ (QQ n - 1) = -1)
    (hmem : θ' ∈ ({θ, -θ, Tmap n ξ0 θ, -Tmap n ξ0 θ} : Set (GaloisField 3 (n / 2)))) :
    θ' ^ (1 + qq n) = θ ^ (1 + qq n) ∧ θ' ^ (QQ n - 1) = -1 := by
  obtain ⟨-, hqodd, hQodd, -⟩ := H8_setup n e hne he ξ0 hξ0
  have hev : Even (1 + qq n) := by obtain ⟨r, hr⟩ := hqodd; exact ⟨r + 1, by omega⟩
  have hev' : Even (QQ n - 1) := by obtain ⟨r, hr⟩ := hQodd; exact ⟨r, by omega⟩
  have hC := H13_c_C n e hne he ξ0 hξ0 θ hθ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h | h <;> rw [h]
  · exact ⟨rfl, hθ⟩
  · exact ⟨hev.neg_pow θ, by rw [hev'.neg_pow]; exact hθ⟩
  · exact ⟨hC.2, hC.1⟩
  · exact ⟨by rw [hev.neg_pow]; exact hC.2, by rw [hev'.neg_pow]; exact hC.1⟩

/-- Proof of Cor 3.5(ii), first part: for a solution `y` of Xia's system and a norm-free `y'` with the same signs,
`y'` solves Xia's system with the same `ν` iff `ŷ'(ξ_0) ∈ {±θ, ±Tθ}` (norm conditions + Thm 3.4(b),(c),(d)). -/
theorem H13_ii_mem (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 4 ≤ e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n)
    (y y' : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2) (hy' : y' ∈ NFSet n 2)
    (hn0 : Nm n (y 0) = -1) (hn1 : Nm n (y 1) = -1) (hS : S y' = S y) (hc : dft ξ0 y' 0 = dft ξ0 y 0) :
    (y' ∈ XiaSet n 2 ∧ dft ξ0 y' 1 ^ (1 + qq n) = dft ξ0 y 1 ^ (1 + qq n)) ↔
      dft ξ0 y' 1 ∈ ({dft ξ0 y 1, -dft ξ0 y 1, Tmap n ξ0 (dft ξ0 y 1), -Tmap n ξ0 (dft ξ0 y 1)} :
        Set (GaloisField 3 (n / 2))) := by
  obtain ⟨hQ, hqodd, hQodd, hι2, hιq, -, -, -, -, -, -, -, -, hnF, -⟩ := H8_setup n e hne he ξ0 hξ0
  obtain ⟨-, -, -, -, -, hVθ, -, -, -, hνfacts, hNm⟩ := sec_3_2_setup_proved n e hne he ξ0 hξ0
  have hNF := hy
  have hNF' := hy'
  obtain ⟨hL1, hL3, hRm, -⟩ := hy
  obtain ⟨hL1', hL3', hRm', -⟩ := hy'
  have hθQ1 := (H4_NF_theta hne (by omega) hξ0 y hL1 hL3 hRm).2
  have hθ'Q1 := (H4_NF_theta hne (by omega) hξ0 y' hL1' hL3' hRm').2
  have hθV := ((hVθ _).mpr hθQ1).1
  have hθ'V := ((hVθ _).mpr hθ'Q1).1
  have hTT := H8_TT n hQ ξ0 hι2 hιq _ hθV
  have hTT' := H8_TT n hQ ξ0 hι2 hιq _ hθ'V
  have hTV := H8_T_mem n hQ hqodd ξ0 hιq _ hθV
  have hTV' := H8_T_mem n hQ hqodd ξ0 hιq _ hθ'V
  obtain ⟨hνq1, -, hνQ⟩ := hνfacts _ hθQ1
  obtain ⟨hinjp, hinjm, -⟩ := thm_3_4_d_proved n e hne he ξ0 hξ0 _ hνQ hνq1
  have hb := thm_3_4_b_proved n e hne he ξ0 hξ0 y hNF
  have hb' := thm_3_4_b_proved n e hne he ξ0 hξ0 y' hNF'
  have hn0' : (n : GaloisField 3 (n / 2))⁻¹ ≠ 0 := inv_ne_zero hnF
  have mp : ∀ x, x ∈ Vsp n → Tmap n ξ0 (Tmap n ξ0 x) = x → Tmap n ξ0 x ∈ Vsp n →
      x + Tmap n ξ0 x ∈ Vplus n ξ0 :=
    fun x hx hxx hTx => ⟨H8_V_add n _ _ hx hTx, by rw [H8_T_add, hxx, add_comm]⟩
  have mm : ∀ x, x ∈ Vsp n → Tmap n ξ0 (Tmap n ξ0 x) = x → Tmap n ξ0 x ∈ Vsp n →
      x - Tmap n ξ0 x ∈ Vminus n ξ0 :=
    fun x hx hxx hTx => ⟨H8_V_sub n hQodd _ _ hx hTx, by rw [H8_T_sub n hqodd, hxx]; ring⟩
  have negp : ∀ u, u ∈ Vplus n ξ0 → -u ∈ Vplus n ξ0 :=
    fun u hu => ⟨H8_V_neg n hQodd u hu.1, by rw [H8_T_neg n hqodd, hu.2]⟩
  have negm : ∀ u, u ∈ Vminus n ξ0 → -u ∈ Vminus n ξ0 :=
    fun u hu => ⟨H8_V_neg n hQodd u hu.1, by rw [H8_T_neg n hqodd, hu.2]⟩
  rw [H13_P_iff n hqodd ξ0 _ _ hTT]
  constructor
  · rintro ⟨hy'X, hν'⟩
    obtain ⟨n0', n1'⟩ := H4_xia_norms hne (by omega) y' hy'X
    obtain ⟨hp0, hp1, -, -⟩ := H13_c_B n e hne he ξ0 hξ0 y' hNF' y hNF hν' hS hc
    have hsq0 : yMinus n (y' 0) ^ 2 = yMinus n (y 0) ^ 2 := by
      have a := hNm (y' 0)
      have b := hNm (y 0)
      rw [n0', hp0] at a
      rw [hn0] at b
      linear_combination a - b
    have hsq1 : yMinus n (y' 1) ^ 2 = yMinus n (y 1) ^ 2 := by
      have a := hNm (y' 1)
      have b := hNm (y 1)
      rw [n1', hp1] at a
      rw [hn1] at b
      linear_combination a - b
    rw [hb'.1, hb.1, hν'] at hsq0
    rw [hb'.2, hb.2, hν'] at hsq1
    refine ⟨?_, ?_⟩
    · rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq0 with h | h
      · left; exact hinjp (mp _ hθ'V hTT' hTV') (mp _ hθV hTT hTV) (mul_left_cancel₀ hn0' h)
      · right
        apply hinjp (mp _ hθ'V hTT' hTV') (negp _ (mp _ hθV hTT hTV))
        rw [H13_Lam_neg]
        exact mul_left_cancel₀ hn0' (by rw [h]; ring)
    · rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq1 with h | h
      · left; exact hinjm (mm _ hθ'V hTT' hTV') (mm _ hθV hTT hTV) (mul_left_cancel₀ hn0' h)
      · right
        apply hinjm (mm _ hθ'V hTT' hTV') (negm _ (mm _ hθV hTT hTV))
        rw [H13_Lam'_neg]
        exact mul_left_cancel₀ hn0' (by rw [h]; ring)
  · rintro ⟨h0, h1⟩
    have hν' : dft ξ0 y' 1 ^ (1 + qq n) = dft ξ0 y 1 ^ (1 + qq n) :=
      (H13_nu_of_mem n e hne he ξ0 hξ0 _ _ hθQ1 ((H13_P_iff n hqodd ξ0 _ _ hTT).mpr ⟨h0, h1⟩)).1
    obtain ⟨hp0, hp1, -, -⟩ := H13_c_B n e hne he ξ0 hξ0 y' hNF' y hNF hν' hS hc
    have hsq0 : yMinus n (y' 0) ^ 2 = yMinus n (y 0) ^ 2 := by
      rw [hb'.1, hb.1, hν']
      rcases h0 with h | h
      · rw [h]
      · rw [h, H13_Lam_neg]; ring
    have hsq1 : yMinus n (y' 1) ^ 2 = yMinus n (y 1) ^ 2 := by
      rw [hb'.2, hb.2, hν']
      rcases h1 with h | h
      · rw [h]
      · rw [h, H13_Lam'_neg]; ring
    refine ⟨H4_nf_to_xia hne (by omega) y' hNF' ?_ ?_, hν'⟩
    · rw [hNm, hp0, hsq0, ← hNm, hn0]
    · rw [hNm, hp1, hsq1, ← hNm, hn1]

/-- The solutions of Xia's system above `(ν, S, ŷ(1))` (the set `above ν s1 h1` of row 12b). -/
def H13_above (n : ℕ) [NeZero n] (ξ0 ν s1 h1 : GaloisField 3 (n / 2)) : Set (ZMod n → GaloisField 3 (n / 2)) :=
  {y | y ∈ XiaSet n 2 ∧ dft ξ0 y 1 ^ (1 + qq n) = ν ∧ S y = s1 ∧ dft ξ0 y 0 = h1}

theorem H13_mem_above {n : ℕ} [NeZero n] {ξ0 ν s1 h1 : GaloisField 3 (n / 2)} {y : ZMod n → GaloisField 3 (n / 2)} :
    y ∈ H13_above n ξ0 ν s1 h1 ↔ y ∈ XiaSet n 2 ∧ dft ξ0 y 1 ^ (1 + qq n) = ν ∧ S y = s1 ∧ dft ξ0 y 0 = h1 :=
  Iff.rfl

theorem H13_ii_iff (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 5 ≤ e) (heo : Odd e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n)
    (ν s1 h1 : GaloisField 3 (n / 2)) :
    ∀ y ∈ H13_above n ξ0 ν s1 h1, ∀ y' ∈ NFSet n 2,
      (y' ∈ H13_above n ξ0 ν s1 h1 ↔ paramMap n ξ0 y' ∈ ({dft ξ0 y 1, -dft ξ0 y 1, Tmap n ξ0 (dft ξ0 y 1),
        -Tmap n ξ0 (dft ξ0 y 1)} : Set _) ×ˢ ({s1} ×ˢ {h1})) := by
  intro y hy y' hy'
  obtain ⟨hyX, hyν, hyS, hyc⟩ := H13_mem_above.mp hy
  have hyNF := H4_xia_to_nf hne (by omega) heo y hyX
  obtain ⟨n0, n1⟩ := H4_xia_norms hne (by omega) y hyX
  rw [H13_mem_above]
  simp only [paramMap, Set.mem_prod, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hy'X, hy'ν, hy'S, hy'c⟩
    have hS : S y' = S y := by rw [hy'S, hyS]
    have hc : dft ξ0 y' 0 = dft ξ0 y 0 := by rw [hy'c, hyc]
    exact ⟨(H13_ii_mem n e hne (by omega) ξ0 hξ0 y y' hyNF hy' n0 n1 hS hc).mp
      ⟨hy'X, by rw [hy'ν, hyν]⟩, hy'S, hy'c⟩
  · rintro ⟨hθ', hy'S, hy'c⟩
    have hS : S y' = S y := by rw [hy'S, hyS]
    have hc : dft ξ0 y' 0 = dft ξ0 y 0 := by rw [hy'c, hyc]
    obtain ⟨hX, hν'⟩ := (H13_ii_mem n e hne (by omega) ξ0 hξ0 y y' hyNF hy' n0 n1 hS hc).mpr hθ'
    exact ⟨hX, by rw [hν', hyν], hy'S, hy'c⟩

/-- `|{θ, -θ, Tθ, -Tθ}| ∈ {2, 4}` for `θ ≠ 0`, `Tθ ≠ 0` (characteristic 3: `x ≠ -x` for `x ≠ 0`). -/
theorem H13_P_card (n : ℕ) (θ Tθ : GaloisField 3 (n / 2)) (hθ : θ ≠ 0) (hT : Tθ ≠ 0) :
    ({θ, -θ, Tθ, -Tθ} : Set (GaloisField 3 (n / 2))).ncard = 2 ∨
      ({θ, -θ, Tθ, -Tθ} : Set (GaloisField 3 (n / 2))).ncard = 4 := by
  have hne : ∀ x : GaloisField 3 (n / 2), x ≠ 0 → x ≠ -x := fun x hx h => hx (H8_eq_zero_of_eq_neg x h)
  by_cases h1 : Tθ = θ
  · left
    have : ({θ, -θ, Tθ, -Tθ} : Set (GaloisField 3 (n / 2))) = {θ, -θ} := by
      rw [h1]; ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [this, Set.ncard_pair (hne θ hθ)]
  by_cases h2 : Tθ = -θ
  · left
    have : ({θ, -θ, Tθ, -Tθ} : Set (GaloisField 3 (n / 2))) = {θ, -θ} := by
      rw [h2, neg_neg]; ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [this, Set.ncard_pair (hne θ hθ)]
  · right
    have hA : θ ∉ ({-θ, Tθ, -Tθ} : Set (GaloisField 3 (n / 2))) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne θ hθ, fun h => h1 h.symm, fun h => h2 (by rw [h, neg_neg])⟩
    have hB : -θ ∉ ({Tθ, -Tθ} : Set (GaloisField 3 (n / 2))) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => h2 h.symm, fun h => h1 (neg_inj.mp h).symm⟩
    have e1 := Set.ncard_insert_of_notMem hA (Set.toFinite _)
    have e2 := Set.ncard_insert_of_notMem hB (Set.toFinite _)
    have e3 := Set.ncard_pair (hne Tθ hT)
    omega

theorem H13_ii_fibre (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 5 ≤ e) (heo : Odd e)
    (ξ0 : GaloisField 3 (n / 2)) (hξ0 : IsPrimitiveRoot ξ0 n)
    (hP : Set.BijOn (dftA ξ0) (NFSet n 2) {h | F1 3 2 ξ0 h ∧ F3 ξ0 h ∧ F4 h})
    (ν s1 h1 : GaloisField 3 (n / 2)) :
    (H13_above n ξ0 ν s1 h1).ncard ≤ 4 ∧ (H13_above n ξ0 ν s1 h1).ncard ∈ ({0, 2, 4} : Set ℕ) ∧
      ∀ y ∈ H13_above n ξ0 ν s1 h1, ∀ y' ∈ NFSet n 2,
        (y' ∈ H13_above n ξ0 ν s1 h1 ↔ paramMap n ξ0 y' ∈ ({dft ξ0 y 1, -dft ξ0 y 1, Tmap n ξ0 (dft ξ0 y 1),
          -Tmap n ξ0 (dft ξ0 y 1)} : Set _) ×ˢ ({s1} ×ˢ {h1})) := by
  have hiff := H13_ii_iff n e hne he heo ξ0 hξ0 ν s1 h1
  rcases Set.eq_empty_or_nonempty (H13_above n ξ0 ν s1 h1) with hE | ⟨y, hy⟩
  · refine ⟨by rw [hE, Set.ncard_empty]; omega, by rw [hE, Set.ncard_empty]; simp, hiff⟩
  refine ⟨?_, ?_, hiff⟩
  all_goals
    obtain ⟨hyX, hyν, hyS, hyc⟩ := H13_mem_above.mp hy
    have hyNF := H4_xia_to_nf hne (by omega) heo y hyX
    obtain ⟨hQ, -, -, hι2, hιq, -, -, -, -, -, -, -, hq9, -, -⟩ := H8_setup n e hne (by omega) ξ0 hξ0
    have hNF := hyNF
    obtain ⟨hL1, hL3, hRm, -⟩ := hyNF
    obtain ⟨hθ0, hθQ1⟩ := H4_NF_theta hne (by omega) hξ0 y hL1 hL3 hRm
    have hT0 : Tmap n ξ0 (dft ξ0 y 1) ≠ 0 := by
      intro h0
      have := (H13_c_C n e hne (by omega) ξ0 hξ0 _ hθQ1).1
      rw [h0, zero_pow (by have := H4_QQ_ge hne (by omega : 3 ≤ e); omega)] at this
      exact one_ne_zero (neg_eq_zero.mp this.symm)
    have hm := H4_mapsTo hne (by omega) ξ0 hξ0 y hNF
    simp only [paramMap, Set.mem_prod, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    have hbij := thm_3_1_bij_of n e hne (by omega) ξ0 hξ0 hP (thm_3_1_step1_proved n e hne (by omega))
    have hsub : H13_above n ξ0 ν s1 h1 ⊆ NFSet n 2 := fun z hz =>
      H4_xia_to_nf hne (by omega) heo z (H13_mem_above.mp hz).1
    have himg : paramMap n ξ0 '' H13_above n ξ0 ν s1 h1 =
        ({dft ξ0 y 1, -dft ξ0 y 1, Tmap n ξ0 (dft ξ0 y 1), -Tmap n ξ0 (dft ξ0 y 1)} : Set _) ×ˢ ({s1} ×ˢ {h1}) := by
      ext p
      constructor
      · rintro ⟨y', hy', rfl⟩
        exact (hiff y hy y' (hsub hy')).mp hy'
      · intro hp
        have hpT : p ∈ ({θ | θ ^ (QQ n - 1) = -1} ×ˢ
            (({1, -1} : Set (GaloisField 3 (n / 2))) ×ˢ {1, -1})) := by
          obtain ⟨θ', s', h'⟩ := p
          simp only [Set.mem_prod, Set.mem_singleton_iff] at hp
          obtain ⟨hθ'P, hs', hh'⟩ := hp
          simp only [Set.mem_prod, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
          rw [hs', hh', ← hyS, ← hyc]
          exact ⟨(H13_nu_of_mem n e hne (by omega) ξ0 hξ0 _ _ hθQ1 hθ'P).2, hm.2.1, hm.2.2⟩
        obtain ⟨y', hy'NF, hpy⟩ := hbij.surjOn hpT
        exact ⟨y', (hiff y hy y' hy'NF).mpr (by rw [hpy]; exact hp), hpy⟩
    have hcard : (H13_above n ξ0 ν s1 h1).ncard =
        ({dft ξ0 y 1, -dft ξ0 y 1, Tmap n ξ0 (dft ξ0 y 1), -Tmap n ξ0 (dft ξ0 y 1)} :
          Set (GaloisField 3 (n / 2))).ncard := by
      rw [← (hbij.injOn.mono hsub).ncard_image, himg, Set.ncard_prod, Set.ncard_prod, Set.ncard_singleton,
        Set.ncard_singleton, mul_one, mul_one]
    rcases H13_P_card n _ _ hθ0 hT0 with h | h <;> rw [hcard, h] <;> simp

/-- The count of Cor 3.5(ii): `|Xia| ≤ 4 · #{ν : ν^{q-1} = -1} · 4 ≤ 16(q-1)` (fibres of `y ↦ (ν, S, ŷ(1))`). -/
theorem H13_ii_count (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 5 ≤ e) (heo : Odd e)
    (ξ0 : GaloisField 3 (n / 2)) (hξ0 : IsPrimitiveRoot ξ0 n)
    (hfib : ∀ ν s1 h1 : GaloisField 3 (n / 2), (H13_above n ξ0 ν s1 h1).ncard ≤ 4) :
    Nat.card (XiaSet n 2) ≤ 16 * (qq n - 1) := by
  classical
  have : Fintype (GaloisField 3 (n / 2)) := Fintype.ofFinite _
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hq9, -, -⟩ := H8_setup n e hne (by omega) ξ0 hξ0
  obtain ⟨-, -, -, -, -, -, -, -, -, hνfacts, -⟩ := sec_3_2_setup_proved n e hne (by omega) ξ0 hξ0
  have hfinX : (XiaSet n 2).Finite := Set.toFinite _
  let f : (ZMod n → GaloisField 3 (n / 2)) → GaloisField 3 (n / 2) × GaloisField 3 (n / 2) × GaloisField 3 (n / 2) :=
    fun y => (dft ξ0 y 1 ^ (1 + qq n), S y, dft ξ0 y 0)
  let N : Finset (GaloisField 3 (n / 2)) := univ.filter (fun ν => ν ^ (qq n - 1) = -1)
  let pm : Finset (GaloisField 3 (n / 2)) := {1, -1}
  have hmaps : ∀ y ∈ hfinX.toFinset, f y ∈ N ×ˢ (pm ×ˢ pm) := by
    intro y hy
    rw [Set.Finite.mem_toFinset] at hy
    have hyNF := H4_xia_to_nf hne (by omega) heo y hy
    have hm := H4_mapsTo hne (by omega) ξ0 hξ0 y hyNF
    simp only [paramMap, Set.mem_prod, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    simp only [f, N, pm, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact ⟨(hνfacts _ hm.1).1, hm.2.1, hm.2.2⟩
  have hfib' : ∀ b ∈ N ×ˢ (pm ×ˢ pm), (hfinX.toFinset.filter (fun y => f y = b)).card ≤ 4 := by
    rintro ⟨ν, s1, h1⟩ -
    have hset : ((hfinX.toFinset.filter (fun y => f y = (ν, s1, h1)) : Finset _) :
        Set (ZMod n → GaloisField 3 (n / 2))) = H13_above n ξ0 ν s1 h1 := by
      ext y
      simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, f, Prod.mk.injEq, H13_mem_above]
    rw [← Set.ncard_coe_finset, hset]
    exact hfib ν s1 h1
  have h1 := Finset.card_le_mul_card_image_of_maps_to hmaps 4 hfib'
  have hN : N.card ≤ qq n - 1 := by
    have h0N : (0 : GaloisField 3 (n / 2)) ∉ (N : Set (GaloisField 3 (n / 2))) := by
      simp only [N, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [zero_pow (by omega)]
      exact fun h => one_ne_zero (neg_eq_zero.mp h.symm)
    have hroots : ∀ x ∈ insert (0 : GaloisField 3 (n / 2)) (N : Set (GaloisField 3 (n / 2))),
        x ^ qq n = (-1) * x := by
      intro x hx
      rcases hx with rfl | hx
      · rw [zero_pow (by omega), mul_zero]
      · simp only [N, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rw [H8_pow_pred x _ (by omega), hx]
    have hle := H7_card_le (qq n) (by omega) (-1) _ hroots
    rw [Nat.card_coe_set_eq, Set.ncard_insert_of_notMem h0N (Set.toFinite _), Set.ncard_coe_finset] at hle
    omega
  have hpm : pm.card ≤ 2 := Finset.card_le_two
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfinX]
  calc hfinX.toFinset.card ≤ 4 * (N ×ˢ (pm ×ˢ pm)).card := h1
    _ = 4 * (N.card * (pm.card * pm.card)) := by rw [Finset.card_product, Finset.card_product]
    _ ≤ 4 * ((qq n - 1) * (2 * 2)) := by gcongr
    _ = 16 * (qq n - 1) := by ring

end Cor

/-- Row 12a — Corollary 3.5(i) (s3_pow2.tex:127-132): `n = 2^e`, `e ≥ 5` odd. Xia's system with `σ = 2` has a solution
iff there are `ν` with `ν^{q-1} = -1`, signs `S`, `ŷ(1)`, and `(θ_+, θ_-) ∈ V_+ × V_-` on the conic
`θ_+^2 - θ_-^2 = ιν` with `N(y_0^+ + n^{-1}Λ_ν(-θ_+)) = -1` and `N(y_1^+ + n^{-1}Λ'_ν(-θ_-)) = -1`, where `y_0^+, y_1^+`
are the values determined by `(ν, S, ŷ(1))` (those of any norm-free solution with these data).
PARAMETRIZED by `hP24` = row `prop_2_4_bij` (`L := F`, `ω := ξ0`, for every `hn`, `h3`). -/
theorem cor_3_5_i_of (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 5 ≤ e) (heo : Odd e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n)
    (hP24 : Even n → ¬ 3 ∣ n → Set.BijOn (dftA ξ0) (NFSet n 2) {h | F1 3 2 ξ0 h ∧ F3 ξ0 h ∧ F4 h}) :
    (XiaSet n 2).Nonempty ↔
      ∃ ν s1 h1 θp θm : GaloisField 3 (n / 2), ν ^ (qq n - 1) = -1 ∧ (s1 = 1 ∨ s1 = -1) ∧ (h1 = 1 ∨ h1 = -1) ∧
        θp ∈ Vplus n ξ0 ∧ θm ∈ Vminus n ξ0 ∧ θp ^ 2 - θm ^ 2 = iota n ξ0 * ν ∧
        ∃ y ∈ NFSet n 2, dft ξ0 y 1 ^ (1 + qq n) = ν ∧ S y = s1 ∧ dft ξ0 y 0 = h1 ∧
          Nm n (yPlus n (y 0) + (n : GaloisField 3 (n / 2))⁻¹ * Lam n ξ0 ν (-θp)) = -1 ∧
          Nm n (yPlus n (y 1) + (n : GaloisField 3 (n / 2))⁻¹ * Lam' n ξ0 ν (-θm)) = -1 := by
  have he4 : 4 ≤ e := by omega
  have hP := hP24 (H4_even_of_pow2 hne (by omega)) (H4_not3_of_pow2 hne)
  obtain ⟨hQ, hqodd, hQodd, hι2, hιq, -, -, -, -, -, -, -, hq9, -, -⟩ := H8_setup n e hne he4 ξ0 hξ0
  obtain ⟨-, -, -, -, -, hVθ, -, -, -, hνfacts, -⟩ := sec_3_2_setup_proved n e hne he4 ξ0 hξ0
  constructor
  · rintro ⟨y, hy⟩
    have hyNF := H4_xia_to_nf hne (by omega) heo y hy
    obtain ⟨n0, n1⟩ := H4_xia_norms hne (by omega) y hy
    have hmem := H4_mapsTo hne (by omega) ξ0 hξ0 y hyNF
    simp only [paramMap, Set.mem_prod, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    obtain ⟨hθQ1, hs, hc⟩ := hmem
    have hθV := ((hVθ _).mpr hθQ1).1
    obtain ⟨-, hA2, hAp, hAm, hAe1, hAe2⟩ := H13_c_A n e hne he4 ξ0 hξ0 _ hθV
    have hb := thm_3_4_b_proved n e hne he4 ξ0 hξ0 y hyNF
    refine ⟨_, _, _, _, _, (hνfacts _ hθQ1).1, hs, hc, hAp, hAm, hA2, y, hyNF, rfl, rfl, rfl, ?_, ?_⟩
    · rw [← hAe1, ← hb.1, H9_split]; exact n0
    · rw [← hAe2, ← hb.2, H9_split]; exact n1
  · rintro ⟨ν, s1, h1, θp, θm, hν, hs1, hh1, hθp, hθm, hconic, y, hy, hyν, hyS, hy0, hn0, hn1⟩
    have h3 := H8_three_eq_zero (F := GaloisField 3 (n / 2))
    have hθV : θp + θm ∈ (Vsp n : Set (GaloisField 3 (n / 2))) := H8_V_add n _ _ hθp.1 hθm.1
    have hTθ : Tmap n ξ0 (θp + θm) = θp - θm := by rw [H8_T_add, hθp.2, hθm.2, sub_eq_add_neg]
    have hθν : (θp + θm) ^ (1 + qq n) = ν := by
      rw [(H13_c_A n e hne he4 ξ0 hξ0 _ hθV).1, hTθ]
      linear_combination (-iota n ξ0) * hconic - ν * hι2
    have hν0 : ν ≠ 0 := by
      intro h; rw [h, zero_pow (by omega)] at hν; exact one_ne_zero (neg_eq_zero.mp hν.symm)
    have hθ0 : θp + θm ≠ 0 := by
      intro h; apply hν0; rw [← hθν, h, zero_pow (by omega)]
    have hθQ1 : (θp + θm) ^ (QQ n - 1) = -1 := (hVθ _).mp ⟨hθV, hθ0⟩
    have hbij := thm_3_1_bij_of n e hne (by omega) ξ0 hξ0 hP (thm_3_1_step1_proved n e hne (by omega))
    have hpT : (θp + θm, s1, h1) ∈ ({θ | θ ^ (QQ n - 1) = -1} ×ˢ
        (({1, -1} : Set (GaloisField 3 (n / 2))) ×ˢ {1, -1})) := by
      simp only [Set.mem_prod, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact ⟨hθQ1, hs1, hh1⟩
    obtain ⟨y', hy', hpm⟩ := hbij.surjOn hpT
    simp only [paramMap, Prod.mk.injEq] at hpm
    obtain ⟨hθ', hS', hc'⟩ := hpm
    have hν' : dft ξ0 y' 1 ^ (1 + qq n) = dft ξ0 y 1 ^ (1 + qq n) := by rw [hθ', hθν, hyν]
    obtain ⟨hp0, hp1, -, -⟩ := H13_c_B n e hne he4 ξ0 hξ0 y' hy' y hy hν' (by rw [hS', hyS])
      (by rw [hc', hy0])
    have hb' := thm_3_4_b_proved n e hne he4 ξ0 hξ0 y' hy'
    refine ⟨y', H4_nf_to_xia hne (by omega) y' hy' ?_ ?_⟩
    · have e0 : θp + θm + (θp - θm) = -θp := by linear_combination θp * h3
      rw [← H9_split n (y' 0), hp0, hb'.1, hθ', hθν, hTθ, e0]; exact hn0
    · have e1 : θp + θm - (θp - θm) = -θm := by linear_combination θm * h3
      rw [← H9_split n (y' 1), hp1, hb'.2, hθ', hθν, hTθ, e1]; exact hn1

/-- Row 12b — Corollary 3.5(ii) (s3_pow2.tex:133-135): above each triple `(ν, S, ŷ(1))` Xia's system (`σ = 2`) has at
most 4 solutions; if it has any, they are the orbit `{±θ_+ ± θ_-}` of `⟨T, θ ↦ -θ⟩` (so 0, 2 or 4 of them); in total
at most `16(q-1) = 16(3^{n/8}-1)` solutions.
PARAMETRIZED by `hP24` = row `prop_2_4_bij` (`L := F`, `ω := ξ0`, for every `hn`, `h3`). -/
theorem cor_3_5_ii_of (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 5 ≤ e) (heo : Odd e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n)
    (hP24 : Even n → ¬ 3 ∣ n → Set.BijOn (dftA ξ0) (NFSet n 2) {h | F1 3 2 ξ0 h ∧ F3 ξ0 h ∧ F4 h}) :
    let above : GaloisField 3 (n / 2) → GaloisField 3 (n / 2) → GaloisField 3 (n / 2) →
        Set (ZMod n → GaloisField 3 (n / 2)) := fun ν s1 h1 =>
      {y | y ∈ XiaSet n 2 ∧ dft ξ0 y 1 ^ (1 + qq n) = ν ∧ S y = s1 ∧ dft ξ0 y 0 = h1}
    (∀ ν s1 h1, (above ν s1 h1).ncard ≤ 4 ∧ (above ν s1 h1).ncard ∈ ({0, 2, 4} : Set ℕ) ∧
      ∀ y ∈ above ν s1 h1, ∀ y' ∈ NFSet n 2,
        (y' ∈ above ν s1 h1 ↔ paramMap n ξ0 y' ∈ ({dft ξ0 y 1, -dft ξ0 y 1, Tmap n ξ0 (dft ξ0 y 1),
          -Tmap n ξ0 (dft ξ0 y 1)} : Set _) ×ˢ ({s1} ×ˢ {h1}))) ∧
      Nat.card (XiaSet n 2) ≤ 16 * (qq n - 1) := by
  intro above
  have hP := hP24 (H4_even_of_pow2 hne (by omega)) (H4_not3_of_pow2 hne)
  have hfibre := H13_ii_fibre n e hne he heo ξ0 hξ0 hP
  exact ⟨hfibre, H13_ii_count n e hne he heo ξ0 hξ0 (fun ν s1 h1 => (hfibre ν s1 h1).1)⟩

/-! ## 6. Corollary 3.5, EXACT: the `_of` forms with `prop_2_4_bij` supplied by `prop_2_4_bij_proved` (Prop24) -/

/-- Row 12a (cor_3_5_i), EXACT: `cor_3_5_i_of` applied to `Xia.Proofs.prop_2_4_bij_proved`. -/
theorem cor_3_5_i_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 5 ≤ e) (heo : Odd e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) :
    (XiaSet n 2).Nonempty ↔
      ∃ ν s1 h1 θp θm : GaloisField 3 (n / 2), ν ^ (qq n - 1) = -1 ∧ (s1 = 1 ∨ s1 = -1) ∧ (h1 = 1 ∨ h1 = -1) ∧
        θp ∈ Vplus n ξ0 ∧ θm ∈ Vminus n ξ0 ∧ θp ^ 2 - θm ^ 2 = iota n ξ0 * ν ∧
        ∃ y ∈ NFSet n 2, dft ξ0 y 1 ^ (1 + qq n) = ν ∧ S y = s1 ∧ dft ξ0 y 0 = h1 ∧
          Nm n (yPlus n (y 0) + (n : GaloisField 3 (n / 2))⁻¹ * Lam n ξ0 ν (-θp)) = -1 ∧
          Nm n (yPlus n (y 1) + (n : GaloisField 3 (n / 2))⁻¹ * Lam' n ξ0 ν (-θm)) = -1 :=
  cor_3_5_i_of n e hne he heo ξ0 hξ0 (fun hn h3 => prop_2_4_bij_proved n hn h3 ξ0 hξ0)

/-- Row 12b (cor_3_5_ii), EXACT: `cor_3_5_ii_of` applied to `Xia.Proofs.prop_2_4_bij_proved`. -/
theorem cor_3_5_ii_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 5 ≤ e) (heo : Odd e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) :
    let above : GaloisField 3 (n / 2) → GaloisField 3 (n / 2) → GaloisField 3 (n / 2) →
        Set (ZMod n → GaloisField 3 (n / 2)) := fun ν s1 h1 =>
      {y | y ∈ XiaSet n 2 ∧ dft ξ0 y 1 ^ (1 + qq n) = ν ∧ S y = s1 ∧ dft ξ0 y 0 = h1}
    (∀ ν s1 h1, (above ν s1 h1).ncard ≤ 4 ∧ (above ν s1 h1).ncard ∈ ({0, 2, 4} : Set ℕ) ∧
      ∀ y ∈ above ν s1 h1, ∀ y' ∈ NFSet n 2,
        (y' ∈ above ν s1 h1 ↔ paramMap n ξ0 y' ∈ ({dft ξ0 y 1, -dft ξ0 y 1, Tmap n ξ0 (dft ξ0 y 1),
          -Tmap n ξ0 (dft ξ0 y 1)} : Set _) ×ˢ ({s1} ×ˢ {h1}))) ∧
      Nat.card (XiaSet n 2) ≤ 16 * (qq n - 1) :=
  cor_3_5_ii_of n e hne he heo ξ0 hξ0 (fun hn h3 => prop_2_4_bij_proved n hn h3 ξ0 hξ0)

end Xia.Proofs

#print axioms Xia.Proofs.eq_top_all_V_proved
#print axioms Xia.Proofs.thm_3_4_b_proved
#print axioms Xia.Proofs.thm_3_4_c_proved
#print axioms Xia.Proofs.cor_3_5_i_of
#print axioms Xia.Proofs.cor_3_5_ii_of
#print axioms Xia.Proofs.cor_3_5_i_proved
#print axioms Xia.Proofs.cor_3_5_ii_proved
