/- Xia/Proofs/Thm62.lean — proofs of the rows thm_6_4_remarks, H14_theta, H14_F3r, sec_6_2_fourier, thm_6_2_step2, thm_6_2 of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry
import Xia.Proofs.Thm31
import Xia.Proofs.Coverage
import Xia.Proofs.Combinatorics
import Xia.Proofs.NumberTheory
import Xia.Proofs.Pow2Arith
import Xia.Proofs.Signs
import Xia.Proofs.Sec22

namespace Xia.Proofs

open Xia Finset

set_option linter.unusedSectionVars false

/-! ## Part A — Coverage s6_primes.tex:148-150 (thm_6_4_remarks) -/

theorem H14_topPairs_five (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) :
    topPairs n 5 = {{orbit 5 (1 : ZMod n), inv (orbit 5 1)}} := by
  obtain ⟨-, -, -, -, -, horb, -⟩ := thm_6_2_step1_proved n e hne he heo
  have h8 : 8 ≤ n := by
    rw [hne]; calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  apply Finset.eq_singleton_iff_unique_mem.mpr
  constructor
  · unfold topPairs topOrbits topLayer
    rw [Finset.mem_image]
    refine ⟨orbit 5 1, ?_, rfl⟩
    rw [Finset.mem_image]
    refine ⟨1, ?_, rfl⟩
    rw [Finset.mem_filter, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
    exact ⟨Finset.mem_univ _, odd_one⟩
  · intro P hP
    unfold topPairs topOrbits topLayer at hP
    obtain ⟨O, hO, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hO
    rw [Finset.mem_filter] at hk
    rcases horb k hk.2 with h | h
    · rw [h]
    · rw [h, H3_inv_inv, Finset.pair_comm]

theorem thm_6_4_remarks_proved :
    (∀ n : ℕ, n % 3 = 2 → kappa n (ZMod 3) = 1 ∧ legendreSym 3 (pp n : ℤ) = 1) ∧
    (∀ n e : ℕ, n = 2 ^ e → 3 ≤ e → Odd e → ∀ [NeZero n],
      (topPairs n 5).card = 1 ∧ ∀ P ∈ topPairs n 5, pairLen P = n / 4) := by
  refine ⟨fun n hn => ?_, fun n e hne he heo _ => ?_⟩
  · have hc : (n : ZMod 3) = 2 := by
      rw [← ZMod.natCast_mod, hn]; rfl
    have hp : ((pp n : ℕ) : ZMod 3) = 1 := by
      unfold pp; push_cast; rw [hc]; decide
    refine ⟨?_, ?_⟩
    · unfold kappa; rw [hc, hp]; decide
    · unfold legendreSym
      rw [show ((pp n : ℤ) : ZMod 3) = 1 by exact_mod_cast hp]
      exact MulChar.map_one _
  · have hT := H14_topPairs_five n e hne he heo
    have h8 : 8 ≤ 2 ^ e := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    have hr : ¬ 5 ∣ pp n * n := (sec_6_1_arith_proved n e hne he heo).2.2.2.2.1
    have hr1 : 5 % 2 ^ e ≠ 2 ^ e - 1 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
    have hsum := (thm_6_4_pairs_proved n e 1 5 (by rw [hne, mul_one]) he odd_one hr hr1).2
    rw [hT, Finset.sum_singleton] at hsum
    refine ⟨by rw [hT, Finset.card_singleton], ?_⟩
    intro P hP
    rw [hT, Finset.mem_singleton] at hP
    rw [hP]; exact hsum

/-! ## Part B — arithmetic of `n = 2^e` (e odd) for `r = 5` -/

section Arith5

theorem H14_shape {n e : ℕ} (hne : n = 2 ^ e) (he : 3 ≤ e) : ∃ t : ℕ, 1 ≤ t ∧ n = 8 * t := H4_shape hne he

/-- `5^{n/4} ≡ 1 (mod n)`. -/
theorem H14_five_pow_quarter {n e : ℕ} [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) :
    (5 : ZMod n) ^ (n / 4) = 1 := by
  obtain ⟨-, -, hord, -⟩ := thm_6_2_step1_proved n e hne he heo
  rw [← hord]; exact pow_orderOf_eq_one _

end Arith5

/-! ## Part C — Step 2, the generic identities along the orbit `{5^k}` -/

section Step2Generic

variable {K : Type*} [Field K]

/-- `t_k := ξ_0^{k5^k} θ^{5^k}` (s6_primes.tex:84). -/
def H14_t (ξ0 θ : K) (j : ℕ) : K := ξ0 ^ (j * 5 ^ j) * θ ^ (5 ^ j)

theorem H14_step2a (ξ0 θ : K) (k : ℕ) : ξ0 ^ ((k + 1) * 5 ^ (k + 1)) * θ ^ (5 ^ (k + 1)) =
    (ξ0 ^ (5 ^ k)) ^ 5 * (ξ0 ^ (k * 5 ^ k) * θ ^ (5 ^ k)) ^ 5 := by
  have e1 : (k + 1) * 5 ^ (k + 1) = 5 ^ k * 5 + k * 5 ^ k * 5 := by ring
  have e2 : 5 ^ (k + 1) = 5 ^ k * 5 := by ring
  rw [e1, e2, pow_add, pow_mul ξ0 (5 ^ k) 5, pow_mul ξ0 (k * 5 ^ k) 5, pow_mul θ (5 ^ k) 5]
  ring

theorem H14_step2c (κ ξ0 θ : K) (hκ : κ ^ 4 = 1) (k : ℕ) :
    -κ / (ξ0 ^ ((k + 1) * 5 ^ (k + 1)) * θ ^ (5 ^ (k + 1))) =
      ((ξ0 ^ (5 ^ k))⁻¹) ^ 5 * (-κ / (ξ0 ^ (k * 5 ^ k) * θ ^ (5 ^ k))) ^ 5 := by
  rw [H14_step2a]
  have hκ5 : (-κ) ^ 5 = -κ := by linear_combination (-κ) * hκ
  rw [div_pow, hκ5]
  simp only [div_eq_mul_inv, mul_inv, inv_pow]
  ring

/-- `θ^{Q-1} = c` from `θ^Q = c θ`, `θ ≠ 0`. -/
theorem H14_theta_of {θ c : K} {Q : ℕ} (hQ1 : 1 ≤ Q) (hθ0 : θ ≠ 0) (hQ : θ ^ Q = c * θ) : θ ^ (Q - 1) = c := by
  have : θ ^ (Q - 1) * θ = c * θ := by rw [pow_sub_one_mul (by omega), hQ]
  exact mul_right_cancel₀ hθ0 this

/-- The wrap: `t_{k + n/4} = t_k` once `θ^{Q-1} = -ι` (`Q = 5^{n/4} ≡ 1 mod n`, `Q ≡ 1 mod 4`). -/
theorem H14_step2b {n : ℕ} [NeZero n] (h8 : 8 ∣ n) {ξ0 θ : K} (hξ1 : ξ0 ^ n = 1) (hm : ξ0 ^ (n / 2) = -1)
    (h5q : (5 : ZMod n) ^ (n / 4) = 1) (hθ : θ ^ (5 ^ (n / 4) - 1) = -ξ0 ^ (n / 4)) (k : ℕ) :
    ξ0 ^ ((k + n / 4) * 5 ^ (k + n / 4)) * θ ^ (5 ^ (k + n / 4)) = ξ0 ^ (k * 5 ^ k) * θ ^ (5 ^ k) := by
  have hQ1 : 1 ≤ 5 ^ (n / 4) := Nat.one_le_pow _ _ (by norm_num)
  have hθQ : θ ^ (5 ^ (n / 4)) = -ξ0 ^ (n / 4) * θ := by
    rw [← pow_sub_one_mul (by omega), hθ]
  -- `θ^{5^{k+n/4}} = (θ^{5^{n/4}})^{5^k} = (-ι)^{5^k} θ^{5^k}`
  have hθpart : θ ^ (5 ^ (k + n / 4)) = (-ξ0 ^ (n / 4)) ^ (5 ^ k) * θ ^ (5 ^ k) := by
    rw [pow_add, pow_mul' θ (5 ^ k) (5 ^ (n / 4)), hθQ, mul_pow]
  -- `ξ0^{(k + n/4) 5^{k+n/4}} = ξ0^{(k + n/4) 5^k}` as `5^{n/4} ≡ 1 (mod n)`
  have hξpart : ξ0 ^ ((k + n / 4) * 5 ^ (k + n / 4)) = ξ0 ^ (k * 5 ^ k) * (ξ0 ^ (n / 4)) ^ (5 ^ k) := by
    rw [H4_pow_congr hξ1 (b := (k + n / 4) * 5 ^ k) (by push_cast; rw [pow_add, h5q, mul_one]),
      add_mul, pow_add, pow_mul ξ0 (n / 4) (5 ^ k)]
  have hodd : Odd (5 ^ k) := Odd.pow (by decide)
  have hι2 : (ξ0 ^ (n / 4)) ^ 2 = -1 := by
    rw [← pow_mul, show n / 4 * 2 = n / 2 by obtain ⟨r, hr⟩ := h8; omega, hm]
  -- `ι^{5^k} (-ι)^{5^k} = -(ι^2)^{5^k} = 1`
  have hkey : (ξ0 ^ (n / 4)) ^ (5 ^ k) * (-ξ0 ^ (n / 4)) ^ (5 ^ k) = 1 := by
    rw [← mul_pow, show ξ0 ^ (n / 4) * -ξ0 ^ (n / 4) = -((ξ0 ^ (n / 4)) ^ 2) by ring, hι2, neg_neg, one_pow]
  rw [hθpart, hξpart]
  linear_combination (ξ0 ^ (k * 5 ^ k) * θ ^ (5 ^ k)) * hkey

end Step2Generic

/-! ## Part D — the DFT on `ℤ/n` in a field with a primitive `n`-th root `ω`: orthogonality, inversion -/

section DFT

variable {n : ℕ} [NeZero n] {K : Type*} [Field K]

theorem H14_orth {ω : K} (hω : IsPrimitiveRoot ω n) (c : ZMod n) :
    ∑ s : ZMod n, ω ^ ((c * s).val) = if c = 0 then (n : K) else 0 := by
  have hω1 := hω.pow_eq_one
  split_ifs with hc
  · subst hc
    simp only [zero_mul, ZMod.val_zero, pow_zero, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
      mul_one]
  · have hx : ω ^ c.val ≠ 1 := hω.pow_ne_one_of_pos_of_lt ((ZMod.val_ne_zero c).mpr hc) (ZMod.val_lt c)
    have hsh := Equiv.sum_comp (Equiv.addRight (1 : ZMod n)) (fun s => ω ^ ((c * s).val))
    have hstep : ∀ s : ZMod n, ω ^ ((c * (s + 1)).val) = ω ^ ((c * s).val) * ω ^ c.val := by
      intro s; rw [mul_add, mul_one, H4_pow_val_add hω1]
    simp only [Equiv.coe_addRight, hstep, ← Finset.sum_mul] at hsh
    have h2 : (∑ s : ZMod n, ω ^ ((c * s).val)) * (ω ^ c.val - 1) = 0 := by linear_combination hsh
    rcases mul_eq_zero.mp h2 with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hx

/-- Inversion: `∑_k ŷ(ω^k) ω^{-kt} = n y_t`. -/
theorem H14_inv {ω : K} (hω : IsPrimitiveRoot ω n) (f : ZMod n → K) (t : ZMod n) :
    ∑ k, dft ω f k * ω ^ ((-(k * t)).val) = (n : K) * f t := by
  have hω1 := hω.pow_eq_one
  unfold dft
  simp_rw [H4_pow_val_mul hω1, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hu : ∀ u : ZMod n, ∑ k, f u * ω ^ ((k * u).val) * ω ^ ((-(k * t)).val) =
      f u * (if u - t = 0 then (n : K) else 0) := by
    intro u
    rw [← H14_orth hω (u - t), Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [mul_assoc, ← H4_pow_val_add hω1, show k * u + -(k * t) = (u - t) * k by ring]
  rw [Finset.sum_congr rfl (fun u _ => hu u)]
  simp only [sub_eq_zero, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

theorem H14_dft_inj {ω : K} (hω : IsPrimitiveRoot ω n) (hn0 : (n : K) ≠ 0) {f g : ZMod n → K}
    (h : ∀ k, dft ω f k = dft ω g k) : f = g := by
  funext t
  have h1 := H14_inv hω f t
  have h2 := H14_inv hω g t
  simp_rw [h] at h1
  exact mul_left_cancel₀ hn0 (h1.symm.trans h2)

theorem H14_dft_zero (ω : K) : dft ω (fun _ : ZMod n => (0 : K)) = fun _ => 0 := by
  funext k; unfold dft; simp

/-- The inverse transform `y_t = n^{-1} ∑_k h(k) ω^{-kt}`. -/
noncomputable def H14_idft (ω : K) (h : ZMod n → K) (t : ZMod n) : K :=
  (n : K)⁻¹ * ∑ k, h k * ω ^ ((-(k * t)).val)

theorem H14_dft_idft {ω : K} (hω : IsPrimitiveRoot ω n) (hn0 : (n : K) ≠ 0) (h : ZMod n → K) :
    dft ω (H14_idft ω h) = h := by
  have hω1 := hω.pow_eq_one
  funext j
  unfold dft H14_idft
  simp_rw [H4_pow_val_mul hω1]
  have hterm : ∀ t : ZMod n, (n : K)⁻¹ * (∑ k, h k * ω ^ ((-(k * t)).val)) * ω ^ ((j * t).val) =
      (n : K)⁻¹ * ∑ k, h k * ω ^ (((j - k) * t).val) := by
    intro t
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl; intro k _
    rw [mul_assoc, ← H4_pow_val_add hω1, show -(k * t) + j * t = (j - k) * t by ring]
  rw [Finset.sum_congr rfl (fun t _ => hterm t), ← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, H14_orth hω]
  simp only [sub_eq_zero, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [inv_mul_eq_iff_eq_mul₀ hn0]; ring

/-- The correlation identity: `ŷ(ξ) ŷ(ξ^{-1}) = ∑_s R(s) ξ^{-s}`. -/
theorem H14_dft_mul_neg {ω : K} (hω1 : ω ^ n = 1) (y : ZMod n → K) (k : ZMod n) :
    dft ω y k * dft ω y (-k) = ∑ s, R y s * ω ^ ((-(k * s)).val) := by
  unfold dft
  simp_rw [H4_pow_val_mul hω1]
  rw [Finset.sum_mul_sum]
  have step : ∀ t : ZMod n, ∑ u, (y t * ω ^ ((k * t).val)) * (y u * ω ^ ((-k * u).val)) =
      ∑ s, y t * y (t + s) * ω ^ ((-(k * s)).val) := by
    intro t
    rw [← Equiv.sum_comp (Equiv.addLeft t)]
    apply Finset.sum_congr rfl
    intro s _
    simp only [Equiv.coe_addLeft]
    have : ω ^ ((k * t).val) * ω ^ ((-k * (t + s)).val) = ω ^ ((-(k * s)).val) := by
      rw [← H4_pow_val_add hω1]; congr 2; ring
    linear_combination (y t * y (t + s)) * this
  rw [Finset.sum_congr rfl (fun t _ => step t), Finset.sum_comm]
  apply Finset.sum_congr rfl; intro s _
  rw [R, Finset.sum_mul]

/-- The transform of `T(s) = c + (d - c)[s = m]` at `-k`. -/
theorem H14_T_sum (hn : Even n) {ω : K} (hω : IsPrimitiveRoot ω n) (c d : K) (k : ZMod n) :
    ∑ s, (if s = half n then d else c) * ω ^ ((-(k * s)).val) =
      c * (if k = 0 then (n : K) else 0) + (d - c) * (ω ^ k.val) ^ (n / 2) := by
  have hω1 := hω.pow_eq_one
  have e1 : ∑ s, ω ^ ((-(k * s)).val) = if k = 0 then (n : K) else 0 := by
    have := H14_orth hω (-k)
    simp only [neg_mul, neg_eq_zero] at this
    exact this
  have e2 : ω ^ ((-(k * half n)).val) = (ω ^ k.val) ^ (n / 2) := by
    rw [← mul_neg, H4_neg_half hn, H4_pow_val_mul_nat hω1]; rfl
  calc ∑ s, (if s = half n then d else c) * ω ^ ((-(k * s)).val)
      = ∑ s, (c * ω ^ ((-(k * s)).val) + if s = half n then (d - c) * ω ^ ((-(k * s)).val) else 0) := by
        apply Finset.sum_congr rfl; intro s _; split_ifs <;> ring
    _ = c * (if k = 0 then (n : K) else 0) + (d - c) * (ω ^ k.val) ^ (n / 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, e1]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [e2]

end DFT

/-! ## Part E — (F3_5) ⟺ (L3_5) ∧ `R(m) = n^4` (any field, any even `n`) -/

section F3

variable {n : ℕ} [NeZero n] {K : Type*} [Field K]

theorem H14_F3_key (hn : Even n) {ω : K} (hω : IsPrimitiveRoot ω n) (y : ZMod n → K) (k : ZMod n)
    (hR : ∀ s, R y s = if s = half n then (n : K) ^ 4 else (n : K) * (1 - (pp n : K))) :
    dft ω y k * dft ω y (-k) = (n : K) * (1 - (pp n : K)) * (if k = 0 then (n : K) else 0) +
      ((n : K) ^ 4 - (n : K) * (1 - (pp n : K))) * (ω ^ k.val) ^ (n / 2) := by
  rw [H14_dft_mul_neg hω.pow_eq_one, ← H14_T_sum hn hω]
  apply Finset.sum_congr rfl; intro s _; rw [hR s]

theorem H14_F3r_of (hn : Even n) {ω : K} (hω : IsPrimitiveRoot ω n) (y : ZMod n → K)
    (hL3 : L3 ((n : K) * (1 - (pp n : K))) y) (hRm : R y (half n) = (n : K) ^ 4) :
    F3r (kappa n K) ω (dft ω y) := by
  have hR : ∀ s, R y s = if s = half n then (n : K) ^ 4 else (n : K) * (1 - (pp n : K)) := by
    intro s; split_ifs with h
    · rw [h, hRm]
    · exact H5_R_of_L3 hn _ y hL3 s h
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [H14_F3_key hn hω y k hR, ite_eq_right hk]; unfold kappa pp; push_cast; ring
  · rw [sq, show dft ω y 0 * dft ω y 0 = dft ω y 0 * dft ω y (-0) by rw [neg_zero], H14_F3_key hn hω y 0 hR,
      ite_eq_left rfl, ZMod.val_zero, pow_zero, one_pow]
    unfold pp; push_cast; ring

theorem H14_L3_of_F3r (hn : Even n) {ω : K} (hω : IsPrimitiveRoot ω n) (hn0 : (n : K) ≠ 0) (y : ZMod n → K)
    (hF : F3r (kappa n K) ω (dft ω y)) :
    L3 ((n : K) * (1 - (pp n : K))) y ∧ R y (half n) = (n : K) ^ 4 := by
  have hω1 := hω.pow_eq_one
  set T : ZMod n → K := fun s => if s = half n then (n : K) ^ 4 else (n : K) * (1 - (pp n : K)) with hT
  have hall : ∀ k : ZMod n, ∑ s, R y s * ω ^ ((-(k * s)).val) = ∑ s, T s * ω ^ ((-(k * s)).val) := by
    intro k
    rw [← H14_dft_mul_neg hω1, hT, H14_T_sum hn hω]
    by_cases hk : k = 0
    · subst hk
      rw [neg_zero, ← sq, hF.2, ite_eq_left rfl, ZMod.val_zero, pow_zero, one_pow]
      unfold pp; push_cast; ring
    · rw [hF.1 k hk, ite_eq_right hk]; unfold kappa pp; push_cast; ring
  have hRT : (fun s => R y s) = T := by
    apply H14_dft_inj hω hn0
    intro k
    have := hall (-k)
    simp only [neg_mul, neg_neg] at this
    unfold dft
    simp_rw [H4_pow_val_mul hω1]
    simpa only [neg_mul, neg_neg] using this
  have hRs : ∀ s, R y s = T s := fun s => congrFun hRT s
  refine ⟨fun s hs => ?_, ?_⟩
  · have hne : s ≠ half n := by
      intro h; rw [h, H4_half_val] at hs; omega
    have := hRs s
    rw [hT] at this; simp only [ite_eq_right hne] at this
    rw [← this]; unfold R; apply Finset.sum_congr rfl; intro t _; rw [add_comm]
  · have := hRs (half n)
    rw [hT] at this; simpa using this

end F3

/-! ## Part F — (F1_5) ⟺ (L1_5) in characteristic 5 -/

section F1

variable {n : ℕ} [NeZero n] {K : Type*} [Field K]

theorem H14_F1_iff (ω : K) (h : ZMod n → K) :
    F1 5 1 ω h ↔ ∀ k : ZMod n, h (5 * k) = (ω ^ k.val) ^ 5 * h k ^ 5 := by
  have e5 : ∀ x : K, x ^ ((5 : ℤ) * 1) = x ^ 5 := by
    intro x; rw [mul_one, show (5 : ℤ) = ((5 : ℕ) : ℤ) by norm_num, zpow_natCast]
  unfold F1
  simp only [Nat.cast_ofNat, e5]

theorem H14_F1_key [CharP K 5] {ω : K} (hω1 : ω ^ n = 1) (y : ZMod n → K) (k : ZMod n) :
    dft ω y (5 * k) - (ω ^ k.val) ^ 5 * dft ω y k ^ 5 =
      (ω ^ k.val) ^ 5 * ∑ t, (y (t + 1) - y t ^ 5) * ω ^ ((5 * k * t).val) := by
  have h5 : (ω ^ k.val) ^ 5 = ω ^ ((5 * k).val) := by
    rw [H4_pow_val_mul_nat hω1 k 5, show k * ((5 : ℕ) : ZMod n) = 5 * k by push_cast; ring]
  have A : dft ω y (5 * k) = (ω ^ k.val) ^ 5 * ∑ t, y (t + 1) * ω ^ ((5 * k * t).val) := by
    have e : dft ω y (5 * k) = ∑ t, y (t + 1) * ω ^ ((5 * k * (t + 1)).val) := by
      unfold dft; simp_rw [H4_pow_val_mul hω1]
      exact (Equiv.sum_comp (Equiv.addRight (1 : ZMod n)) (fun u => y u * ω ^ ((5 * k * u).val))).symm
    rw [e, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro t _
    rw [h5, mul_add, mul_one, H4_pow_val_add hω1]; ring
  have B : dft ω y k ^ 5 = ∑ t, y t ^ 5 * ω ^ ((5 * k * t).val) := by
    unfold dft; simp_rw [H4_pow_val_mul hω1]; rw [sum_pow_char]
    apply Finset.sum_congr rfl; intro t _
    rw [mul_pow, H4_pow_val_mul_nat hω1 (k * t) 5, show k * t * ((5 : ℕ) : ZMod n) = 5 * k * t by push_cast; ring]
  rw [A, B, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro t _; ring

theorem H14_F1_of_L1 [CharP K 5] {ω : K} (hω1 : ω ^ n = 1) (y : ZMod n → K) (hL1 : L1 5 1 y) :
    F1 5 1 ω (dft ω y) := by
  rw [H14_F1_iff]; intro k
  have hz : ∀ t, y (t + 1) - y t ^ 5 = 0 := by
    intro t; rw [sub_eq_zero]; have := hL1 t; rwa [Int.cast_one] at this
  have := H14_F1_key hω1 y k
  simp only [hz, zero_mul, Finset.sum_const_zero, mul_zero, sub_eq_zero] at this
  exact this

theorem H14_L1_of_F1 [CharP K 5] {ω : K} (hω : IsPrimitiveRoot ω n) (hn0 : (n : K) ≠ 0)
    (h5s : ∀ k : ZMod n, ∃ k', k = 5 * k') (y : ZMod n → K) (hF1 : F1 5 1 ω (dft ω y)) : L1 5 1 y := by
  have hω1 := hω.pow_eq_one
  rw [H14_F1_iff] at hF1
  have hg : ∀ k, dft ω (fun t => y (t + 1) - y t ^ 5) k = dft ω (fun _ => (0 : K)) k := by
    intro k
    rw [H14_dft_zero]
    obtain ⟨k', rfl⟩ := h5s k
    have := H14_F1_key hω1 y k'
    rw [hF1 k', sub_self] at this
    have hne : (ω ^ k'.val) ^ 5 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (hω.ne_zero (NeZero.ne n)))
    unfold dft; simp_rw [H4_pow_val_mul hω1]
    exact (mul_eq_zero.mp this.symm).resolve_left hne
  have hfun := H14_dft_inj hω hn0 hg
  intro s
  have := congrFun hfun s
  rw [Int.cast_one]; exact sub_eq_zero.mp this

/-- The iterate `ŷ(ξ^{5^j}) = ξ^{j5^j} ŷ(ξ)^{5^j}`. -/
theorem H14_F1_iter {ω : K} (hω1 : ω ^ n = 1) {h : ZMod n → K}
    (hF1 : ∀ k : ZMod n, h (5 * k) = (ω ^ k.val) ^ 5 * h k ^ 5) :
    ∀ (j : ℕ) (k : ZMod n), h ((5 : ZMod n) ^ j * k) = (ω ^ k.val) ^ (j * 5 ^ j) * h k ^ (5 ^ j) := by
  intro j
  induction j with
  | zero => intro k; simp
  | succ j ih =>
    intro k
    have hx : ω ^ ((5 : ZMod n) ^ j * k).val = (ω ^ k.val) ^ (5 ^ j) := by
      rw [H4_pow_val_mul_nat hω1 k (5 ^ j)]; congr 2; push_cast; ring
    rw [show (5 : ZMod n) ^ (j + 1) * k = 5 * (5 ^ j * k) by ring, hF1, ih, hx, H14_step2a]

end F1

/-! ## Part G — (F4) ⟺ (L4) (any field with `2 ≠ 0`, any even `n ≥ 3`) -/

section F4

variable {n : ℕ} [NeZero n] {K : Type*} [Field K]

/-- `c(r) := ∑_t (-1)^t y_t y_{r-t}` (s2_xia.tex:101). -/
def H14_C (y : ZMod n → K) (r : ZMod n) : K := ∑ t, sgn t * y t * y (r - t)

/-- `S ∑_{2s = r} y_s`, the coefficient of `ŷ(-1) ŷ(ξ^2)`. -/
def H14_D (y : ZMod n → K) (r : ZMod n) : K := S y * ∑ s, if 2 * s = r then y s else 0

theorem H14_F4_lhs (hn : Even n) (h2 : 2 ≤ n) {ω : K} (hω : IsPrimitiveRoot ω n) (y : ZMod n → K) (k : ZMod n) :
    dft ω y k * dft ω y (k + half n) = ∑ r, H14_C y r * ω ^ ((k * r).val) := by
  have hω1 := hω.pow_eq_one
  have hsg : ∀ t : ZMod n, ω ^ (((k + half n) * t).val) = sgn t * ω ^ ((k * t).val) := by
    intro t
    rw [add_mul, H4_pow_val_add hω1, ← H4_pow_val_mul hω1 (half n) t, H4_pow_val_half hω hn h2]
    unfold sgn; ring
  rw [mul_comm (dft ω y k) _]
  unfold dft
  simp_rw [H4_pow_val_mul hω1, hsg]
  rw [Finset.sum_mul_sum]
  have step : ∀ t : ZMod n, ∑ u, y t * (sgn t * ω ^ ((k * t).val)) * (y u * ω ^ ((k * u).val)) =
      ∑ r, sgn t * y t * y (r - t) * ω ^ ((k * r).val) := by
    intro t
    calc ∑ u, y t * (sgn t * ω ^ ((k * t).val)) * (y u * ω ^ ((k * u).val))
        = ∑ r, y t * (sgn t * ω ^ ((k * t).val)) * (y (r - t) * ω ^ ((k * (r - t)).val)) :=
          (Equiv.sum_comp (Equiv.subRight t)
            (fun u => y t * (sgn t * ω ^ ((k * t).val)) * (y u * ω ^ ((k * u).val)))).symm
      _ = ∑ r, sgn t * y t * y (r - t) * ω ^ ((k * r).val) := by
          apply Finset.sum_congr rfl; intro r _
          have : ω ^ ((k * t).val) * ω ^ ((k * (r - t)).val) = ω ^ ((k * r).val) := by
            rw [← H4_pow_val_add hω1]; congr 2; ring
          linear_combination (sgn t * y t * y (r - t)) * this
  rw [Finset.sum_congr rfl (fun t _ => step t), Finset.sum_comm]
  apply Finset.sum_congr rfl; intro r _
  unfold H14_C; rw [Finset.sum_mul]

theorem H14_F4_rhs (hn : Even n) (h2 : 2 ≤ n) {ω : K} (hω : IsPrimitiveRoot ω n) (y : ZMod n → K) (k : ZMod n) :
    dft ω y (half n) * dft ω y (2 * k) = ∑ r, H14_D y r * ω ^ ((k * r).val) := by
  have hω1 := hω.pow_eq_one
  rw [H4_S_eq_dft hn h2 hω]
  have hterm : ∀ r, H14_D y r * ω ^ ((k * r).val) =
      ∑ s, if 2 * s = r then S y * (y s * ω ^ ((k * (2 * s)).val)) else 0 := by
    intro r; unfold H14_D; rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro s _
    split_ifs with h
    · rw [← h]; ring
    · ring
  rw [Finset.sum_congr rfl (fun r _ => hterm r), Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  unfold dft; rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _
  rw [H4_pow_val_mul hω1, show 2 * k * s = k * (2 * s) by ring]

theorem H14_F4_iff (hn : Even n) (h2 : 2 ≤ n) {ω : K} (hω : IsPrimitiveRoot ω n) (hn0 : (n : K) ≠ 0)
    (y : ZMod n → K) : F4 (dft ω y) ↔ ∀ r, H14_C y r = H14_D y r := by
  have hω1 := hω.pow_eq_one
  constructor
  · intro hF4
    have hfun : H14_C y = H14_D y := by
      apply H14_dft_inj hω hn0
      intro k
      have := hF4 k
      rw [H14_F4_lhs hn h2 hω, H14_F4_rhs hn h2 hω] at this
      unfold dft; simp_rw [H4_pow_val_mul hω1]
      exact this
    exact fun r => congrFun hfun r
  · intro hCD k
    rw [H14_F4_lhs hn h2 hω, H14_F4_rhs hn h2 hω]
    simp_rw [hCD]

theorem H14_sum_two_mul (hn : Even n) (h3 : 3 ≤ n) (y : ZMod n → K) (s0 : ZMod n) :
    (∑ s, if 2 * s = 2 * s0 then y s else 0) = y s0 + y (s0 + half n) := by
  have hiff : ∀ s : ZMod n, 2 * s = 2 * s0 ↔ s = s0 ∨ s = s0 + half n := by
    intro s; constructor
    · intro h
      have h0 : 2 * (s - s0) = 0 := by rw [mul_sub, h, sub_self]
      rcases H4_two_mul_eq_zero hn h3 _ h0 with h' | h'
      · left; exact sub_eq_zero.mp h'
      · right; rw [← h']; ring
    · rintro (rfl | rfl)
      · rfl
      · rw [mul_add, H4_two_mul_half hn, add_zero]
  have hne : s0 ≠ s0 + half n := by
    intro h; apply H4_half_ne_zero (n := n) (by omega); linear_combination -h
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (fun s : ZMod n => 2 * s = 2 * s0) = {s0, s0 + half n} := by
    ext s; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, hiff]
  rw [hf, Finset.sum_pair hne]

theorem H14_CD_of_L4 (hn : Even n) (h3 : 3 ≤ n) (h2K : (2 : K) ≠ 0) (y : ZMod n → K) (hL4 : L4 y) :
    ∀ r, H14_C y r = H14_D y r := by
  have hev : ∀ s : ZMod n, Even (2 * s).val := by
    intro s
    have h2val : (2 : ZMod n).val = 2 := by
      rw [show (2 : ZMod n) = ((2 : ℕ) : ZMod n) by norm_num, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [ZMod.val_mul, h2val, Nat.even_iff, Nat.mod_mod_of_dvd _ (even_iff_two_dvd.mp hn)]
    omega
  intro r
  by_cases hr : Odd r.val
  · have hD : H14_D y r = 0 := by
      unfold H14_D
      rw [Finset.sum_eq_zero, mul_zero]
      intro s _
      split_ifs with h
      · exfalso
        rw [← h] at hr
        exact (Nat.not_odd_iff_even.mpr (hev s)) hr
      · rfl
    have hC : H14_C y r = 0 := by
      have hsr : (sgn r : K) = -1 := by unfold sgn; exact hr.neg_one_pow
      have hsym : H14_C y r = -H14_C y r := by
        unfold H14_C
        rw [← Finset.sum_neg_distrib]
        calc ∑ t, sgn t * y t * y (r - t) = ∑ t, sgn (r - t) * y (r - t) * y (r - (r - t)) :=
              (Equiv.sum_comp (Equiv.subLeft r) (fun t => (sgn t : K) * y t * y (r - t))).symm
          _ = ∑ t, -(sgn t * y t * y (r - t)) := by
              apply Finset.sum_congr rfl; intro t _
              rw [sub_sub_cancel, sub_eq_add_neg r t, H5_sgn_add hn, H5_sgn_neg hn, hsr]; ring
      have h2C : 2 * H14_C y r = 0 := by linear_combination hsym
      exact (mul_eq_zero.mp h2C).resolve_left h2K
    rw [hC, hD]
  · have h2s := H4_two_mul_hf r hr
    generalize ((r.val / 2 : ℕ) : ZMod n) = s0 at h2s
    subst h2s
    unfold H14_C H14_D
    rw [H2_L4_all hn hL4, H14_sum_two_mul hn h3 y]
    ring

theorem H14_L4_of_CD (hn : Even n) (h3 : 3 ≤ n) (y : ZMod n → K) (hCD : ∀ r, H14_C y r = H14_D y r) : L4 y := by
  intro s _
  have := hCD (2 * s)
  unfold H14_C H14_D at this
  rw [H14_sum_two_mul hn h3 y] at this
  rw [this]; ring

end F4

/-! ## Part H — transport along `F_{5^n} → L`, and values in `F_{5^n}` -/

section Transport

variable {n : ℕ} [NeZero n] {F L : Type*} [Field F] [Field L] [Algebra F L]

theorem H14_map_R (y : ZMod n → F) (s : ZMod n) :
    R (fun t => algebraMap F L (y t)) s = algebraMap F L (R y s) := by
  unfold R; rw [map_sum]; simp only [map_mul]

theorem H14_map_S (y : ZMod n → F) : S (fun t => algebraMap F L (y t)) = algebraMap F L (S y) := by
  unfold S sgn; rw [map_sum]; simp only [map_mul, map_pow, map_neg, map_one]

theorem H14_map_L1 (y : ZMod n → F) : L1 5 1 (fun t => algebraMap F L (y t)) ↔ L1 5 1 y := by
  unfold L1
  simp only [← map_pow, (algebraMap F L).injective.eq_iff]

theorem H14_map_c : algebraMap F L ((n : F) * (1 - (pp n : F))) = (n : L) * (1 - (pp n : L)) := by
  simp only [map_mul, map_sub, map_one, map_natCast]

theorem H14_map_L3 (y : ZMod n → F) :
    L3 ((n : L) * (1 - (pp n : L))) (fun t => algebraMap F L (y t)) ↔ L3 ((n : F) * (1 - (pp n : F))) y := by
  unfold L3
  have key : ∀ s : ZMod n, (∑ t, algebraMap F L (y t) * algebraMap F L (y (s + t))) =
      algebraMap F L (∑ t, y t * y (s + t)) := by
    intro s; rw [map_sum]; simp only [map_mul]
  simp only [key, ← H14_map_c (n := n) (F := F) (L := L), (algebraMap F L).injective.eq_iff]

theorem H14_map_L4 (y : ZMod n → F) : L4 (fun t => algebraMap F L (y t)) ↔ L4 y := by
  unfold L4
  have key : ∀ s : ZMod n, (∑ t, (sgn t : L) * algebraMap F L (y t) * algebraMap F L (y (2 * s - t))) =
      algebraMap F L (∑ t, sgn t * y t * y (2 * s - t)) := by
    intro s; rw [map_sum]; unfold sgn; simp only [map_mul, map_pow, map_neg, map_one]
  have key2 : ∀ s : ZMod n, (algebraMap F L (y s) + algebraMap F L (y (s + half n))) *
      S (fun t => algebraMap F L (y t)) = algebraMap F L ((y s + y (s + half n)) * S y) := by
    intro s; rw [H14_map_S]; simp only [map_mul, map_add]
  simp only [key, key2, (algebraMap F L).injective.eq_iff]

/-- A root of `X^{5^n} - X` in an extension `L` of `F_{5^n}` lies in `F_{5^n}`. -/
theorem H14_mem_range {L : Type*} [Field L] [Algebra (GaloisField 5 n) L] (z : L) (hz : z ^ (5 ^ n) = z) :
    ∃ x : GaloisField 5 n, algebraMap _ L x = z := by
  classical
  by_contra hne
  push Not at hne
  let : Fintype (GaloisField 5 n) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 5 n) = 5 ^ n := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 5 n (NeZero.ne n)]
  have h1 : 1 < 5 ^ n := Nat.one_lt_pow (NeZero.ne n) (by norm_num)
  have hP0 : (Polynomial.X ^ (5 ^ n) - Polynomial.X : Polynomial L) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero L h1
  have hdeg : (Polynomial.X ^ (5 ^ n) - Polynomial.X : Polynomial L).natDegree = 5 ^ n :=
    FiniteField.X_pow_card_sub_X_natDegree_eq L h1
  have hroot : ∀ w : L, w ^ (5 ^ n) = w →
      w ∈ (Polynomial.X ^ (5 ^ n) - Polynomial.X : Polynomial L).roots.toFinset := by
    intro w hw
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0]
    simp [hw]
  have hsub : insert z (Finset.univ.image (algebraMap (GaloisField 5 n) L)) ⊆
      (Polynomial.X ^ (5 ^ n) - Polynomial.X : Polynomial L).roots.toFinset := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hroot _ hz
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hw
      apply hroot; rw [← map_pow, ← hcard, FiniteField.pow_card]
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_image_of_injective _ (algebraMap (GaloisField 5 n) L).injective,
    Finset.card_univ, hcard] at hc
  have := (Multiset.toFinset_card_le (Polynomial.X ^ (5 ^ n) - Polynomial.X : Polynomial L).roots).trans
    (Polynomial.card_roots' _)
  omega

end Transport

/-! ## Part I — `κ` in characteristic 5 -/

theorem H14_kappa {K : Type*} [Field K] [CharP K 5] {n e : ℕ} (hne : n = 2 ^ e) (heo : Odd e) :
    (n : K) ^ 2 = -1 ∧ kappa n K = -(n : K) ∧ kappa n K ^ 2 = -1 := by
  have h5 : (5 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 5
  have hn2 : (n : K) ^ 2 = -1 := by
    have h4' : (4 : K) = -1 := by linear_combination h5
    rw [hne, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, mul_comm e 2, pow_mul,
      show (2 : K) ^ 2 = 4 by norm_num, h4', heo.neg_one_pow]
  have hκ : kappa n K = -(n : K) := by
    unfold kappa pp; push_cast; linear_combination ((n : K) ^ 2 + (n : K)) * hn2
  exact ⟨hn2, hκ, by rw [hκ, neg_sq, hn2]⟩

theorem H14_two_ne_zero {K : Type*} [Field K] [CharP K 5] : (2 : K) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K 5] at h'
  norm_num at h'

/-! ## Part J — the Fourier form for `r = 5` (sec_6_2_fourier), exact -/

theorem sec_6_2_fourier_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) {L : Type*} [Field L]
    [Algebra (GaloisField 5 n) L] (ω : L) (hω : IsPrimitiveRoot ω n) :
    Set.BijOn (dftA ω) (NF5Set n) {h | F1 5 1 ω h ∧ F3r (kappa n L) ω h ∧ F4 h} ∧
      ∀ y ∈ NF5Set n, (∀ (j : ℕ) (k : ZMod n),
        dftA ω y ((5 : ZMod n) ^ j * k) = (ω ^ k.val) ^ (j * 5 ^ j) * dftA ω y k ^ (5 ^ j)) ∧
        dftA ω y (half n) = algebraMap _ L (S y) := by
  have : CharP L 5 := charP_of_injective_algebraMap (algebraMap (GaloisField 5 n) L).injective 5
  obtain ⟨t, ht1, hnt⟩ := H4_shape hne he
  have hn : Even n := ⟨4 * t, by omega⟩
  have h2 : 2 ≤ n := by omega
  have h3 : 3 ≤ n := by omega
  have hω1 := hω.pow_eq_one
  have h2L : (2 : L) ≠ 0 := H14_two_ne_zero
  have hn0 : (n : L) ≠ 0 := by rw [hne]; push_cast; exact pow_ne_zero _ h2L
  have h5s : ∀ k : ZMod n, ∃ k', k = 5 * k' := fun k => ⟨5 ^ (n / 4 - 1) * k, by
    rw [← mul_assoc, mul_pow_sub_one (by omega) (5 : ZMod n), H14_five_pow_quarter hne he heo, one_mul]⟩
  have hdA : ∀ y : ZMod n → GaloisField 5 n, dftA ω y = dft ω (fun t => algebraMap (GaloisField 5 n) L (y t)) :=
    fun y => rfl
  have hfwd : ∀ y ∈ NF5Set n, F1 5 1 ω (dftA ω y) ∧ F3r (kappa n L) ω (dftA ω y) ∧ F4 (dftA ω y) := by
    rintro y ⟨hL1, hL3, hRm, hL4⟩
    rw [hdA]
    refine ⟨H14_F1_of_L1 hω1 _ ((H14_map_L1 y).mpr hL1),
      H14_F3r_of hn hω _ ((H14_map_L3 y).mpr hL3) (by rw [H14_map_R, hRm]; simp),
      (H14_F4_iff hn h2 hω hn0 _).mpr (H14_CD_of_L4 hn h3 h2L _ ((H14_map_L4 y).mpr hL4))⟩
  refine ⟨⟨fun y hy => hfwd y hy, ?_, ?_⟩, ?_⟩
  · intro y1 _ y2 _ heq
    have := H14_dft_inj hω hn0 (f := fun t => algebraMap (GaloisField 5 n) L (y1 t))
      (g := fun t => algebraMap (GaloisField 5 n) L (y2 t)) (fun k => congrFun heq k)
    funext t; exact (algebraMap (GaloisField 5 n) L).injective (congrFun this t)
  · rintro h ⟨hF1, hF3, hF4⟩
    have hyL : dft ω (H14_idft ω h) = h := H14_dft_idft hω hn0 h
    rw [← hyL] at hF1 hF3 hF4
    have hL1 := H14_L1_of_F1 hω hn0 h5s _ hF1
    obtain ⟨hL3, hRm⟩ := H14_L3_of_F3r hn hω hn0 _ hF3
    have hL4 := H14_L4_of_CD hn h3 _ ((H14_F4_iff hn h2 hω hn0 _).mp hF4)
    have hfix : ∀ t, H14_idft ω h t ^ (5 ^ n) = H14_idft ω h t := by
      intro t; have := H6_L1_iter hL1 n t
      simp only [ZMod.natCast_self, zero_mul, add_zero] at this; exact this.symm
    choose y hy using fun t => H14_mem_range (H14_idft ω h t) (hfix t)
    have hyy : (fun t => algebraMap (GaloisField 5 n) L (y t)) = H14_idft ω h := funext hy
    refine ⟨y, ⟨(H14_map_L1 y).mp (by rw [hyy]; exact hL1), (H14_map_L3 y).mp (by rw [hyy]; exact hL3), ?_,
      (H14_map_L4 y).mp (by rw [hyy]; exact hL4)⟩, ?_⟩
    · apply (algebraMap (GaloisField 5 n) L).injective
      rw [← H14_map_R, hyy, hRm]; simp
    · rw [hdA, hyy, hyL]
  · intro y hy
    obtain ⟨hF1, -, -⟩ := hfwd y hy
    refine ⟨H14_F1_iter hω1 ((H14_F1_iff ω _).mp hF1), ?_⟩
    rw [hdA, H4_S_eq_dft hn h2 hω, H14_map_S]

/-! ## Part K — Theorem 6.2, Step 2 (thm_6_2_step2), exact -/

/-- Frobenius on `θ = ŷ(ξ_0)`: `θ^{Q_5} = -ι_5 θ` (s6_primes.tex:82-83). -/
theorem H14_frob {K : Type*} [Field K] [CharP K 5] {n e : ℕ} [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e)
    {ω : K} (hω : IsPrimitiveRoot ω n) (y : ZMod n → K) (hL1 : L1 5 1 y) :
    dft ω y 1 ^ (5 ^ (n / 4)) = -ω ^ (n / 4) * dft ω y 1 := by
  obtain ⟨t, ht1, hnt⟩ := H4_shape hne he
  have hn : Even n := ⟨4 * t, by omega⟩
  have hω1 := hω.pow_eq_one
  have hm : ω ^ (n / 2) = -1 := H4_pow_half hω hn (by omega)
  have hrw : ∀ u : ZMod n, (ω ^ (1 : ZMod n).val) ^ u.val = ω ^ u.val := by
    intro u; rw [H4_pow_val_mul hω1, one_mul]
  have hq : ((n / 4 : ℕ) : ZMod n).val = n / 4 := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hι2 : ω ^ (n / 4) * ω ^ (n / 4) = -1 := by rw [← pow_add, show n / 4 + n / 4 = n / 2 by omega, hm]
  have h1 : dft ω y 1 ^ (5 ^ (n / 4)) = ∑ u, y (u + ((n / 4 : ℕ) : ZMod n)) * ω ^ u.val := by
    unfold dft; simp_rw [hrw]; rw [sum_pow_char_pow]
    apply Finset.sum_congr rfl; intro u _
    have hit := H6_L1_iter hL1 (n / 4) u
    simp only [Int.cast_one, mul_one] at hit
    rw [mul_pow, ← hit, ← pow_mul,
      H4_pow_congr hω1 (b := u.val) (by push_cast; rw [H14_five_pow_quarter hne he heo, mul_one])]
  have h2 : dft ω y 1 = ω ^ (n / 4) * ∑ u, y (u + ((n / 4 : ℕ) : ZMod n)) * ω ^ u.val := by
    have e : dft ω y 1 = ∑ u, y (u + ((n / 4 : ℕ) : ZMod n)) * ω ^ (u + ((n / 4 : ℕ) : ZMod n)).val := by
      unfold dft; simp_rw [hrw]
      exact (Equiv.sum_comp (Equiv.addRight ((n / 4 : ℕ) : ZMod n)) (fun u => y u * ω ^ u.val)).symm
    rw [e, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro u _
    rw [H4_pow_val_add hω1, hq]; ring
  rw [h1]
  conv_rhs => rw [h2]
  linear_combination (∑ u, y (u + ((n / 4 : ℕ) : ZMod n)) * ω ^ u.val) * hι2

theorem thm_6_2_step2_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) (ξ0 : GaloisField 5 n)
    (hξ0 : IsPrimitiveRoot ξ0 n) :
    (∀ y ∈ NF5Set n, dft ξ0 y 1 ≠ 0 ∧ dft ξ0 y 1 ^ (5 ^ (n / 4) - 1) = -ξ0 ^ (n / 4)) ∧
    ∀ θ : GaloisField 5 n, θ ^ (5 ^ (n / 4) - 1) = -ξ0 ^ (n / 4) →
      (∀ k : ℕ, ξ0 ^ ((k + 1) * 5 ^ (k + 1)) * θ ^ (5 ^ (k + 1)) =
        (ξ0 ^ (5 ^ k)) ^ 5 * (ξ0 ^ (k * 5 ^ k) * θ ^ (5 ^ k)) ^ 5) ∧
      (∀ k : ℕ, ξ0 ^ ((k + n / 4) * 5 ^ (k + n / 4)) * θ ^ (5 ^ (k + n / 4)) = ξ0 ^ (k * 5 ^ k) * θ ^ (5 ^ k)) ∧
      (∀ k : ℕ, -kappa n (GaloisField 5 n) / (ξ0 ^ ((k + 1) * 5 ^ (k + 1)) * θ ^ (5 ^ (k + 1))) =
        ((ξ0 ^ (5 ^ k))⁻¹) ^ 5 * (-kappa n (GaloisField 5 n) / (ξ0 ^ (k * 5 ^ k) * θ ^ (5 ^ k))) ^ 5) := by
  obtain ⟨t, ht1, hnt⟩ := H4_shape hne he
  have hn : Even n := ⟨4 * t, by omega⟩
  have h8 : 8 ∣ n := ⟨t, hnt⟩
  have hξ1 := hξ0.pow_eq_one
  have hm : ξ0 ^ (n / 2) = -1 := H4_pow_half hξ0 hn (by omega)
  obtain ⟨-, hκ, hκ2⟩ := H14_kappa (K := GaloisField 5 n) hne heo
  have hκ4 : kappa n (GaloisField 5 n) ^ 4 = 1 := by
    rw [show kappa n (GaloisField 5 n) ^ 4 = (kappa n (GaloisField 5 n) ^ 2) ^ 2 by ring, hκ2]; norm_num
  have hκ0 : kappa n (GaloisField 5 n) ≠ 0 := by
    intro h0; rw [h0] at hκ2; norm_num at hκ2
  refine ⟨?_, fun θ hθ => ⟨fun k => H14_step2a ξ0 θ k,
    fun k => H14_step2b h8 hξ1 hm (H14_five_pow_quarter hne he heo) hθ k,
    fun k => H14_step2c _ ξ0 θ hκ4 k⟩⟩
  rintro y ⟨hL1, hL3, hRm, -⟩
  have hF3 := H14_F3r_of hn hξ0 y hL3 hRm
  have h10 : (1 : ZMod n) ≠ 0 := by
    intro h; have := congrArg ZMod.val h
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega), ZMod.val_zero] at this; omega
  have h0 : dft ξ0 y 1 ≠ 0 := by
    intro h0
    have := hF3.1 1 h10
    rw [h0, zero_mul, H4_pow_one_val hξ1, hm] at this
    exact hκ0 (by linear_combination this)
  refine ⟨h0, H14_theta_of (Nat.one_le_pow _ _ (by norm_num)) h0 ?_⟩
  rw [H14_frob hne he heo hξ0 y hL1]

/-! ## Part L — the top layer for `r = 5`: odd residues are `±5^j`; values `t_j` and `-κ/t_j` -/

section Top5

variable {n : ℕ} [NeZero n] {K : Type*} [Field K]

open Classical in
noncomputable def H14_top (ξ0 θ κ : K) (k : ZMod n) : K :=
  if hk : ∃ j : ℕ, k = (5 : ZMod n) ^ j then H14_t ξ0 θ hk.choose
  else if hk' : ∃ j : ℕ, k = -(5 : ZMod n) ^ j then -κ / H14_t ξ0 θ hk'.choose else 0

theorem H14_top_pos {ξ0 θ κ : K} (hwd : ∀ i j : ℕ, (5 : ZMod n) ^ i = 5 ^ j → H14_t ξ0 θ i = H14_t ξ0 θ j)
    (j : ℕ) : H14_top ξ0 θ κ ((5 : ZMod n) ^ j) = H14_t ξ0 θ j := by
  have hex : ∃ i : ℕ, (5 : ZMod n) ^ j = 5 ^ i := ⟨j, rfl⟩
  unfold H14_top; rw [dite_eq_left hex]
  exact hwd _ _ hex.choose_spec.symm

theorem H14_top_neg {ξ0 θ κ : K} (hwd : ∀ i j : ℕ, (5 : ZMod n) ^ i = 5 ^ j → H14_t ξ0 θ i = H14_t ξ0 θ j)
    (hdisj : ∀ i j : ℕ, -(5 : ZMod n) ^ j ≠ 5 ^ i) (j : ℕ) :
    H14_top ξ0 θ κ (-(5 : ZMod n) ^ j) = -κ / H14_t ξ0 θ j := by
  have hn1 : ¬ ∃ i : ℕ, -(5 : ZMod n) ^ j = 5 ^ i := fun ⟨i, hi⟩ => hdisj i j hi
  have hex : ∃ i : ℕ, -(5 : ZMod n) ^ j = -5 ^ i := ⟨j, rfl⟩
  unfold H14_top; rw [dite_eq_right hn1, dite_eq_left hex]
  rw [hwd hex.choose j (neg_inj.mp hex.choose_spec).symm]

theorem H14_t_periodic {p : ℕ} {ξ0 θ : K} (hwrap : ∀ k, H14_t ξ0 θ (k + p) = H14_t ξ0 θ k) :
    ∀ q r, H14_t ξ0 θ (r + p * q) = H14_t ξ0 θ r := by
  intro q; induction q with
  | zero => intro r; simp
  | succ q ih => intro r; rw [mul_add_one, ← add_assoc, hwrap, ih]

theorem H14_t_wd {ξ0 θ : K} (hord : orderOf (5 : ZMod n) = n / 4) (hpos : 0 < n / 4)
    (hwrap : ∀ k, H14_t ξ0 θ (k + n / 4) = H14_t ξ0 θ k) :
    ∀ i j : ℕ, (5 : ZMod n) ^ i = 5 ^ j → H14_t ξ0 θ i = H14_t ξ0 θ j := by
  intro i j hij
  have hfin : IsOfFinOrder (5 : ZMod n) := orderOf_pos_iff.mp (by rw [hord]; exact hpos)
  have hmod := hfin.pow_inj_mod.mp hij
  rw [hord] at hmod
  rw [← Nat.mod_add_div i (n / 4), ← Nat.mod_add_div j (n / 4), H14_t_periodic hwrap, H14_t_periodic hwrap, hmod]

theorem H14_odd_cases (horb : ∀ x : ZMod n, Odd x.val → orbit 5 x = orbit 5 1 ∨ orbit 5 x = inv (orbit 5 1))
    (x : ZMod n) (hx : Odd x.val) : ∃ j : ℕ, x = (5 : ZMod n) ^ j ∨ x = -(5 : ZMod n) ^ j := by
  have hself : x ∈ orbit 5 x := by
    unfold orbit; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨0, by simp⟩
  rcases horb x hx with h | h
  · rw [h] at hself
    unfold orbit at hself; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hself
    obtain ⟨j, hj⟩ := hself
    exact ⟨j, Or.inl (by simpa using hj)⟩
  · rw [h] at hself
    unfold Xia.inv orbit at hself
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hself
    obtain ⟨w, ⟨j, hj⟩, hw⟩ := hself
    exact ⟨j, Or.inr (by rw [← hw, hj]; simp)⟩

theorem H14_neg_ne (hdisj : Disjoint (orbit 5 (1 : ZMod n)) (inv (orbit 5 1))) (i j : ℕ) :
    -(5 : ZMod n) ^ j ≠ 5 ^ i := by
  intro h
  have h1 : (5 : ZMod n) ^ i ∈ orbit 5 (1 : ZMod n) := by
    unfold orbit; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨i, by simp⟩
  have h2 : (5 : ZMod n) ^ i ∈ inv (orbit 5 (1 : ZMod n)) := by
    unfold Xia.inv; rw [Finset.mem_image]; refine ⟨5 ^ j, ?_, h⟩
    unfold orbit; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨j, by simp⟩
  exact Finset.disjoint_left.mp hdisj h1 h2

theorem H14_odd_val_pow5 (hn : Even n) (j : ℕ) : Odd ((5 : ZMod n) ^ j).val := by
  rw [show (5 : ZMod n) ^ j = ((5 ^ j : ℕ) : ZMod n) by push_cast; rfl, ZMod.val_natCast, Nat.odd_iff,
    Nat.mod_mod_of_dvd _ (even_iff_two_dvd.mp hn), ← Nat.odd_iff]
  exact Odd.pow (by decide)

theorem H14_E5 {ω : K} (hω1 : ω ^ n = 1) (j : ℕ) : ω ^ ((5 : ZMod n) ^ j).val = ω ^ (5 ^ j) := by
  rw [← H4_pow_val_natCast hω1 (5 ^ j)]; push_cast; rfl

theorem H14_pow5_half {ξ0 : K} (hm : ξ0 ^ (n / 2) = -1) (j : ℕ) : (ξ0 ^ (5 ^ j)) ^ (n / 2) = -1 := by
  rw [← pow_mul, mul_comm (5 ^ j) (n / 2), pow_mul, hm, Odd.neg_one_pow (Odd.pow (by decide))]

theorem H14_five_mul_ne {e : ℕ} (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) (k : ZMod n) (hk : k ≠ 0) :
    (5 : ZMod n) * k ≠ 0 := by
  intro h0
  apply hk
  have hq := H14_five_pow_quarter hne he heo
  obtain ⟨t, ht1, hnt⟩ := H4_shape hne he
  calc k = (5 : ZMod n) ^ (n / 4) * k := by rw [hq, one_mul]
    _ = 5 ^ (n / 4 - 1) * (5 * k) := by rw [← mul_assoc, pow_sub_one_mul (by omega)]
    _ = 0 := by rw [h0, mul_zero]

theorem H14_dftA_eq {n : ℕ} [NeZero n] (ξ0 : GaloisField 5 n) (y : ZMod n → GaloisField 5 n) :
    dftA ξ0 y = dft ξ0 y := by
  funext k; simp only [dftA, Algebra.algebraMap_self, RingHom.id_apply]

end Top5

/-! ## Part M — the layer recursion for `r = 5` (Steps 2-4 of s6_primes.tex:82-96): uniqueness and existence -/

section Fix5

variable {n : ℕ} [NeZero n] {K : Type*} [Field K] [CharP K 5]

/-- `ŷ(-1)^2 = κ` from (F3_5) at `-1` (`m` even). -/
theorem H14_hm_sq {e : ℕ} (hne : n = 2 ^ e) (he : 3 ≤ e) {ω : K} (hω : IsPrimitiveRoot ω n) {h : ZMod n → K}
    (hF3 : F3r (kappa n K) ω h) : h (half n) ^ 2 = kappa n K := by
  obtain ⟨t, ht1, hnt⟩ := H4_shape hne he
  have hn : Even n := ⟨4 * t, by omega⟩
  have := hF3.1 (half n) (H4_half_ne_zero (by omega))
  rw [H4_neg_half hn, H4_pow_val_half hω hn (by omega), Even.neg_one_pow ⟨2 * t, by omega⟩, mul_one] at this
  rw [sq]; exact this

/-- Uniqueness half: a function with (F1_5), (F3_5), (F4_5) is the fixed point of the layer recursion with
parameters `(h(1), h(-1)^{-1}, h(1 ↦ 0))`. -/
theorem H14_G_fixed {e : ℕ} (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) {ξ0 : K} (hξ0 : IsPrimitiveRoot ξ0 n)
    (horb : ∀ x : ZMod n, Odd x.val → orbit 5 x = orbit 5 1 ∨ orbit 5 x = inv (orbit 5 1))
    (hdisj' : ∀ i j : ℕ, -(5 : ZMod n) ^ j ≠ 5 ^ i) {h : ZMod n → K}
    (hwd : ∀ i j : ℕ, (5 : ZMod n) ^ i = 5 ^ j → H14_t ξ0 (h 1) i = H14_t ξ0 (h 1) j)
    (hF1 : F1 5 1 ξ0 h) (hF3 : F3r (kappa n K) ξ0 h) (hF4 : F4 h) :
    H4_Gam (H14_top ξ0 (h 1) (kappa n K)) (h (half n))⁻¹ (h 0) h = h := by
  obtain ⟨t, ht1, hnt⟩ := H4_shape hne he
  have hn : Even n := ⟨4 * t, by omega⟩
  have hω1 := hξ0.pow_eq_one
  have hm : ξ0 ^ (n / 2) = -1 := H4_pow_half hξ0 hn (by omega)
  have hF1' := (H14_F1_iff ξ0 h).mp hF1
  obtain ⟨-, -, hκ2⟩ := H14_kappa (K := K) hne heo
  have hκ0 : kappa n K ≠ 0 := by intro h0; rw [h0] at hκ2; norm_num at hκ2
  have hm2 := H14_hm_sq hne he hξ0 hF3
  have hm0 : h (half n) ≠ 0 := by intro h0; rw [h0] at hm2; exact hκ0 (by rw [← hm2]; ring)
  have hpos : ∀ j : ℕ, h ((5 : ZMod n) ^ j) = H14_t ξ0 (h 1) j := by
    intro j
    have := H14_F1_iter hω1 hF1' j 1
    rw [mul_one, H4_pow_one_val hω1] at this
    rw [this]; rfl
  have hneg : ∀ j : ℕ, h (-(5 : ZMod n) ^ j) = -kappa n K / H14_t ξ0 (h 1) j := by
    intro j
    have hne0 : (5 : ZMod n) ^ j ≠ 0 := by
      intro h0; have := H14_odd_val_pow5 hn j; rw [h0, ZMod.val_zero] at this; exact absurd this (by decide)
    have h3 := hF3.1 ((5 : ZMod n) ^ j) hne0
    rw [H14_E5 hω1, H14_pow5_half hm, hpos] at h3
    have ht0 : H14_t ξ0 (h 1) j ≠ 0 := by
      intro h0; rw [h0, zero_mul] at h3; exact hκ0 (by linear_combination h3)
    rw [eq_div_iff ht0]; linear_combination h3
  funext k
  rw [H4_Gam_apply]
  split_ifs with hodd hk0
  · obtain ⟨j, hj | hj⟩ := H14_odd_cases horb k hodd
    · rw [hj, H14_top_pos hwd, hpos]
    · rw [hj, H14_top_neg hwd hdisj', hneg]
  · rw [hk0]
  · have h2z := H4_two_mul_hf k hodd
    have h4z := hF4 ((k.val / 2 : ℕ) : ZMod n)
    rw [h2z] at h4z
    rw [mul_assoc, h4z, ← mul_assoc, inv_mul_cancel₀ hm0, one_mul]

/-- Existence half: the fixed point built from `(θ, S, c)` with `θ^{Q_5-1} = -ι_5`, `S^2 = κ`, `c^2 = n^2` satisfies
(F1_5), (F3_5), (F4_5) and has parameters `(θ, S, c)`. -/
theorem H14_fix_props {e : ℕ} (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) {ξ0 : K} (hξ0 : IsPrimitiveRoot ξ0 n)
    (horb : ∀ x : ZMod n, Odd x.val → orbit 5 x = orbit 5 1 ∨ orbit 5 x = inv (orbit 5 1))
    (hdisj' : ∀ i j : ℕ, -(5 : ZMod n) ^ j ≠ 5 ^ i)
    {θ s c : K} (hwd : ∀ i j : ℕ, (5 : ZMod n) ^ i = 5 ^ j → H14_t ξ0 θ i = H14_t ξ0 θ j)
    (hθ : θ ^ (5 ^ (n / 4) - 1) = -ξ0 ^ (n / 4)) (hs : s ^ 2 = kappa n K) (hc : c ^ 2 = (n : K) ^ 2) :
    F1 5 1 ξ0 (H4_fix e (H14_top (n := n) ξ0 θ (kappa n K)) s⁻¹ c) ∧
      F3r (kappa n K) ξ0 (H4_fix e (H14_top (n := n) ξ0 θ (kappa n K)) s⁻¹ c) ∧
      F4 (H4_fix e (H14_top (n := n) ξ0 θ (kappa n K)) s⁻¹ c) ∧
      H4_fix e (H14_top (n := n) ξ0 θ (kappa n K)) s⁻¹ c 1 = θ ∧
      H4_fix e (H14_top (n := n) ξ0 θ (kappa n K)) s⁻¹ c (half n) = s ∧
      H4_fix e (H14_top (n := n) ξ0 θ (kappa n K)) s⁻¹ c 0 = c := by
  have hfix : H4_Gam (H14_top (n := n) ξ0 θ (kappa n K)) s⁻¹ c (H4_fix e (H14_top (n := n) ξ0 θ (kappa n K)) s⁻¹ c) =
      H4_fix e (H14_top (n := n) ξ0 θ (kappa n K)) s⁻¹ c := H4_fix_eq hne (by omega) _ s⁻¹ c
  generalize H4_fix e (H14_top (n := n) ξ0 θ (kappa n K)) s⁻¹ c = h at hfix ⊢
  obtain ⟨t, ht1, hnt⟩ := H4_shape hne he
  have hn : Even n := ⟨4 * t, by omega⟩
  have h4 : 4 ∣ n := ⟨2 * t, by omega⟩
  have h3n : 3 ≤ n := by omega
  have hω1 : ξ0 ^ n = 1 := hξ0.pow_eq_one
  have hm : ξ0 ^ (n / 2) = -1 := H4_pow_half hξ0 hn (by omega)
  obtain ⟨hn2, -, hκ2⟩ := H14_kappa (K := K) hne heo
  have hκ0 : kappa n K ≠ 0 := by intro h0; rw [h0] at hκ2; norm_num at hκ2
  have hκ4 : kappa n K ^ 4 = 1 := by
    rw [show kappa n K ^ 4 = (kappa n K ^ 2) ^ 2 by ring, hκ2]; norm_num
  have hs0 : s ≠ 0 := by intro h0; rw [h0] at hs; exact hκ0 (by rw [← hs]; ring)
  -- the fixed-point equation, read off at odd `k`, at `0`, and at `2z ≠ 0`
  have hP1 : ∀ k : ZMod n, Odd k.val → h k = H14_top ξ0 θ (kappa n K) k := by
    intro k hk; rw [← hfix, H4_Gam_apply, ite_eq_left hk]
  have hP0 : h 0 = c := by rw [← hfix, H4_Gam_zero]
  have hP2 : ∀ z : ZMod n, 2 * z ≠ 0 → h (2 * z) = s⁻¹ * h z * h (z + half n) := by
    intro z hz
    have h2val : (2 : ZMod n).val = 2 := by
      rw [show (2 : ZMod n) = ((2 : ℕ) : ZMod n) by norm_num, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have hnodd : ¬ Odd (2 * z).val := by
      rw [Nat.not_odd_iff_even, ZMod.val_mul, h2val, Nat.even_iff,
        Nat.mod_mod_of_dvd _ (even_iff_two_dvd.mp hn)]
      omega
    have hfz := congrFun hfix (2 * z)
    rw [H4_Gam_apply, ite_eq_right hnodd, ite_eq_right hz] at hfz
    have hw2 := H4_two_mul_hf (2 * z) hnodd
    have hdiff : 2 * ((((2 * z).val / 2 : ℕ) : ZMod n) - z) = 0 := by rw [mul_sub, hw2, sub_self]
    rcases H4_two_mul_eq_zero hn h3n _ hdiff with hd | hd
    · rw [sub_eq_zero] at hd; rw [← hfz, hd]
    · rw [sub_eq_iff_eq_add] at hd
      rw [← hfz, hd, show half n + z + half n = z by
        rw [add_comm (half n) z, add_assoc, H4_half_add_half hn, add_zero], add_comm (half n) z]
      ring
  -- the values on the top layer
  have hθ0 : θ ≠ 0 := by
    intro h0
    have hQ : 1 ≤ 5 ^ (n / 4) - 1 := by
      have : 5 ≤ 5 ^ (n / 4) := by
        calc 5 = 5 ^ 1 := by norm_num
          _ ≤ 5 ^ (n / 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [h0, zero_pow (by omega)] at hθ
    exact pow_ne_zero (n / 4) (hξ0.ne_zero (NeZero.ne n)) (neg_eq_zero.mp hθ.symm)
  have ht0 : ∀ j, H14_t ξ0 θ j ≠ 0 := fun j =>
    mul_ne_zero (pow_ne_zero _ (hξ0.ne_zero (NeZero.ne n))) (pow_ne_zero _ hθ0)
  have hpos : ∀ j : ℕ, h ((5 : ZMod n) ^ j) = H14_t ξ0 θ j := by
    intro j; rw [hP1 _ (H14_odd_val_pow5 hn j), H14_top_pos hwd]
  have hneg : ∀ j : ℕ, h (-(5 : ZMod n) ^ j) = -kappa n K / H14_t ξ0 θ j := by
    intro j; rw [hP1 _ (H4_odd_val_neg hn _ (H14_odd_val_pow5 hn j)), H14_top_neg hwd hdisj']
  have hE5h : ∀ j : ℕ, (ξ0 ^ (5 ^ j)) ^ (n / 2) = -1 := H14_pow5_half hm
  have hE5n : ∀ j : ℕ, ξ0 ^ (-(5 : ZMod n) ^ j).val = (ξ0 ^ (5 ^ j))⁻¹ := by
    intro j; rw [H4_pow_val_neg hω1, H14_E5 hω1]
  -- (F1_5) and (F3_5) layer by layer (Step 3 of the paper)
  have hP4 : ∀ i, i ≤ e → ∀ k : ZMod n, ¬ 2 ^ i ∣ k.val →
      h (5 * k) = (ξ0 ^ k.val) ^ 5 * h k ^ 5 ∧ h k * h (-k) = kappa n K * (ξ0 ^ k.val) ^ (n / 2) := by
    intro i
    induction i with
    | zero => intro _ k hk; exact absurd (by simp) hk
    | succ i ih =>
      intro hi k hk
      by_cases hodd : Odd k.val
      · obtain ⟨j, hj | hj⟩ := H14_odd_cases horb k hodd
        · subst hj
          rw [show (5 : ZMod n) * 5 ^ j = 5 ^ (j + 1) by ring, hpos, hpos, hneg, H14_E5 hω1]
          refine ⟨H14_step2a ξ0 θ j, ?_⟩
          rw [hE5h]; field_simp [ht0 j]
        · subst hj
          rw [show (5 : ZMod n) * -5 ^ j = -5 ^ (j + 1) by ring, neg_neg, hneg, hneg, hpos, hE5n]
          refine ⟨H14_step2c _ ξ0 θ hκ4 j, ?_⟩
          rw [inv_pow, hE5h]; field_simp [ht0 j]
      · have hk0 : k ≠ 0 := by intro h0; apply hk; rw [h0, ZMod.val_zero]; exact dvd_zero _
        obtain ⟨hz1, hz2⟩ := H4_layer_hf hne i hi k hodd hk
        have h2z := H4_two_mul_hf k hodd
        generalize ((k.val / 2 : ℕ) : ZMod n) = z at hz1 hz2 h2z
        obtain ⟨a1, a3⟩ := ih (by omega) z hz1
        obtain ⟨b1, b3⟩ := ih (by omega) (z + half n) hz2
        obtain ⟨c1, c3⟩ := thm_6_2_step3_proved n h4 ξ0 hξ0 (kappa n K) hκ2 h s hs z
          (by
            intro w hw
            rcases Set.mem_insert_iff.mp hw with rfl | hw
            · exact a1
            · rw [Set.mem_singleton_iff] at hw; subst hw; exact b1)
          (by
            intro w hw
            rcases Set.mem_insert_iff.mp hw with rfl | hw
            · exact a3
            · rw [Set.mem_singleton_iff] at hw; subst hw; exact b3)
        have hk' : h k = s⁻¹ * h z * h (z + half n) := by
          rw [← h2z]; exact hP2 z (by rw [h2z]; exact hk0)
        have h5k : h (5 * k) = s⁻¹ * h (5 * z) * h (5 * z + half n) := by
          rw [← h2z, show (5 : ZMod n) * (2 * z) = 2 * (5 * z) by ring]
          exact hP2 _ (by rw [show (2 : ZMod n) * (5 * z) = 5 * (2 * z) by ring, h2z];
                          exact H14_five_mul_ne hne he heo k hk0)
        have hmk : h (-k) = s⁻¹ * h (-z) * h (-z + half n) := by
          rw [← h2z, show -(2 * z) = 2 * (-z) by ring]
          exact hP2 _ (by rw [show (2 : ZMod n) * -z = -(2 * z) by ring, h2z]; exact neg_ne_zero.mpr hk0)
        rw [h2z] at c1 c3
        refine ⟨?_, ?_⟩
        · calc h (5 * k) = s⁻¹ * h (5 * z) * h (5 * z + half n) := h5k
            _ = h (5 * z) * h (5 * z + half n) / s := by ring
            _ = (ξ0 ^ k.val) ^ 5 * (h z * h (z + half n) / s) ^ 5 := c1
            _ = (ξ0 ^ k.val) ^ 5 * h k ^ 5 := by rw [hk']; ring
        · calc h k * h (-k) = (h z * h (z + half n) / s) * (h (-z) * h (-z + half n) / s) := by
                rw [hk', hmk]; ring
            _ = kappa n K * (ξ0 ^ k.val) ^ (n / 2) := c3
  have hall : ∀ k : ZMod n, k ≠ 0 →
      h (5 * k) = (ξ0 ^ k.val) ^ 5 * h k ^ 5 ∧ h k * h (-k) = kappa n K * (ξ0 ^ k.val) ^ (n / 2) :=
    fun k hk0 => hP4 e le_rfl k (H4_nonzero_ndvd hne k hk0)
  have hF3 : F3r (kappa n K) ξ0 h := ⟨fun k hk => (hall k hk).2, by rw [hP0, hc]⟩
  have hF1 : ∀ k : ZMod n, h (5 * k) = (ξ0 ^ k.val) ^ 5 * h k ^ 5 := by
    intro k
    by_cases hk0 : k = 0
    · subst hk0
      rw [mul_zero, H4_pow_val_zero, one_pow, one_mul, hP0]
      have hc4 : c ^ 4 = 1 := by rw [show c ^ 4 = (c ^ 2) ^ 2 by ring, hc, hn2]; norm_num
      linear_combination (-c) * hc4
    · exact (hall k hk0).1
  -- `h(-1) = S` (Step 4)
  have hhm : h (half n) = s := by
    have hι : 2 * ((n / 4 : ℕ) : ZMod n) = half n := by
      unfold half; rw [show n / 2 = 2 * (n / 4) by omega]; push_cast; ring
    have := hP2 ((n / 4 : ℕ) : ZMod n) (by rw [hι]; exact H4_half_ne_zero (by omega))
    rw [hι] at this
    obtain ⟨h1, h2, -⟩ := thm_6_2_step4_proved n e hne he heo ξ0 hξ0 h hF3 s hs
    rw [this, mul_assoc, h1, inv_mul_eq_div, h2]
  refine ⟨(H14_F1_iff ξ0 h).mpr hF1, hF3, ?_, ?_, hhm, hP0⟩
  · intro k
    by_cases h2k : 2 * k = 0
    · rcases H4_two_mul_eq_zero hn h3n k h2k with rfl | rfl
      · rw [zero_add, mul_zero]; ring
      · rw [two_mul]
    · rw [hP2 k h2k, hhm]; field_simp
  · have := hpos 0
    rw [pow_zero] at this
    rw [this]; simp [H14_t]

end Fix5

/-! ## Part N — Theorem 6.2: bijection, sets and count -/

/-- MapsTo: `(ŷ(ξ_0), S, ŷ(1))` of a solution lies in the target set (no hypotheses). -/
theorem H14_mapsTo {n e : ℕ} [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) (ξ0 : GaloisField 5 n)
    (hξ0 : IsPrimitiveRoot ξ0 n) (y : ZMod n → GaloisField 5 n) (hy : y ∈ NF5Set n) :
    paramMap n ξ0 y ∈ ({θ | θ ^ (5 ^ (n / 4) - 1) = -ξ0 ^ (n / 4)} ×ˢ
      ({s | s ^ 2 = kappa n _} ×ˢ {(n : GaloisField 5 n), -(n : GaloisField 5 n)})) := by
  obtain ⟨t, ht1, hnt⟩ := H4_shape hne he
  have hn : Even n := ⟨4 * t, by omega⟩
  obtain ⟨hL1, hL3, hRm, _⟩ := hy
  have hF3 := H14_F3r_of hn hξ0 y hL3 hRm
  have hS2 : S y ^ 2 = kappa n (GaloisField 5 n) := by
    rw [← H4_S_eq_dft hn (by omega) hξ0]; exact H14_hm_sq hne he hξ0 hF3
  have h0 := (thm_6_2_step4_proved n e hne he heo ξ0 hξ0 _ hF3 (S y) hS2).2.2.1
  simp only [paramMap, Set.mem_prod, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact ⟨((thm_6_2_step2_proved n e hne he heo ξ0 hξ0).1 y ⟨hL1, hL3, hRm, ‹_›⟩).2, hS2, h0⟩

/-- Theorem 6.2, bijection, given the Fourier form's bijection at `L := F_{5^n}`, `ω := ξ0`. -/
theorem H14_bij (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) (ξ0 : GaloisField 5 n)
    (hξ0 : IsPrimitiveRoot ξ0 n)
    (hbij : Set.BijOn (dftA ξ0) (NF5Set n) {h | F1 5 1 ξ0 h ∧ F3r (kappa n (GaloisField 5 n)) ξ0 h ∧ F4 h}) :
    Set.BijOn (paramMap n ξ0) (NF5Set n)
      ({θ | θ ^ (5 ^ (n / 4) - 1) = -ξ0 ^ (n / 4)} ×ˢ
        ({s | s ^ 2 = kappa n _} ×ˢ {(n : GaloisField 5 n), -(n : GaloisField 5 n)})) := by
  obtain ⟨-, -, hord, -, -, horb, hdisj⟩ := thm_6_2_step1_proved n e hne he heo
  obtain ⟨t, ht1, hnt⟩ := H4_shape hne he
  have hn : Even n := ⟨4 * t, by omega⟩
  have h8 : 8 ∣ n := ⟨t, hnt⟩
  have hm : ξ0 ^ (n / 2) = -1 := H4_pow_half hξ0 hn (by omega)
  have hdisj' := H14_neg_ne hdisj
  have hwd : ∀ θ : GaloisField 5 n, θ ^ (5 ^ (n / 4) - 1) = -ξ0 ^ (n / 4) →
      ∀ i j : ℕ, (5 : ZMod n) ^ i = 5 ^ j → H14_t ξ0 θ i = H14_t ξ0 θ j := fun θ hθ =>
    H14_t_wd hord (by omega)
      (fun k => H14_step2b h8 hξ0.pow_eq_one hm (H14_five_pow_quarter hne he heo) hθ k)
  have hstep2 := (thm_6_2_step2_proved n e hne he heo ξ0 hξ0).1
  refine ⟨fun y hy => H14_mapsTo hne he heo ξ0 hξ0 y hy, ?_, ?_⟩
  · intro y1 hy1 y2 hy2 heq
    apply hbij.injOn hy1 hy2
    have hG1 := hbij.mapsTo hy1
    have hG2 := hbij.mapsTo hy2
    rw [H14_dftA_eq] at hG1 hG2 ⊢
    rw [H14_dftA_eq]
    obtain ⟨a1, a3, a4⟩ := hG1
    obtain ⟨b1, b3, b4⟩ := hG2
    simp only [paramMap, Prod.mk.injEq] at heq
    obtain ⟨e1, eS, e0⟩ := heq
    rw [← H4_S_eq_dft hn (by omega) hξ0, ← H4_S_eq_dft hn (by omega) hξ0] at eS
    have fx1 := H14_G_fixed hne he heo hξ0 horb hdisj' (hwd _ (hstep2 y1 hy1).2) a1 a3 a4
    have fx2 := H14_G_fixed hne he heo hξ0 horb hdisj' (hwd _ (hstep2 y2 hy2).2) b1 b3 b4
    rw [← e1, ← eS, ← e0] at fx2
    exact (H4_fix_unique hne (by omega) _ _ _ _ fx1).trans (H4_fix_unique hne (by omega) _ _ _ _ fx2).symm
  · rintro ⟨θ, s, c⟩ hT
    simp only [Set.mem_prod, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hT
    obtain ⟨hθ, hs, hc⟩ := hT
    have hc2 : c ^ 2 = (n : GaloisField 5 n) ^ 2 := by rcases hc with rfl | rfl <;> ring
    obtain ⟨f1, f3, f4, v1, vm, v0⟩ := H14_fix_props hne he heo hξ0 horb hdisj' (hwd θ hθ) hθ hs hc2
    obtain ⟨y, hy, hyh⟩ := hbij.surjOn ⟨f1, f3, f4⟩
    refine ⟨y, hy, ?_⟩
    rw [H14_dftA_eq] at hyh
    simp only [paramMap]
    rw [← H4_S_eq_dft hn (by omega) hξ0, hyh, v1, vm, v0]

/-- The first set has `Q_5 - 1` elements (a coset of `μ_{Q_5-1}`, s6_primes.tex:72-74). -/
theorem H14_theta_card {n e : ℕ} [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) (ξ0 : GaloisField 5 n)
    (hξ0 : IsPrimitiveRoot ξ0 n) :
    Nat.card {θ : GaloisField 5 n // θ ^ (5 ^ (n / 4) - 1) = -ξ0 ^ (n / 4)} = 5 ^ (n / 4) - 1 := by
  obtain ⟨t, ht1, hnt⟩ := H4_shape hne he
  obtain ⟨hdvd, -, himg, hι4⟩ := thm_6_2_sets_proved n e hne he heo ξ0 hξ0
  have hQ5 : 5 ≤ 5 ^ (n / 4) := by
    calc 5 = 5 ^ 1 := by norm_num
      _ ≤ 5 ^ (n / 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hQpos : 0 < 5 ^ (n / 4) - 1 := by omega
  have hmem : -ξ0 ^ (n / 4) ∈ (fun x : GaloisField 5 n => x ^ (5 ^ (n / 4) - 1)) ''
      {x | x ^ (4 * (5 ^ (n / 4) - 1)) = 1} := by rw [himg]; exact hι4
  obtain ⟨x0, -, hx0⟩ := hmem
  simp only at hx0
  have hι0 : -ξ0 ^ (n / 4) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ (hξ0.ne_zero (NeZero.ne n)))
  have hx00 : x0 ≠ 0 := by
    intro h0; rw [h0, zero_pow (by omega)] at hx0; exact hι0 hx0.symm
  have hd : 5 ^ (n / 4) - 1 ∣ Nat.card (GaloisField 5 n) - 1 := by
    rw [GaloisField.card 5 n (NeZero.ne n)]; exact (Dvd.intro_left 4 rfl).trans hdvd
  obtain ⟨ζ, hζ⟩ := H3_exists_prim (K := GaloisField 5 n) (5 ^ (n / 4) - 1) hd (by omega)
  have hcardR : (Polynomial.nthRootsFinset (5 ^ (n / 4) - 1) (1 : GaloisField 5 n)).card = 5 ^ (n / 4) - 1 :=
    hζ.card_nthRootsFinset
  let eqv : {θ : GaloisField 5 n // θ ^ (5 ^ (n / 4) - 1) = -ξ0 ^ (n / 4)} ≃
      {x : GaloisField 5 n // x ∈ Polynomial.nthRootsFinset (5 ^ (n / 4) - 1) (1 : GaloisField 5 n)} :=
    { toFun := fun θ => ⟨x0⁻¹ * θ.1, by
        rw [Polynomial.mem_nthRootsFinset hQpos, mul_pow, inv_pow, hx0, θ.2, inv_mul_cancel₀ hι0]⟩
      invFun := fun x => ⟨x0 * x.1, by
        have hx := (Polynomial.mem_nthRootsFinset hQpos (1 : GaloisField 5 n)).mp x.2
        rw [mul_pow, hx0, hx, mul_one]⟩
      left_inv := fun θ => by ext; simp [hx00]
      right_inv := fun x => by ext; simp [hx00] }
  rw [Nat.card_congr eqv, Nat.card_eq_finsetCard, hcardR]

/-- `{S : S^2 = κ}` has two elements, and they lie in `F_25`. -/
theorem H14_S_set {n e : ℕ} [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) :
    Nat.card {s : GaloisField 5 n // s ^ 2 = kappa n (GaloisField 5 n)} = 2 ∧
      ∀ s : GaloisField 5 n, s ^ 2 = kappa n (GaloisField 5 n) → s ^ 25 = s := by
  obtain ⟨t, ht1, hnt⟩ := H4_shape hne he
  obtain ⟨-, -, hκ2⟩ := H14_kappa (K := GaloisField 5 n) hne heo
  have hκ0 : kappa n (GaloisField 5 n) ≠ 0 := by intro h0; rw [h0] at hκ2; norm_num at hκ2
  -- a primitive 8th root of unity
  have h5n : (5 : ZMod n) ^ n = 1 := by
    calc (5 : ZMod n) ^ n = (5 : ZMod n) ^ (n / 4 * 4) := by congr 1; omega
      _ = ((5 : ZMod n) ^ (n / 4)) ^ 4 := pow_mul _ _ _
      _ = 1 := by rw [H14_five_pow_quarter hne he heo, one_pow]
  have hd8 : 8 ∣ Nat.card (GaloisField 5 n) - 1 := by
    rw [GaloisField.card 5 n (NeZero.ne n)]
    exact (Dvd.intro t hnt.symm).trans ((H6_five_pow_eq_one_iff n n).mp h5n)
  obtain ⟨ζ, hζ⟩ := H3_exists_prim (K := GaloisField 5 n) 8 hd8 (by norm_num)
  have hζ4 : ζ ^ 4 = -1 := H4_pow_half hζ ⟨4, rfl⟩ (by norm_num)
  have hsq : ∃ s0 : GaloisField 5 n, s0 ^ 2 = kappa n (GaloisField 5 n) := by
    have hprod : (ζ ^ 2 - kappa n (GaloisField 5 n)) * (ζ ^ 2 + kappa n (GaloisField 5 n)) = 0 := by
      linear_combination hζ4 - hκ2
    rcases mul_eq_zero.mp hprod with h | h
    · exact ⟨ζ, by linear_combination h⟩
    · exact ⟨ζ ^ 3, by linear_combination ζ ^ 2 * hζ4 - h⟩
  obtain ⟨s0, hs0⟩ := hsq
  have hs00 : s0 ≠ 0 := by intro h0; rw [h0] at hs0; exact hκ0 (by rw [← hs0]; ring)
  have hne2 : s0 ≠ -s0 := by
    intro h
    have h2 : (2 : GaloisField 5 n) * s0 = 0 := by linear_combination h
    exact hs00 ((mul_eq_zero.mp h2).resolve_left H14_two_ne_zero)
  have hset : ({s | s ^ 2 = kappa n (GaloisField 5 n)} : Set (GaloisField 5 n)) = {s0, -s0} := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [← hs0, sq_eq_sq_iff_eq_or_eq_neg]
  refine ⟨?_, ?_⟩
  · change Nat.card ({s | s ^ 2 = kappa n (GaloisField 5 n)} : Set (GaloisField 5 n)) = 2
    rw [hset, Nat.card_coe_set_eq, Set.ncard_pair hne2]
  · intro s hs
    rw [show s ^ 25 = s * (s ^ 2) ^ 12 by ring, hs,
      show kappa n (GaloisField 5 n) ^ 12 = (kappa n (GaloisField 5 n) ^ 2) ^ 6 by ring, hκ2]
    norm_num

/-- Theorem 6.2, parametrized by the Fourier form `sec_6_2_fourier` at `L := F_{5^n}`, `ω := ξ0` (every `ξ0`). -/
theorem thm_6_2_of (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e)
    (hFour : ∀ ξ0 : GaloisField 5 n, IsPrimitiveRoot ξ0 n →
      Set.BijOn (dftA ξ0) (NF5Set n) {h | F1 5 1 ξ0 h ∧ F3r (kappa n (GaloisField 5 n)) ξ0 h ∧ F4 h} ∧
        ∀ y ∈ NF5Set n, (∀ (j : ℕ) (k : ZMod n),
          dftA ξ0 y ((5 : ZMod n) ^ j * k) = (ξ0 ^ k.val) ^ (j * 5 ^ j) * dftA ξ0 y k ^ (5 ^ j)) ∧
          dftA ξ0 y (half n) = algebraMap _ (GaloisField 5 n) (S y)) :
    (∃ ξ0 : GaloisField 5 n, IsPrimitiveRoot ξ0 n) ∧
    ∀ ξ0 : GaloisField 5 n, IsPrimitiveRoot ξ0 n →
      Set.BijOn (paramMap n ξ0) (NF5Set n)
        ({θ | θ ^ (5 ^ (n / 4) - 1) = -ξ0 ^ (n / 4)} ×ˢ ({s | s ^ 2 = kappa n _} ×ˢ {(n : GaloisField 5 n), -(n : GaloisField 5 n)})) ∧
      Nat.card (NF5Set n) = 4 * (5 ^ (n / 4) - 1) ∧
      Nat.card {θ : GaloisField 5 n // θ ^ (5 ^ (n / 4) - 1) = -ξ0 ^ (n / 4)} = 5 ^ (n / 4) - 1 ∧
      Nat.card {s : GaloisField 5 n // s ^ 2 = kappa n _} = 2 ∧
      ∀ s : GaloisField 5 n, s ^ 2 = kappa n _ → s ^ 25 = s := by
  obtain ⟨t, ht1, hnt⟩ := H4_shape hne he
  have hex : ∃ ξ0 : GaloisField 5 n, IsPrimitiveRoot ξ0 n := by
    have h5n : (5 : ZMod n) ^ n = 1 := by
      calc (5 : ZMod n) ^ n = (5 : ZMod n) ^ (n / 4 * 4) := by congr 1; omega
        _ = ((5 : ZMod n) ^ (n / 4)) ^ 4 := pow_mul _ _ _
        _ = 1 := by rw [H14_five_pow_quarter hne he heo, one_pow]
    apply H3_exists_prim
    · rw [GaloisField.card 5 n (NeZero.ne n)]; exact (H6_five_pow_eq_one_iff n n).mp h5n
    · omega
  obtain ⟨hS1, hS2⟩ := H14_S_set (n := n) hne he heo
  refine ⟨hex, fun ξ0 hξ0 => ?_⟩
  have hb := H14_bij n e hne he heo ξ0 hξ0 (hFour ξ0 hξ0).1
  have hA := H14_theta_card hne he heo ξ0 hξ0
  have hn2 := (H14_kappa (K := GaloisField 5 n) hne heo).1
  have hnn : (n : GaloisField 5 n) ≠ -(n : GaloisField 5 n) := by
    intro h
    have h2 : (2 : GaloisField 5 n) * (n : GaloisField 5 n) = 0 := by linear_combination h
    have hn0 : (n : GaloisField 5 n) = 0 := (mul_eq_zero.mp h2).resolve_left H14_two_ne_zero
    rw [hn0] at hn2; norm_num at hn2
  refine ⟨hb, ?_, hA, hS1, hS2⟩
  rw [Nat.card_congr (Set.BijOn.equiv _ hb), Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod,
    Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
  have h1 : Nat.card ({θ | θ ^ (5 ^ (n / 4) - 1) = -ξ0 ^ (n / 4)} : Set (GaloisField 5 n)) = 5 ^ (n / 4) - 1 := hA
  have h2 : Nat.card ({s | s ^ 2 = kappa n (GaloisField 5 n)} : Set (GaloisField 5 n)) = 2 := hS1
  have h3 : Nat.card ({(n : GaloisField 5 n), -(n : GaloisField 5 n)} : Set (GaloisField 5 n)) = 2 := by
    rw [Nat.card_coe_set_eq, Set.ncard_pair hnn]
  rw [h1, h2, h3]; ring

/-- Theorem 6.2, EXACT (via the Fourier form proved above). -/
theorem thm_6_2_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) :
    (∃ ξ0 : GaloisField 5 n, IsPrimitiveRoot ξ0 n) ∧
    ∀ ξ0 : GaloisField 5 n, IsPrimitiveRoot ξ0 n →
      Set.BijOn (paramMap n ξ0) (NF5Set n)
        ({θ | θ ^ (5 ^ (n / 4) - 1) = -ξ0 ^ (n / 4)} ×ˢ ({s | s ^ 2 = kappa n _} ×ˢ {(n : GaloisField 5 n), -(n : GaloisField 5 n)})) ∧
      Nat.card (NF5Set n) = 4 * (5 ^ (n / 4) - 1) ∧
      Nat.card {θ : GaloisField 5 n // θ ^ (5 ^ (n / 4) - 1) = -ξ0 ^ (n / 4)} = 5 ^ (n / 4) - 1 ∧
      Nat.card {s : GaloisField 5 n // s ^ 2 = kappa n _} = 2 ∧
      ∀ s : GaloisField 5 n, s ^ 2 = kappa n _ → s ^ 25 = s :=
  thm_6_2_of n e hne he heo (fun ξ0 hξ0 => sec_6_2_fourier_proved n e hne he heo ξ0 hξ0)

end Xia.Proofs

#print axioms Xia.Proofs.thm_6_4_remarks_proved
#print axioms Xia.Proofs.sec_6_2_fourier_proved
#print axioms Xia.Proofs.thm_6_2_step2_proved
#print axioms Xia.Proofs.thm_6_2_of
#print axioms Xia.Proofs.thm_6_2_proved
