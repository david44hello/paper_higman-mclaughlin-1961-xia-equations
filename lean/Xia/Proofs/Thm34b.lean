/- Xia/Proofs/Thm34b.lean — proofs of the rows L10_hX34b of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import Xia.Defs.DiffSet

namespace Xia.Proofs

open Xia Finset

set_option linter.unusedSectionVars false

/-! ## (A) Salié's evaluation, elementary (any additive character `e` of `ZMod p`, `p` an odd prime) -/

section H31A

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K]

/-- The quadratic character of `ZMod p`, with values in `K`. -/
noncomputable def H31_psi (K : Type*) [Field K] (x : ZMod p) : K := ((quadraticChar (ZMod p) x : ℤ) : K)

theorem H31_psi_mul (x y : ZMod p) : H31_psi K (x * y) = H31_psi K x * H31_psi K y := by
  unfold H31_psi
  rw [map_mul, Int.cast_mul]

theorem H31_psi_zero : H31_psi K (0 : ZMod p) = 0 := by
  unfold H31_psi
  rw [quadraticChar_zero, Int.cast_zero]

theorem H31_psi_sq {x : ZMod p} (hx : x ≠ 0) : H31_psi K x * H31_psi K x = 1 := by
  unfold H31_psi
  rw [← Int.cast_mul, ← sq, quadraticChar_sq_one hx, Int.cast_one]

theorem H31_psi_sq' {x : ZMod p} (hx : x ≠ 0) : H31_psi K (x ^ 2) = 1 := by
  unfold H31_psi
  rw [quadraticChar_sq_one' hx, Int.cast_one]

theorem H31_two_ne_zero (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have hp := (Fact.out : p.Prime)
  rcases (Nat.dvd_prime Nat.prime_two).1 h' with h1 | h1
  · exact hp.one_lt.ne' h1
  · exact hp2 h1

/-- Root count: `#{y ≠ 0 : y + y⁻¹ = c} = 1 + ψ(c² - 4)`. -/
theorem H31_card_roots (hp2 : p ≠ 2) (c : ZMod p) :
    (((univ.filter (fun y : ZMod p => y + y⁻¹ = c ∧ y ≠ 0)).card : ℕ) : K) = H31_psi K (c ^ 2 - 4) + 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := H31_two_ne_zero hp2
  have h2i : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  have hcount := quadraticChar_card_sqrts (F := ZMod p) (by rw [ZMod.ringChar_zmod_n]; exact hp2) (c ^ 2 - 4)
  have hbij : (univ.filter (fun y : ZMod p => y + y⁻¹ = c ∧ y ≠ 0)).card =
      ({x : ZMod p | x ^ 2 = c ^ 2 - 4}.toFinset).card := by
    apply Finset.card_nbij' (fun y => 2 * y - c) (fun z => (z + c) * 2⁻¹)
    · intro y hy
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy
      simp only [Set.coe_toFinset, Set.mem_ofPred_eq]
      obtain ⟨hyc, hy0⟩ := hy
      have hyy := mul_inv_cancel₀ hy0
      linear_combination (4 * y) * hyc - 4 * hyy
    · intro z hz
      simp only [Set.coe_toFinset, Set.mem_ofPred_eq] at hz
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
      set y := (z + c) * 2⁻¹ with hy
      have hq : y * y + 1 = c * y := by
        rw [hy]
        linear_combination (2⁻¹ : ZMod p) ^ 2 * hz +
          ((c * z + c ^ 2) * 2⁻¹ - (2 * 2⁻¹ + 1)) * h2i
      have hy0 : y ≠ 0 := by
        intro h0
        rw [h0] at hq
        simp at hq
      refine ⟨?_, hy0⟩
      have hinv : y⁻¹ = c - y := inv_eq_of_mul_eq_one_right (by linear_combination -hq)
      rw [hinv]
      ring
    · intro y _
      show (2 * y - c + c) * 2⁻¹ = y
      linear_combination y * h2i
    · intro z _
      show 2 * ((z + c) * 2⁻¹) - c = z
      linear_combination (z + c) * h2i
  unfold H31_psi
  rw [hbij]
  have h := congrArg (Int.cast : ℤ → K) hcount
  push_cast at h
  exact h

/-- `A(c) := ∑_{y + y⁻¹ = c} ψ(y) = ψ(c + 2) + ψ(c - 2)`. -/
theorem H31_A_eq (hp2 : p ≠ 2) (c : ZMod p) :
    ∑ y ∈ univ.filter (fun y : ZMod p => y + y⁻¹ = c), H31_psi K y = H31_psi K (c + 2) + H31_psi K (c - 2) := by
  have h2 : (2 : ZMod p) ≠ 0 := H31_two_ne_zero hp2
  by_cases hc : c + 2 = 0
  · -- `c = -2`: the only `y` is `-1`.
    have hset : univ.filter (fun y : ZMod p => y + y⁻¹ = c) = {-1} := by
      ext y
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · intro h
        have hy0 : y ≠ 0 := by
          rintro rfl
          rw [inv_zero, add_zero] at h
          apply h2
          linear_combination hc + h
        have hyy := mul_inv_cancel₀ hy0
        have hsq : (y + 1) ^ 2 = 0 := by linear_combination y * h - hyy + y * hc
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
        linear_combination this
      · rintro rfl
        rw [inv_neg, inv_one]
        linear_combination -hc
    rw [hset, sum_singleton, hc, H31_psi_zero, zero_add,
      show c - 2 = (-1) * 2 ^ 2 by linear_combination hc, H31_psi_mul, H31_psi_sq' h2, mul_one]
  · -- `c ≠ -2`: every root `y` has `ψ(y) = ψ(c+2)`.
    rw [← sum_filter_of_ne (p := fun y : ZMod p => y ≠ 0) (fun y _ hy => by
      rintro rfl; exact hy H31_psi_zero), filter_filter]
    have hterm : ∀ y ∈ univ.filter (fun y : ZMod p => y + y⁻¹ = c ∧ y ≠ 0), H31_psi K y = H31_psi K (c + 2) := by
      intro y hy
      simp only [mem_filter, mem_univ, true_and] at hy
      obtain ⟨hyc, hy0⟩ := hy
      have hyy := mul_inv_cancel₀ hy0
      have hsq : y * (c + 2) = (y + 1) ^ 2 := by linear_combination -(y * hyc) + hyy
      have hy1 : y + 1 ≠ 0 := by
        intro h0
        rw [h0, zero_pow (by norm_num)] at hsq
        exact (mul_ne_zero hy0 hc) hsq
      have e1 : H31_psi K y * H31_psi K (c + 2) = 1 := by
        rw [← H31_psi_mul, hsq, H31_psi_sq' hy1]
      have e2 := H31_psi_sq (K := K) hc
      linear_combination H31_psi K (c + 2) * e1 - H31_psi K y * e2
    rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul, H31_card_roots hp2 c,
      show c ^ 2 - 4 = (c + 2) * (c - 2) by ring, H31_psi_mul]
    have e2 := H31_psi_sq (K := K) hc
    linear_combination H31_psi K (c - 2) * e2

/-- Twisted Gauss sum: `∑_x ψ(x) e(v x) = ψ(v) G`. -/
theorem H31_twist (e : ZMod p → K) {v : ZMod p} (hv : v ≠ 0) :
    ∑ x, H31_psi K x * e (v * x) = H31_psi K v * ∑ x, H31_psi K x * e x := by
  rw [mul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft₀ v hv) _ _ (fun x => ?_)
  simp only [Equiv.mulLeft₀_apply]
  rw [H31_psi_mul]
  have e2 := H31_psi_sq (K := K) hv
  linear_combination -(H31_psi K x * e (v * x)) * e2

/-- `T(v) := ∑_y ψ(y) e(v (y + y⁻¹)) = ψ(v) G (e(2v) + e(-2v))`. -/
theorem H31_T (hp2 : p ≠ 2) (e : ZMod p → K) (he : ∀ a b, e (a + b) = e a * e b) {v : ZMod p} (hv : v ≠ 0) :
    ∑ y, H31_psi K y * e (v * (y + y⁻¹)) =
      H31_psi K v * (∑ x, H31_psi K x * e x) * (e (2 * v) + e (-(2 * v))) := by
  have h1 : ∑ y, H31_psi K y * e (v * (y + y⁻¹)) =
      ∑ c, (∑ y ∈ univ.filter (fun y : ZMod p => y + y⁻¹ = c), H31_psi K y) * e (v * c) := by
    rw [← Finset.sum_fiberwise univ (fun y : ZMod p => y + y⁻¹)]
    refine sum_congr rfl (fun c _ => ?_)
    rw [sum_mul]
    refine sum_congr rfl (fun y hy => ?_)
    rw [(mem_filter.1 hy).2]
  rw [h1]
  simp_rw [H31_A_eq hp2, add_mul, sum_add_distrib]
  have hA : ∑ c, H31_psi K (c + 2) * e (v * c) = e (-(2 * v)) * ∑ c, H31_psi K c * e (v * c) := by
    rw [mul_sum]
    refine Fintype.sum_equiv (Equiv.addRight 2) _ _ (fun c => ?_)
    simp only [Equiv.coe_addRight]
    rw [show v * c = -(2 * v) + v * (c + 2) by ring, he]
    ring
  have hB : ∑ c, H31_psi K (c - 2) * e (v * c) = e (2 * v) * ∑ c, H31_psi K c * e (v * c) := by
    rw [mul_sum]
    refine Fintype.sum_equiv (Equiv.subRight 2) _ _ (fun c => ?_)
    simp only [Equiv.subRight_apply]
    rw [show v * c = 2 * v + v * (c - 2) by ring, he]
    ring
  rw [hA, hB, H31_twist e hv]
  ring

/-- SALIÉ: for `v ≠ 0`, `∑_x ψ(x) e(x + v² x⁻¹) = G (e(2v) + e(-2v))`, `G = ∑_x ψ(x) e(x)`. -/
theorem H31_salie (hp2 : p ≠ 2) (e : ZMod p → K) (he : ∀ a b, e (a + b) = e a * e b) {v : ZMod p} (hv : v ≠ 0) :
    ∑ x, H31_psi K x * e (x + v ^ 2 * x⁻¹) = (∑ x, H31_psi K x * e x) * (e (2 * v) + e (-(2 * v))) := by
  have hvv := mul_inv_cancel₀ hv
  have h1 : ∑ x, H31_psi K x * e (x + v ^ 2 * x⁻¹) = ∑ y, H31_psi K v * (H31_psi K y * e (v * (y + y⁻¹))) := by
    refine (Fintype.sum_equiv (Equiv.mulLeft₀ v hv) _ _ (fun y => ?_)).symm
    simp only [Equiv.mulLeft₀_apply]
    rw [H31_psi_mul, mul_inv]
    have harg : v * y + v ^ 2 * (v⁻¹ * y⁻¹) = v * (y + y⁻¹) := by
      linear_combination (v * y⁻¹) * hvv
    rw [harg]
    ring
  rw [h1, ← mul_sum, H31_T hp2 e he hv]
  have e2 := H31_psi_sq (K := K) hv
  linear_combination ((∑ x, H31_psi K x * e x) * (e (2 * v) + e (-(2 * v)))) * e2

end H31A

/-! ## (B) The index `ind x ∈ ℤ/n` (`χ(x) = μ^{ind x}`) and the cosets `C_t := {x ≠ 0 : ind x = t}` -/

section H31B

variable {p n : ℕ} [Fact p.Prime] [NeZero n] {M : Type*} [Field M]

/-- The standing data: `g` generates `(ZMod p)ˣ`, `χ(g)` and `μ` are primitive `n`-th roots of unity. -/
structure H31_Ctx (n : ℕ) (χ : MulChar (ZMod p) M) (g : (ZMod p)ˣ) (μ : M) : Prop where
  hg : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g
  hχg : IsPrimitiveRoot (χ (g : ZMod p)) n
  hμ : IsPrimitiveRoot μ n

theorem H31_pow_val_add {R : Type*} [Monoid R] (x : R) (hx : x ^ n = 1) (a b : ZMod n) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hx, pow_add]

theorem H31_pow_natCast_val {R : Type*} [Monoid R] (x : R) (hx : x ^ n = 1) (k : ℕ) :
    x ^ ((k : ZMod n)).val = x ^ k := by
  rw [ZMod.val_natCast, ← pow_eq_pow_mod _ hx]

theorem H31_half_val : (half n : ZMod n).val = n / 2 := by
  unfold half
  rw [ZMod.val_natCast]
  have := NeZero.pos n
  exact Nat.mod_eq_of_lt (by omega)

/-- A primitive `n`-th root with `n` even has `ζ^{n/2} = -1`. -/
theorem H31_pow_half (h2 : 2 ∣ n) {R : Type*} [Field R] {ζ : R} (hζ : IsPrimitiveRoot ζ n) :
    ζ ^ (n / 2) = -1 := by
  have hn0 : n ≠ 0 := NeZero.ne n
  have h := hζ.pow_of_dvd (show n / 2 ≠ 0 by omega) (Nat.div_dvd_of_dvd h2)
  rw [Nat.div_div_self h2 hn0] at h
  exact h.eq_neg_one_of_two_right

theorem H31_exists_pow (g : (ZMod p)ˣ) (hg : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (a : ZMod p) (ha : a ≠ 0) :
    ∃ k : ℕ, (g : ZMod p) ^ k = a := by
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1
    (mem_powers_iff_mem_zpowers.2 (hg (Units.mk0 a ha)))
  exact ⟨k, by rw [← Units.val_pow_eq_pow_val, hk, Units.val_mk0]⟩

/-- A generator `g` of `(ZMod p)ˣ` (`p` odd) is a non-square: `ψ(g^k) = (-1)^k`. -/
theorem H31_legendre_gen (hp2 : p ≠ 2) (g : (ZMod p)ˣ) (hg : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (k : ℕ) :
    quadraticChar (ZMod p) ((g : ZMod p) ^ k) = (-1) ^ k := by
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have hns : ¬ IsSquare (g : ZMod p) := by
    rw [ZMod.euler_criterion p (Units.ne_zero g)]
    intro h1
    have hu : g ^ (p / 2) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, h1, Units.val_one]
    exact pow_ne_one_of_lt_orderOf (by omega) (by rw [hord]; omega) hu
  rw [map_pow, quadraticChar_neg_one_iff_not_isSquare.2 hns]

open Classical in
variable (n) in
/-- `ind x`: the unique `t ∈ ℤ/n` with `χ(x) = μ^t` (junk `0` if there is none). -/
noncomputable def H31_ind (χ : MulChar (ZMod p) M) (μ : M) (x : ZMod p) : ZMod n :=
  if h : ∃ t : ZMod n, χ x = μ ^ t.val then h.choose else 0

variable {χ : MulChar (ZMod p) M} {g : (ZMod p)ˣ} {μ : M}

theorem H31_ind_spec {x : ZMod p} (h : ∃ t : ZMod n, χ x = μ ^ t.val) :
    χ x = μ ^ (H31_ind n χ μ x).val := by
  unfold H31_ind
  rw [dite_eq_left h]
  exact h.choose_spec

theorem H31_ind_eq (hμ : IsPrimitiveRoot μ n) {x : ZMod p} {t : ZMod n} (h : χ x = μ ^ t.val) :
    H31_ind n χ μ x = t := by
  have hs := H31_ind_spec ⟨t, h⟩
  rw [h] at hs
  exact ZMod.val_injective n (hμ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hs.symm)

theorem H31_chi_pow_n (hc : H31_Ctx n χ g μ) {x : ZMod p} (hx : x ≠ 0) : χ x ^ n = 1 := by
  obtain ⟨k, rfl⟩ := H31_exists_pow g hc.hg x hx
  rw [map_pow, pow_right_comm, hc.hχg.pow_eq_one, one_pow]

theorem H31_exists_ind (hc : H31_Ctx n χ g μ) {x : ZMod p} (hx : x ≠ 0) : ∃ t : ZMod n, χ x = μ ^ t.val := by
  obtain ⟨i, hi, hμi⟩ := hc.hμ.eq_pow_of_pow_eq_one (H31_chi_pow_n hc hx)
  exact ⟨(i : ZMod n), by rw [ZMod.val_cast_of_lt hi, hμi]⟩

theorem H31_ind_spec' (hc : H31_Ctx n χ g μ) {x : ZMod p} (hx : x ≠ 0) : χ x = μ ^ (H31_ind n χ μ x).val :=
  H31_ind_spec (H31_exists_ind hc hx)

theorem H31_ind_mul (hc : H31_Ctx n χ g μ) {x y : ZMod p} (hx : x ≠ 0) (hy : y ≠ 0) :
    H31_ind n χ μ (x * y) = H31_ind n χ μ x + H31_ind n χ μ y := by
  apply H31_ind_eq hc.hμ
  rw [map_mul, H31_ind_spec' hc hx, H31_ind_spec' hc hy, H31_pow_val_add μ hc.hμ.pow_eq_one]

theorem H31_ind_one (hc : H31_Ctx n χ g μ) : H31_ind n χ μ (1 : ZMod p) = 0 := by
  apply H31_ind_eq hc.hμ
  rw [map_one, ZMod.val_zero, pow_zero]

theorem H31_ind_inv (hc : H31_Ctx n χ g μ) {x : ZMod p} (hx : x ≠ 0) :
    H31_ind n χ μ x⁻¹ = -H31_ind n χ μ x := by
  have h := H31_ind_mul hc hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, H31_ind_one hc] at h
  linear_combination -h

theorem H31_ind_sq (hc : H31_Ctx n χ g μ) {x : ZMod p} (hx : x ≠ 0) :
    H31_ind n χ μ (x ^ 2) = 2 * H31_ind n χ μ x := by
  rw [sq, H31_ind_mul hc hx hx]
  ring

variable (n) in
/-- The coset `C_t := {x ≠ 0 : ind x = t}`. -/
noncomputable def H31_C (χ : MulChar (ZMod p) M) (μ : M) (t : ZMod n) : Finset (ZMod p) :=
  (univ.erase 0).filter (fun x => H31_ind n χ μ x = t)

theorem H31_mem_C (x : ZMod p) (t : ZMod n) : x ∈ H31_C n χ μ t ↔ x ≠ 0 ∧ H31_ind n χ μ x = t := by
  simp [H31_C]

theorem H31_image (hc : H31_Ctx n χ g μ) {x : ZMod p} (hx : x ≠ 0) (a : ZMod n) :
    (H31_C n χ μ a).image (fun w => x * w) = H31_C n χ μ (H31_ind n χ μ x + a) := by
  ext z
  simp only [mem_image, H31_mem_C]
  constructor
  · rintro ⟨w, ⟨hw0, hwa⟩, rfl⟩
    exact ⟨mul_ne_zero hx hw0, by rw [H31_ind_mul hc hx hw0, hwa]⟩
  · rintro ⟨hz0, hza⟩
    refine ⟨x⁻¹ * z, ⟨mul_ne_zero (inv_ne_zero hx) hz0, ?_⟩, by rw [← mul_assoc, mul_inv_cancel₀ hx, one_mul]⟩
    rw [H31_ind_mul hc (inv_ne_zero hx) hz0, H31_ind_inv hc hx, hza]
    ring

/-- Shifting a coset sum: `∑_{z ∈ C_{ind x + a}} f z = ∑_{w ∈ C_a} f (x w)`. -/
theorem H31_sum_shift {A : Type*} [AddCommMonoid A] (hc : H31_Ctx n χ g μ) {x : ZMod p} (hx : x ≠ 0)
    (a : ZMod n) (f : ZMod p → A) :
    ∑ z ∈ H31_C n χ μ (H31_ind n χ μ x + a), f z = ∑ w ∈ H31_C n χ μ a, f (x * w) := by
  rw [← H31_image hc hx a, sum_image (fun w _ w' _ h => mul_left_cancel₀ hx h)]

/-- Summing over all cosets: `∑_t ∑_{x ∈ C_t} F t x = ∑_{x ≠ 0} F (ind x) x`. -/
theorem H31_sum_cosets {A : Type*} [AddCommMonoid A] (F : ZMod n → ZMod p → A) :
    ∑ t, ∑ x ∈ H31_C n χ μ t, F t x = ∑ x ∈ univ.erase 0, F (H31_ind n χ μ x) x := by
  rw [← sum_fiberwise (univ.erase (0 : ZMod p)) (H31_ind n χ μ) (fun x => F (H31_ind n χ μ x) x)]
  refine sum_congr rfl (fun t _ => sum_congr rfl (fun x hx => ?_))
  rw [(mem_filter.1 hx).2]

theorem H31_mem_C0 (hc : H31_Ctx n χ g μ) (x : ZMod p) : x ∈ H31_C n χ μ 0 ↔ x ∈ Hpow p n := by
  rw [H31_mem_C]
  constructor
  · rintro ⟨hx0, hx⟩
    have h1 : χ x = 1 := by rw [H31_ind_spec' hc hx0, hx, ZMod.val_zero, pow_zero]
    obtain ⟨k, rfl⟩ := H31_exists_pow g hc.hg x hx0
    rw [map_pow] at h1
    obtain ⟨j, rfl⟩ := hc.hχg.dvd_of_pow_eq_one k h1
    exact ⟨(g : ZMod p) ^ j, pow_ne_zero _ (Units.ne_zero g), by ring⟩
  · rintro ⟨b, hb, rfl⟩
    refine ⟨pow_ne_zero _ hb, H31_ind_eq hc.hμ ?_⟩
    rw [ZMod.val_zero, pow_zero]
    obtain ⟨k, rfl⟩ := H31_exists_pow g hc.hg b hb
    rw [map_pow, map_pow, ← pow_mul, pow_mul', hc.hχg.pow_eq_one, one_pow]

theorem H31_card_C0 (hc : H31_Ctx n χ g μ) (hD : IsDiffSet p (Hpow p n) (n + 1) 1) :
    (H31_C n χ μ 0).card = n + 1 := by
  have h1 := hD.1
  have hset : (↑(H31_C n χ μ 0) : Set (ZMod p)) = Hpow p n := by
    ext x
    exact (Finset.mem_coe).trans (H31_mem_C0 hc x)
  rw [← hset, Set.ncard_coe_finset] at h1
  exact h1

theorem H31_C_nonempty (hc : H31_Ctx n χ g μ) (t : ZMod n) : ∃ x, x ∈ H31_C n χ μ t := by
  have h1 : (μ ^ t.val) ^ n = 1 := by rw [pow_right_comm, hc.hμ.pow_eq_one, one_pow]
  obtain ⟨i, -, hi⟩ := hc.hχg.eq_pow_of_pow_eq_one h1
  refine ⟨(g : ZMod p) ^ i, (H31_mem_C _ _).2 ⟨pow_ne_zero _ (Units.ne_zero g), H31_ind_eq hc.hμ ?_⟩⟩
  rw [map_pow, hi]

theorem H31_card_C (hc : H31_Ctx n χ g μ) (hD : IsDiffSet p (Hpow p n) (n + 1) 1) (t : ZMod n) :
    (H31_C n χ μ t).card = n + 1 := by
  obtain ⟨x, hx⟩ := H31_C_nonempty hc t
  rw [H31_mem_C] at hx
  rw [← hx.2, ← add_zero (H31_ind n χ μ x), ← H31_image hc hx.1,
    card_image_of_injective _ (mul_right_injective₀ hx.1), H31_card_C0 hc hD]

theorem H31_neg_one_not_mem (hp2 : p ≠ 2) (hpn : p = n ^ 2 + n + 1) (hev : Even n) :
    (-1 : ZMod p) ∉ Hpow p n := by
  rintro ⟨b, hb, hb1⟩
  have h1 := ZMod.pow_card_sub_one_eq_one hb
  rw [show p - 1 = n * (n + 1) by rw [hpn, Nat.add_sub_cancel]; ring, pow_mul, ← hb1,
    (Even.add_one hev).neg_one_pow] at h1
  exact H31_two_ne_zero hp2 (by linear_combination -h1)

theorem H31_ind_neg_one (hc : H31_Ctx n χ g μ) (hp2 : p ≠ 2) (hpn : p = n ^ 2 + n + 1) (hev : Even n) :
    H31_ind n χ μ (-1 : ZMod p) = half n := by
  have hm0 : (-1 : ZMod p) ≠ 0 := neg_ne_zero.2 one_ne_zero
  have h2t : H31_ind n χ μ (-1 : ZMod p) + H31_ind n χ μ (-1 : ZMod p) = 0 := by
    rw [← H31_ind_mul hc hm0 hm0, neg_one_mul, neg_neg, H31_ind_one hc]
  have ht0 : H31_ind n χ μ (-1 : ZMod p) ≠ 0 := by
    intro h0
    exact H31_neg_one_not_mem hp2 hpn hev ((H31_mem_C0 hc _).1 ((H31_mem_C _ _).2 ⟨hm0, h0⟩))
  set t := H31_ind n χ μ (-1 : ZMod p) with ht
  have hv : (t + t).val = 0 := by rw [h2t, ZMod.val_zero]
  rw [ZMod.val_add] at hv
  have hlt := ZMod.val_lt t
  have hpos : t.val ≠ 0 := by rwa [Ne, ZMod.val_eq_zero]
  obtain ⟨c, hcd⟩ := Nat.dvd_of_mod_eq_zero hv
  have hc1 : c = 1 := by
    rcases c with _ | _ | c
    · omega
    · rfl
    · nlinarith
  subst hc1
  apply ZMod.val_injective n
  rw [H31_half_val]
  omega

/-- The sign `(-1)^{ind x}` is the quadratic character (`n` even). -/
theorem H31_sgn_ind (hc : H31_Ctx n χ g μ) (hp2 : p ≠ 2) (hev : Even n) {K : Type*} [Field K] {x : ZMod p}
    (hx : x ≠ 0) : (-1 : K) ^ (H31_ind n χ μ x).val = H31_psi K x := by
  have hn0 : n ≠ 0 := NeZero.ne n
  have h2 : 2 ∣ n := even_iff_two_dvd.mp hev
  have hμm : μ ^ (n / 2) = -1 := H31_pow_half h2 hc.hμ
  have hgm : χ (g : ZMod p) ^ (n / 2) = -1 := H31_pow_half h2 hc.hχg
  have hM : (-1 : M) ≠ 1 := by
    rw [← hμm]
    exact hc.hμ.pow_ne_one_of_pos_of_lt (by omega) (by omega)
  have e1 : χ x ^ (n / 2) = (-1) ^ (H31_ind n χ μ x).val := by
    rw [H31_ind_spec' hc hx, pow_right_comm, hμm]
  obtain ⟨k, rfl⟩ := H31_exists_pow g hc.hg x hx
  have e2 : χ ((g : ZMod p) ^ k) ^ (n / 2) = (-1) ^ k := by
    rw [map_pow, pow_right_comm, hgm]
  have hpar : (-1 : M) ^ (H31_ind n χ μ ((g : ZMod p) ^ k)).val = (-1) ^ k := e1.symm.trans e2
  unfold H31_psi
  rw [H31_legendre_gen hp2 g hc.hg k]
  push_cast
  rcases Nat.even_or_odd (H31_ind n χ μ ((g : ZMod p) ^ k)).val with ha | ha <;>
    rcases Nat.even_or_odd k with hk | hk
  · rw [ha.neg_one_pow, hk.neg_one_pow]
  · rw [ha.neg_one_pow, hk.neg_one_pow] at hpar
    exact absurd hpar.symm hM
  · rw [ha.neg_one_pow, hk.neg_one_pow] at hpar
    exact absurd hpar hM
  · rw [ha.neg_one_pow, hk.neg_one_pow]

end H31B

/-! ## (C) The periods `η_t := ∑_{x ∈ C_t} ζ^x` (any field `K` with a primitive `p`-th root `ζ`) -/

section H31C

variable {p n : ℕ} [Fact p.Prime] [NeZero p] [NeZero n] {M : Type*} [Field M] {K : Type*} [Field K]
variable {χ : MulChar (ZMod p) M} {g : (ZMod p)ˣ} {μ : M} {ζ : K}

/-- The additive character `e(x) := ζ^x` (exponent `x.val`). -/
def H31_e (ζ : K) (x : ZMod p) : K := ζ ^ x.val

variable (n) in
/-- The Gauss period `η_t := ∑_{x ∈ C_t} e(x)`. -/
noncomputable def H31_eta (χ : MulChar (ZMod p) M) (μ : M) (ζ : K) (t : ZMod n) : K :=
  ∑ x ∈ H31_C n χ μ t, H31_e ζ x

theorem H31_e_add (hζ : IsPrimitiveRoot ζ p) (a b : ZMod p) : H31_e ζ (a + b) = H31_e ζ a * H31_e ζ b :=
  H31_pow_val_add ζ hζ.pow_eq_one a b

theorem H31_e_zero : H31_e ζ (0 : ZMod p) = 1 := by
  unfold H31_e
  rw [ZMod.val_zero, pow_zero]

theorem H31_e_natmul (hζ : IsPrimitiveRoot ζ p) (k : ℕ) (x : ZMod p) :
    H31_e ζ ((k : ZMod p) * x) = H31_e ζ x ^ k := by
  induction k with
  | zero => rw [Nat.cast_zero, zero_mul, H31_e_zero, pow_zero]
  | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, H31_e_add hζ, ih, pow_succ]

theorem H31_sum_e_zero (hζ : IsPrimitiveRoot ζ p) : ∑ x : ZMod p, H31_e ζ x = 0 := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have h1 : H31_e ζ (1 : ZMod p) = ζ := by
    unfold H31_e
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hp1, pow_one]
  have hs : (∑ x : ZMod p, H31_e ζ x) * ζ = ∑ x : ZMod p, H31_e ζ x := by
    rw [sum_mul]
    refine Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun x => ?_)
    simp only [Equiv.coe_addRight]
    rw [H31_e_add hζ, h1]
  have hne : ζ - 1 ≠ 0 := sub_ne_zero.2 (hζ.ne_one hp1)
  have h0 : (∑ x : ZMod p, H31_e ζ x) * (ζ - 1) = 0 := by linear_combination hs
  exact (mul_eq_zero.1 h0).resolve_right hne

theorem H31_sum_e_mul (hζ : IsPrimitiveRoot ζ p) {c : ZMod p} (hc : c ≠ 0) : ∑ x, H31_e ζ (c * x) = 0 := by
  rw [Fintype.sum_equiv (Equiv.mulLeft₀ c hc) (fun x => H31_e ζ (c * x)) (H31_e ζ) (fun x => rfl)]
  exact H31_sum_e_zero hζ

theorem H31_sum_e_nz (hζ : IsPrimitiveRoot ζ p) {c : ZMod p} (hc : c ≠ 0) :
    ∑ x ∈ univ.erase 0, H31_e ζ (c * x) = -1 := by
  rw [sum_erase_eq_sub (mem_univ _), H31_sum_e_mul hζ hc, mul_zero, H31_e_zero]
  ring

/-- Difference-set count: `∑_{h, h' ∈ H} f(h - h') = n f(0) + ∑_d f(d)` (`H = C_0`, `λ = 1`). -/
theorem H31_DS_sum (hc : H31_Ctx n χ g μ) (hD : IsDiffSet p (Hpow p n) (n + 1) 1) (f : ZMod p → K) :
    ∑ h ∈ H31_C n χ μ 0, ∑ h' ∈ H31_C n χ μ 0, f (h - h') = (n : K) * f 0 + ∑ d, f d := by
  classical
  rw [← sum_product' (H31_C n χ μ 0) (H31_C n χ μ 0) (fun h h' => f (h - h')),
    ← sum_fiberwise (H31_C n χ μ 0 ×ˢ H31_C n χ μ 0) (fun pr => pr.1 - pr.2) (fun pr => f (pr.1 - pr.2))]
  have hfib : ∀ d : ZMod p, ∑ pr ∈ (H31_C n χ μ 0 ×ˢ H31_C n χ μ 0).filter (fun pr => pr.1 - pr.2 = d),
      f (pr.1 - pr.2) = (if d = 0 then (n : K) * f d else 0) + f d := by
    intro d
    rw [sum_congr rfl (fun pr hpr => by rw [(mem_filter.1 hpr).2]), sum_const, nsmul_eq_mul]
    by_cases hd : d = 0
    · subst hd
      have hdiag : (H31_C n χ μ 0 ×ˢ H31_C n χ μ 0).filter (fun pr => pr.1 - pr.2 = 0) = (H31_C n χ μ 0).diag := by
        ext pr
        simp only [mem_filter, mem_product, mem_diag, sub_eq_zero]
        constructor
        · rintro ⟨⟨h1, -⟩, h3⟩
          exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩
          exact ⟨⟨h1, h3 ▸ h1⟩, h3⟩
      rw [hdiag, diag_card, H31_card_C0 hc hD, ite_eq_left rfl]
      push_cast
      ring
    · rw [ite_eq_right hd, zero_add]
      have h1 := hD.2 d hd
      have hcard : ((H31_C n χ μ 0 ×ˢ H31_C n χ μ 0).filter (fun pr => pr.1 - pr.2 = d)).card = 1 := by
        rw [← Nat.card_eq_finsetCard, ← h1]
        exact Nat.card_congr (Equiv.subtypeEquivRight (fun pr => by
          simp only [mem_filter, mem_product, H31_mem_C0 hc, and_assoc]))
      rw [hcard, Nat.cast_one, one_mul]
  rw [sum_congr rfl (fun d _ => hfib d), sum_add_distrib, sum_ite_eq' univ (0 : ZMod p) (fun d => (n : K) * f d),
    ite_eq_left (mem_univ _)]

/-- (L1) for the periods: `η_{s + ind 5} = η_s^5` in characteristic 5. -/
theorem H31_eta_frob [CharP K 5] (hc : H31_Ctx n χ g μ) (hζ : IsPrimitiveRoot ζ p) (h5 : (5 : ZMod p) ≠ 0)
    (s : ZMod n) : H31_eta n χ μ ζ (s + H31_ind n χ μ 5) = H31_eta n χ μ ζ s ^ 5 := by
  unfold H31_eta
  rw [add_comm, H31_sum_shift hc h5, sum_pow_char]
  refine sum_congr rfl (fun w _ => ?_)
  have := H31_e_natmul hζ 5 w
  rw [Nat.cast_ofNat] at this
  exact this

/-- `η_{s + n/2} = ∑_{z ∈ C_s} e(-z)`. -/
theorem H31_eta_half (hc : H31_Ctx n χ g μ) (hp2 : p ≠ 2) (hpn : p = n ^ 2 + n + 1) (hev : Even n) (s : ZMod n) :
    H31_eta n χ μ ζ (s + half n) = ∑ z ∈ H31_C n χ μ s, H31_e ζ (-1 * z) := by
  unfold H31_eta
  rw [← H31_ind_neg_one hc hp2 hpn hev, add_comm, H31_sum_shift hc (neg_ne_zero.2 one_ne_zero)]

/-- (L2) for the periods: `η_s η_{s+n/2} = n`. -/
theorem H31_eta_L2 (hc : H31_Ctx n χ g μ) (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) (hpn : p = n ^ 2 + n + 1)
    (hev : Even n) (hD : IsDiffSet p (Hpow p n) (n + 1) 1) (s : ZMod n) :
    H31_eta n χ μ ζ s * H31_eta n χ μ ζ (s + half n) = n := by
  obtain ⟨c, hcs⟩ := H31_C_nonempty hc s
  rw [H31_mem_C] at hcs
  have hsh : ∀ F : ZMod p → K, ∑ a ∈ H31_C n χ μ s, F a = ∑ h ∈ H31_C n χ μ 0, F (c * h) := by
    intro F
    rw [← H31_sum_shift hc hcs.1, add_zero, hcs.2]
  rw [H31_eta_half hc hp2 hpn hev, H31_eta, sum_mul_sum]
  simp only [hsh]
  have hterm : ∀ h h' : ZMod p, H31_e ζ (c * h) * H31_e ζ (-1 * (c * h')) = H31_e ζ (c * (h - h')) := by
    intro h h'
    rw [← H31_e_add hζ]
    congr 1
    ring
  simp only [hterm]
  rw [H31_DS_sum hc hD (fun d => H31_e ζ (c * d)), H31_sum_e_mul hζ hcs.1, mul_zero, H31_e_zero, mul_one,
    add_zero]

/-- (L3) for the periods: `∑_t η_t η_{s+t} = -(n+1)` for `s ≠ n/2`. -/
theorem H31_eta_L3 (hc : H31_Ctx n χ g μ) (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) (hpn : p = n ^ 2 + n + 1)
    (hev : Even n) (hD : IsDiffSet p (Hpow p n) (n + 1) 1) (s : ZMod n) (hs : s ≠ half n) :
    ∑ t, H31_eta n χ μ ζ t * H31_eta n χ μ ζ (s + t) = -((n : K) + 1) := by
  have e1 : ∑ t, H31_eta n χ μ ζ t * H31_eta n χ μ ζ (s + t) =
      ∑ t, ∑ x ∈ H31_C n χ μ t, H31_e ζ x * H31_eta n χ μ ζ (s + t) := by
    refine sum_congr rfl (fun t _ => ?_)
    rw [H31_eta, sum_mul]
  have e2 : ∑ t, ∑ x ∈ H31_C n χ μ t, H31_e ζ x * H31_eta n χ μ ζ (s + t) =
      ∑ x ∈ univ.erase 0, H31_e ζ x * H31_eta n χ μ ζ (s + H31_ind n χ μ x) :=
    H31_sum_cosets (fun t x => H31_e ζ x * H31_eta n χ μ ζ (s + t))
  have e3 : ∀ x ∈ univ.erase (0 : ZMod p), H31_e ζ x * H31_eta n χ μ ζ (s + H31_ind n χ μ x) =
      ∑ w ∈ H31_C n χ μ s, H31_e ζ ((1 + w) * x) := by
    intro x hx
    rw [H31_eta, add_comm, H31_sum_shift hc (ne_of_mem_erase hx), mul_sum]
    refine sum_congr rfl (fun w _ => ?_)
    rw [← H31_e_add hζ]
    congr 1
    ring
  have e4 : ∀ w ∈ H31_C n χ μ s, ∑ x ∈ univ.erase (0 : ZMod p), H31_e ζ ((1 + w) * x) = -1 := by
    intro w hw
    rw [H31_mem_C] at hw
    refine H31_sum_e_nz hζ (fun h0 => hs ?_)
    have hw1 : w = -1 := by linear_combination h0
    rw [← hw.2, hw1, H31_ind_neg_one hc hp2 hpn hev]
  rw [e1, e2, sum_congr rfl e3, sum_comm, sum_congr rfl e4, sum_const, H31_card_C hc hD, nsmul_eq_mul]
  push_cast
  ring

/-- `(z/2)^2` maps `C_s` injectively onto `C_{2s - 2 ind 2}`. -/
theorem H31_sq_injOn (hc : H31_Ctx n χ g μ) (hp2 : p ≠ 2) (hpn : p = n ^ 2 + n + 1) (hev : Even n) (s : ZMod n) :
    Set.InjOn (fun z : ZMod p => (z * 2⁻¹) ^ 2) (H31_C n χ μ s : Set (ZMod p)) := by
  have h2 : (2 : ZMod p)⁻¹ ≠ 0 := inv_ne_zero (H31_two_ne_zero hp2)
  intro z hz z' hz' hzz
  simp only [mem_coe, H31_mem_C] at hz hz'
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hzz with h | h
  · exact mul_right_cancel₀ h2 h
  · exfalso
    have hz1 : z = -1 * z' := mul_right_cancel₀ h2 (by rw [h]; ring)
    have hi := congrArg (H31_ind n χ μ) hz1
    rw [H31_ind_mul hc (neg_ne_zero.2 one_ne_zero) hz'.1, H31_ind_neg_one hc hp2 hpn hev, hz.2, hz'.2] at hi
    have hh : half n = (0 : ZMod n) := by linear_combination -hi
    have hv := congrArg ZMod.val hh
    rw [H31_half_val, ZMod.val_zero] at hv
    have hn0 : n ≠ 0 := NeZero.ne n
    obtain ⟨r, hr⟩ := hev
    omega

theorem H31_sq_image (hc : H31_Ctx n χ g μ) (hp2 : p ≠ 2) (hpn : p = n ^ 2 + n + 1) (hev : Even n)
    (hD : IsDiffSet p (Hpow p n) (n + 1) 1) (s : ZMod n) :
    (H31_C n χ μ s).image (fun z : ZMod p => (z * 2⁻¹) ^ 2) = H31_C n χ μ (2 * s - 2 * H31_ind n χ μ 2) := by
  have h2 : (2 : ZMod p) ≠ 0 := H31_two_ne_zero hp2
  have hsub : (H31_C n χ μ s).image (fun z : ZMod p => (z * 2⁻¹) ^ 2) ⊆ H31_C n χ μ (2 * s - 2 * H31_ind n χ μ 2) := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := mem_image.1 hw
    rw [H31_mem_C] at hz ⊢
    have hz2 : z * 2⁻¹ ≠ 0 := mul_ne_zero hz.1 (inv_ne_zero h2)
    refine ⟨pow_ne_zero _ hz2, ?_⟩
    rw [H31_ind_sq hc hz2, H31_ind_mul hc hz.1 (inv_ne_zero h2), H31_ind_inv hc h2, hz.2]
    ring
  refine eq_of_subset_of_card_le hsub ?_
  rw [card_image_of_injOn (H31_sq_injOn hc hp2 hpn hev s), H31_card_C hc hD, H31_card_C hc hD]

/-- The fourth equation for the periods: `∑_t (-1)^t η_t η_{u-t} = (η_s + η_{s+n/2}) ∑_t (-1)^t η_t`,
`u = 2s - 2 ind 2` (Salié's evaluation). -/
theorem H31_eta_L4 (hc : H31_Ctx n χ g μ) (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) (hpn : p = n ^ 2 + n + 1)
    (hev : Even n) (hD : IsDiffSet p (Hpow p n) (n + 1) 1) (s : ZMod n) :
    ∑ t, (-1 : K) ^ t.val * H31_eta n χ μ ζ t * H31_eta n χ μ ζ (2 * s - 2 * H31_ind n χ μ 2 - t) =
      (H31_eta n χ μ ζ s + H31_eta n χ μ ζ (s + half n)) * ∑ t, (-1 : K) ^ t.val * H31_eta n χ μ ζ t := by
  have h2 : (2 : ZMod p) ≠ 0 := H31_two_ne_zero hp2
  have h2i : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  have hz0 : H31_psi K (0 : ZMod p) * H31_e ζ (0 : ZMod p) = 0 := by rw [H31_psi_zero, zero_mul]
  -- (a) the alternating sum of periods is the Gauss sum `G = ∑_x ψ(x) e(x)`
  have hGt : ∑ t, (-1 : K) ^ t.val * H31_eta n χ μ ζ t = ∑ x : ZMod p, H31_psi K x * H31_e ζ x := by
    have e1 : ∑ t, (-1 : K) ^ t.val * H31_eta n χ μ ζ t =
        ∑ t, ∑ x ∈ H31_C n χ μ t, (-1 : K) ^ t.val * H31_e ζ x := by
      refine sum_congr rfl (fun t _ => ?_)
      rw [H31_eta, mul_sum]
    have e2 : ∑ t, ∑ x ∈ H31_C n χ μ t, (-1 : K) ^ t.val * H31_e ζ x =
        ∑ x ∈ univ.erase 0, (-1 : K) ^ (H31_ind n χ μ x).val * H31_e ζ x :=
      H31_sum_cosets (fun t x => (-1 : K) ^ t.val * H31_e ζ x)
    rw [e1, e2, ← sum_erase (univ : Finset (ZMod p)) (f := fun x => H31_psi K x * H31_e ζ x) hz0]
    exact sum_congr rfl (fun x hx => by rw [H31_sgn_ind hc hp2 hev (ne_of_mem_erase hx)])
  rw [hGt]
  -- (b) the left side is a sum of Salié sums over `C_u`
  have e1 : ∑ t, (-1 : K) ^ t.val * H31_eta n χ μ ζ t * H31_eta n χ μ ζ (2 * s - 2 * H31_ind n χ μ 2 - t) =
      ∑ t, ∑ x ∈ H31_C n χ μ t,
        (-1 : K) ^ t.val * H31_e ζ x * H31_eta n χ μ ζ (2 * s - 2 * H31_ind n χ μ 2 - t) := by
    refine sum_congr rfl (fun t _ => ?_)
    rw [H31_eta, mul_sum, sum_mul]
  have e2 : ∑ t, ∑ x ∈ H31_C n χ μ t,
        (-1 : K) ^ t.val * H31_e ζ x * H31_eta n χ μ ζ (2 * s - 2 * H31_ind n χ μ 2 - t) =
      ∑ x ∈ univ.erase 0, (-1 : K) ^ (H31_ind n χ μ x).val * H31_e ζ x *
        H31_eta n χ μ ζ (2 * s - 2 * H31_ind n χ μ 2 - H31_ind n χ μ x) :=
    H31_sum_cosets (fun t x => (-1 : K) ^ t.val * H31_e ζ x * H31_eta n χ μ ζ (2 * s - 2 * H31_ind n χ μ 2 - t))
  have e3 : ∀ x ∈ univ.erase (0 : ZMod p), (-1 : K) ^ (H31_ind n χ μ x).val * H31_e ζ x *
      H31_eta n χ μ ζ (2 * s - 2 * H31_ind n χ μ 2 - H31_ind n χ μ x) =
      ∑ w ∈ H31_C n χ μ (2 * s - 2 * H31_ind n χ μ 2), H31_psi K x * H31_e ζ (x + w * x⁻¹) := by
    intro x hx
    have hx0 := ne_of_mem_erase hx
    rw [H31_sgn_ind hc hp2 hev hx0,
      show 2 * s - 2 * H31_ind n χ μ 2 - H31_ind n χ μ x = H31_ind n χ μ x⁻¹ + (2 * s - 2 * H31_ind n χ μ 2) by
        rw [H31_ind_inv hc hx0]; ring,
      H31_eta, H31_sum_shift hc (inv_ne_zero hx0), mul_sum]
    refine sum_congr rfl (fun w _ => ?_)
    rw [mul_assoc, ← H31_e_add hζ]
    congr 2
    ring
  rw [e1, e2, sum_congr rfl e3, sum_comm]
  rw [sum_congr rfl (fun (w : ZMod p) _ => sum_erase (univ : Finset (ZMod p))
    (f := fun x => H31_psi K x * H31_e ζ (x + w * x⁻¹)) (by rw [H31_psi_zero, zero_mul]))]
  -- (c) reindex `C_u` by `C_s` (`w = (z/2)^2`), (d) Salié
  rw [← H31_sq_image hc hp2 hpn hev hD s, sum_image (H31_sq_injOn hc hp2 hpn hev s)]
  rw [sum_congr rfl (fun z hz => H31_salie hp2 (H31_e ζ) (H31_e_add hζ)
    (mul_ne_zero ((H31_mem_C _ _).1 hz).1 (inv_ne_zero h2)))]
  -- (e) `e(2 (z/2)) + e(-2 (z/2)) = e(z) + e(-z)`, summed over `C_s`
  have hfin : ∀ z ∈ H31_C n χ μ s, (∑ x : ZMod p, H31_psi K x * H31_e ζ x) *
      (H31_e ζ (2 * (z * 2⁻¹)) + H31_e ζ (-(2 * (z * 2⁻¹)))) =
      (∑ x : ZMod p, H31_psi K x * H31_e ζ x) * (H31_e ζ z + H31_e ζ (-1 * z)) := by
    intro z _
    rw [show 2 * (z * 2⁻¹) = z by linear_combination z * h2i,
      show -z = -1 * z by ring]
  rw [sum_congr rfl hfin, ← mul_sum, sum_add_distrib, H31_eta_half hc hp2 hpn hev, H31_eta]
  ring

end H31C

/-! ## (D) Descent to `GaloisField 5 d` and the target -/

section H31D

/-- An element `z` of a field `L` with `z^{|F|} = z` lies in the image of any ring hom `φ : F →+* L` from a finite
field (root count of `X^q - X`; the same counting as `H28_mem_range`). -/
theorem H31_mem_range {F L : Type*} [Field F] [Fintype F] [Field L] (φ : F →+* L) (z : L)
    (hz : z ^ Fintype.card F = z) : ∃ x : F, φ x = z := by
  classical
  have h1q : 1 < Fintype.card F := Fintype.one_lt_card
  have hinj := φ.injective
  set P : Polynomial L := Polynomial.X ^ (Fintype.card F) - Polynomial.X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero L h1q
  have hroot : ∀ s : L, s ^ (Fintype.card F) = s → s ∈ P.roots.toFinset := by
    intro s hs
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def, hP]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hs, sub_self]
  by_contra hnot
  set A : Finset L := univ.image φ with hA
  have hAcard : A.card = Fintype.card F := by rw [hA, card_image_of_injective _ hinj, card_univ]
  have hzA : z ∉ A := by
    intro hzA
    obtain ⟨x, -, hx⟩ := mem_image.mp hzA
    exact hnot ⟨x, hx⟩
  have hsub : insert z A ⊆ P.roots.toFinset := by
    intro s hs
    rcases mem_insert.mp hs with hs | hs
    · rw [hs]
      exact hroot _ hz
    · obtain ⟨x, -, rfl⟩ := mem_image.mp hs
      apply hroot
      rw [← map_pow, FiniteField.pow_card]
  have h1 := card_le_card hsub
  rw [card_insert_of_notMem hzA, hAcard] at h1
  have h2 := (Multiset.toFinset_card_le P.roots).trans (Polynomial.card_roots' P)
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq L h1q] at h2
  omega

/-- `1 + (n-1) p = n^3`. -/
theorem H31_nat_L2 (n : ℕ) (hn : 1 ≤ n) : 1 + (n - 1) * pp n = n ^ 3 := by
  unfold pp
  zify [hn]
  ring

variable (n) in
/-- `Y_t := n η_t` (the paper's normalisation; it lands the constants `n^3`, `n(1-p)`). -/
noncomputable def H31_Y [NeZero n] [Fact (pp n).Prime] [NeZero (pp n)] {M : Type*} [Field M] {K : Type*} [Field K]
    (χ : MulChar (ZMod (pp n)) M) (μ : M) (ζ : K) (t : ZMod n) : K :=
  (n : K) * H31_eta n χ μ ζ t

/-- The four equations for `Y_t := n η_t` in `K` (characteristic 5, `ζ` a primitive `p`-th root). -/
theorem H31_Y_eqs (n : ℕ) [NeZero n] (hev : Even n) [Fact (pp n).Prime] [NeZero (pp n)] {M : Type*} [Field M]
    (χ : MulChar (ZMod (pp n)) M) (g : (ZMod (pp n))ˣ) (μ : M) (hc : H31_Ctx n χ g μ)
    (hD : IsDiffSet (pp n) (Hpow (pp n) n) (n + 1) 1) (σ θ : ℕ) (h5 : χ 5 = μ ^ σ) (h2 : χ 2 = μ ^ θ)
    {K : Type*} [Field K] [CharP K 5] {ζ : K} (hζ : IsPrimitiveRoot ζ (pp n)) :
    (∀ s, H31_Y n χ μ ζ (s + (σ : ZMod n)) = H31_Y n χ μ ζ s ^ 5) ∧
    (∀ s, H31_Y n χ μ ζ s * H31_Y n χ μ ζ (s + half n) = (n : K) ^ 3) ∧
    (∀ s, s ≠ half n → ∑ t, H31_Y n χ μ ζ t * H31_Y n χ μ ζ (s + t) = (n : K) * (1 - (pp n : K))) ∧
    (∀ s, ∑ t, (-1 : K) ^ t.val * H31_Y n χ μ ζ t * H31_Y n χ μ ζ (2 * s - 2 * (θ : ZMod n) - t) =
      (H31_Y n χ μ ζ s + H31_Y n χ μ ζ (s + half n)) * ∑ t, (-1 : K) ^ t.val * H31_Y n χ μ ζ t) := by
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  have hpn : pp n = n ^ 2 + n + 1 := rfl
  have hp7 : 7 ≤ pp n := by
    have h2n : 2 ≤ n := by
      obtain ⟨r, hr⟩ := hev
      omega
    have : 4 ≤ n ^ 2 := by nlinarith
    rw [hpn]
    omega
  have hp2 : pp n ≠ 2 := by omega
  have h5ne : (5 : ZMod (pp n)) ≠ 0 := by
    intro h
    have h' : ((5 : ℕ) : ZMod (pp n)) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have hi5 : H31_ind n χ μ (5 : ZMod (pp n)) = (σ : ZMod n) :=
    H31_ind_eq hc.hμ (by rw [H31_pow_natCast_val μ hc.hμ.pow_eq_one, h5])
  have hi2 : H31_ind n χ μ (2 : ZMod (pp n)) = (θ : ZMod n) :=
    H31_ind_eq hc.hμ (by rw [H31_pow_natCast_val μ hc.hμ.pow_eq_one, h2])
  have hn5 : (n : K) ^ 5 = n := by
    have e := map_natCast (frobenius K 5) n
    rwa [frobenius_def] at e
  refine ⟨fun s => ?_, fun s => ?_, fun s hs => ?_, fun s => ?_⟩
  · show (n : K) * H31_eta n χ μ ζ (s + σ) = ((n : K) * H31_eta n χ μ ζ s) ^ 5
    rw [← hi5, H31_eta_frob hc hζ h5ne, mul_pow, hn5]
  · show (n : K) * H31_eta n χ μ ζ s * ((n : K) * H31_eta n χ μ ζ (s + half n)) = (n : K) ^ 3
    have e := H31_eta_L2 hc hζ hp2 hpn hev hD s
    linear_combination (n : K) ^ 2 * e
  · show ∑ t, (n : K) * H31_eta n χ μ ζ t * ((n : K) * H31_eta n χ μ ζ (s + t)) = (n : K) * (1 - (pp n : K))
    have e := H31_eta_L3 hc hζ hp2 hpn hev hD s hs
    have e' : ∑ t, (n : K) * H31_eta n χ μ ζ t * ((n : K) * H31_eta n χ μ ζ (s + t)) =
        (n : K) ^ 2 * ∑ t, H31_eta n χ μ ζ t * H31_eta n χ μ ζ (s + t) := by
      rw [mul_sum]
      refine sum_congr rfl (fun t _ => ?_)
      ring
    rw [e', e]
    unfold pp
    push_cast
    ring
  · show ∑ t, (-1 : K) ^ t.val * ((n : K) * H31_eta n χ μ ζ t) *
        ((n : K) * H31_eta n χ μ ζ (2 * s - 2 * (θ : ZMod n) - t)) =
      ((n : K) * H31_eta n χ μ ζ s + (n : K) * H31_eta n χ μ ζ (s + half n)) *
        ∑ t, (-1 : K) ^ t.val * ((n : K) * H31_eta n χ μ ζ t)
    have e := H31_eta_L4 hc hζ hp2 hpn hev hD s
    rw [hi2] at e
    have e' : ∑ t, (-1 : K) ^ t.val * ((n : K) * H31_eta n χ μ ζ t) *
        ((n : K) * H31_eta n χ μ ζ (2 * s - 2 * (θ : ZMod n) - t)) =
        (n : K) ^ 2 * ∑ t, (-1 : K) ^ t.val * H31_eta n χ μ ζ t *
          H31_eta n χ μ ζ (2 * s - 2 * (θ : ZMod n) - t) := by
      rw [mul_sum]
      refine sum_congr rfl (fun t _ => ?_)
      ring
    have e'' : ∑ t, (-1 : K) ^ t.val * ((n : K) * H31_eta n χ μ ζ t) =
        (n : K) * ∑ t, (-1 : K) ^ t.val * H31_eta n χ μ ζ t := by
      rw [mul_sum]
      refine sum_congr rfl (fun t _ => ?_)
      ring
    rw [e', e'', e]
    ring

/-- Xia's Theorem 3.4(b) in our instance, for any EVEN `n` with `p = n^2+n+1` prime. -/
theorem H31_main (n : ℕ) [NeZero n] (hev : Even n) (hp : (pp n).Prime)
    {M : Type*} [Field M] (χ : MulChar (ZMod (pp n)) M) (g : (ZMod (pp n))ˣ)
    (hg : ∀ x : (ZMod (pp n))ˣ, x ∈ Subgroup.zpowers g) (hχg : IsPrimitiveRoot (χ (g : ZMod (pp n))) n) :
    IsDiffSet (pp n) (Hpow (pp n) n) (n + 1) 1 → ∀ (μ : M) (σ θ : ℕ), IsPrimitiveRoot μ n →
      χ 5 = μ ^ σ → χ 2 = μ ^ θ →
      ∃ y : ZMod n → GaloisField 5 (n / Nat.gcd σ n),
        L1 5 (σ : ℤ) y ∧ L2 (((1 + (n - 1) * pp n : ℕ) : GaloisField 5 (n / Nat.gcd σ n))) y ∧
        L3 ((n : GaloisField 5 (n / Nat.gcd σ n)) * (1 - (pp n : GaloisField 5 (n / Nat.gcd σ n)))) y ∧
        ∀ s : ZMod n, s.val < n / 2 →
          ∑ t, sgn t * y t * y (2 * s - 2 * (θ : ZMod n) - t) = (y s + y (s + half n)) * S y := by
  intro hD μ σ θ hμ h5 h2
  have : Fact (pp n).Prime := ⟨hp⟩
  have : NeZero (pp n) := ⟨hp.ne_zero⟩
  have hc : H31_Ctx n χ g μ := ⟨hg, hχg, hμ⟩
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  -- `5 ∤ p`, so `\bar F_5` has a primitive `p`-th root of unity `ζ`
  have h5p : ¬ 5 ∣ pp n := by
    intro hdv
    have h55 := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).1 hdv
    have h2n : 2 ≤ n := by
      obtain ⟨r, hr⟩ := hev
      omega
    have : 4 ≤ n ^ 2 := by nlinarith
    unfold pp at h55
    omega
  have : NeZero ((pp n : ℕ) : ZMod 5) := ⟨by rw [Ne, ZMod.natCast_eq_zero_iff]; exact h5p⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure (ZMod 5)) (pp n)
  obtain ⟨KL1, KL2, KL3, KL4⟩ := H31_Y_eqs n hev χ g μ hc hD σ θ h5 h2 hζ
  -- descent: `Y_s^{5^d} = Y_{s + dσ} = Y_s`, and the roots of `X^{5^d} - X` are the image of `F_{5^d}`
  have hd0 : n / Nat.gcd σ n ≠ 0 :=
    (Nat.div_pos (Nat.gcd_le_right σ (NeZero.pos n)) (Nat.gcd_pos_of_pos_right σ (NeZero.pos n))).ne'
  let : Fintype (GaloisField 5 (n / Nat.gcd σ n)) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 5 (n / Nat.gcd σ n)) = 5 ^ (n / Nat.gcd σ n) := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 5 _ hd0]
  let φ : GaloisField 5 (n / Nat.gcd σ n) →+* AlgebraicClosure (ZMod 5) :=
    (IsAlgClosed.lift (R := ZMod 5) (M := AlgebraicClosure (ZMod 5))
      (S := GaloisField 5 (n / Nat.gcd σ n))).toRingHom
  have hiter : ∀ j : ℕ, ∀ s, H31_Y n χ μ ζ s ^ (5 ^ j) = H31_Y n χ μ ζ (s + ((j * σ : ℕ) : ZMod n)) := by
    intro j
    induction j with
    | zero =>
      intro s
      simp
    | succ j ih =>
      intro s
      rw [pow_succ, pow_mul, ih, ← KL1]
      congr 1
      push_cast
      ring
  have hdvd : n ∣ n / Nat.gcd σ n * σ := by
    obtain ⟨c, hcσ⟩ := Nat.gcd_dvd_left σ n
    refine ⟨c, ?_⟩
    calc n / Nat.gcd σ n * σ = n / Nat.gcd σ n * (Nat.gcd σ n * c) := by rw [← hcσ]
      _ = n * c := by rw [← mul_assoc, Nat.div_mul_cancel (Nat.gcd_dvd_right σ n)]
  have hfix : ∀ s, H31_Y n χ μ ζ s ^ Fintype.card (GaloisField 5 (n / Nat.gcd σ n)) = H31_Y n χ μ ζ s := by
    intro s
    rw [hcard, hiter, (ZMod.natCast_eq_zero_iff _ _).2 hdvd, add_zero]
  choose y hy using fun s => H31_mem_range φ (H31_Y n χ μ ζ s) (hfix s)
  have hne_half : ∀ s : ZMod n, s.val < n / 2 → s ≠ half n := by
    intro s hs h
    rw [h, H31_half_val] at hs
    exact lt_irrefl _ hs
  refine ⟨y, fun s => ?_, fun s _ => ?_, fun s hs => ?_, fun s _ => ?_⟩
  · apply φ.injective
    rw [map_pow, hy, hy, Int.cast_natCast]
    exact KL1 s
  · apply φ.injective
    rw [map_mul, hy, hy, map_natCast, H31_nat_L2 n hn1]
    push_cast
    exact KL2 s
  · apply φ.injective
    simp only [map_sum, map_mul, map_sub, map_one, map_natCast, hy]
    exact KL3 s (hne_half s hs)
  · apply φ.injective
    unfold S sgn
    simp only [map_sum, map_mul, map_add, map_pow, map_neg, map_one, hy]
    exact KL4 s

/-- Token for token the hypothesis `hX34b` of row `prop_6_1_X12_X34b`. -/
theorem L10_hX34b_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (_heo : Odd e) (hp : (pp n).Prime)
    {M : Type*} [Field M] (χ : MulChar (ZMod (pp n)) M) (g : (ZMod (pp n))ˣ)
    (hg : ∀ x : (ZMod (pp n))ˣ, x ∈ Subgroup.zpowers g) (hχg : IsPrimitiveRoot (χ (g : ZMod (pp n))) n) :
    IsDiffSet (pp n) (Hpow (pp n) n) (n + 1) 1 → ∀ (μ : M) (σ θ : ℕ), IsPrimitiveRoot μ n →
      χ 5 = μ ^ σ → χ 2 = μ ^ θ →
      ∃ y : ZMod n → GaloisField 5 (n / Nat.gcd σ n),
        L1 5 (σ : ℤ) y ∧ L2 (((1 + (n - 1) * pp n : ℕ) : GaloisField 5 (n / Nat.gcd σ n))) y ∧
        L3 ((n : GaloisField 5 (n / Nat.gcd σ n)) * (1 - (pp n : GaloisField 5 (n / Nat.gcd σ n)))) y ∧
        ∀ s : ZMod n, s.val < n / 2 →
          ∑ t, sgn t * y t * y (2 * s - 2 * (θ : ZMod n) - t) = (y s + y (s + half n)) * S y := by
  have hev : Even n := by
    rw [hne]
    exact Nat.even_pow.2 ⟨even_two, by omega⟩
  exact H31_main n hev hp χ g hg hχg

end H31D

end Xia.Proofs

#print axioms Xia.Proofs.H31_salie
#print axioms Xia.Proofs.H31_main
#print axioms Xia.Proofs.L10_hX34b_proved
