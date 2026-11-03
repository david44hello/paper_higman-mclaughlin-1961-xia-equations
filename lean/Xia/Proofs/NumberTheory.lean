/- Xia/Proofs/NumberTheory.lean — proofs of the rows lem_2_2_fourth_power, lem_2_2_sigma, pow2_range, lem_2_2_pow2, intro_sum_L2, thm_6_4_step1 and 1 more of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry

namespace Xia.Proofs

open Xia Finset

/-! ## Small arithmetic helpers -/

/-- `2^(3+2k) ≡ 8` and `2^(4+2k) ≡ 16 (mod 24)`. -/
lemma H1_pow2_mod24 (k : ℕ) : 2 ^ (3 + 2 * k) % 24 = 8 ∧ 2 ^ (4 + 2 * k) % 24 = 16 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have e1 : 2 ^ (3 + 2 * (k + 1)) = 4 * 2 ^ (3 + 2 * k) := by ring
    have e2 : 2 ^ (4 + 2 * (k + 1)) = 4 * 2 ^ (4 + 2 * k) := by ring
    rw [e1, e2]
    omega

/-- `4^j ≡ 1` or `4 (mod 5)`. -/
lemma H1_four_pow_mod5 (j : ℕ) : 4 ^ j % 5 = 1 ∨ 4 ^ j % 5 = 4 := by
  induction j with
  | zero => left; rfl
  | succ j ih => rw [pow_succ]; omega

/-- If `8 ∣ n` and `pp n` is prime then `n ≥ 8` (`pp 0 = 1` is not prime). -/
lemma H1_n_ge (n : ℕ) (h8 : 8 ∣ n) (hp : (pp n).Prime) : 8 ≤ n := by
  rcases h8 with ⟨k, rfl⟩
  rcases k with _ | k
  · norm_num [pp] at hp
  · omega

/-- `pp n ≥ n + 1`. -/
lemma H1_pp_ge (n : ℕ) : n + 1 ≤ pp n := by
  unfold pp; omega

/-! ## Lemma 2.2, first sentence: Jacobi reciprocity twice -/

/-- `J(2n+1 | 3) = 1 ↔ 3 ∣ n`. -/
lemma H1_J_three (n : ℕ) : jacobiSym ((2 * n + 1 : ℕ) : ℤ) 3 = 1 ↔ 3 ∣ n := by
  rw [jacobiSym.mod_left, ← Int.natCast_mod]
  have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases this with h | h | h
  · have e : (2 * n + 1) % 3 = 1 := by omega
    rw [e]
    have hv : jacobiSym ((1 : ℕ) : ℤ) 3 = 1 := by norm_num
    rw [hv]
    constructor
    · intro _; omega
    · intro _; rfl
  · have e : (2 * n + 1) % 3 = 0 := by omega
    rw [e]
    have hv : jacobiSym ((0 : ℕ) : ℤ) 3 = 0 := by norm_num
    rw [hv]
    constructor
    · intro h'; norm_num at h'
    · intro h'; omega
  · have e : (2 * n + 1) % 3 = 2 := by omega
    rw [e]
    have hv : jacobiSym ((2 : ℕ) : ℤ) 3 = -1 := by norm_num
    rw [hv]
    constructor
    · intro h'; norm_num at h'
    · intro h'; omega

/-- `J(4 | 2n+1) = 1`. -/
lemma H1_J_four (n : ℕ) : jacobiSym 4 (2 * n + 1) = 1 := by
  have e : (4 : ℤ) = 2 ^ 2 := by norm_num
  rw [e]
  apply jacobiSym.sq_one'
  show Nat.gcd (2 : ℤ).natAbs ((2 * n + 1 : ℕ) : ℤ).natAbs = 1
  rw [Int.natAbs_natCast, show (2 : ℤ).natAbs = 2 from rfl, Nat.gcd_rec]
  have : (2 * n + 1) % 2 = 1 := by omega
  rw [this]
  exact Nat.gcd_one_left 2

/-- The paper's chain (s2_xia.tex:30-33): `J(2n+1 | p) = J(2n+1 | 3)` for `8 ∣ n`. -/
lemma H1_jacobi_chain (n : ℕ) (h8 : 8 ∣ n) :
    jacobiSym ((2 * n + 1 : ℕ) : ℤ) (pp n) = jacobiSym ((2 * n + 1 : ℕ) : ℤ) 3 := by
  have hw4 : (2 * n + 1) % 4 = 1 := by omega
  have hpodd : Odd (pp n) := by
    rcases h8 with ⟨k, rfl⟩
    exact ⟨32 * k ^ 2 + 4 * k, by unfold pp; ring⟩
  rw [jacobiSym.quadratic_reciprocity_one_mod_four hw4 hpodd,
    jacobiSym.quadratic_reciprocity_one_mod_four hw4 (by decide : Odd 3)]
  have hmod : (4 * ((pp n : ℕ) : ℤ)) % ((2 * n + 1 : ℕ) : ℤ) = 3 % ((2 * n + 1 : ℕ) : ℤ) := by
    have e : 4 * ((pp n : ℕ) : ℤ) = 3 + ((2 * n + 1 : ℕ) : ℤ) * ((2 * n + 1 : ℕ) : ℤ) := by
      unfold pp; push_cast; ring
    rw [e, Int.add_mul_emod_self_left]
  have key := jacobiSym.mod_left' hmod
  rw [jacobiSym.mul_left, H1_J_four, one_mul] at key
  rw [key]
  norm_num

/-- `2n+1` is a square mod `p` iff `3 ∣ n` (for `8 ∣ n`, `p = pp n` prime). -/
lemma H1_sq_iff (n : ℕ) [hF : Fact (pp n).Prime] (h8 : 8 ∣ n) :
    IsSquare ((2 * n + 1 : ℕ) : ZMod (pp n)) ↔ 3 ∣ n := by
  have hn8 := H1_n_ge n h8 hF.out
  have hne : ((2 * n + 1 : ℕ) : ZMod (pp n)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have hle := Nat.le_of_dvd (by omega) hd
    have : 2 * n + 1 < pp n := by unfold pp; nlinarith
    omega
  rw [← legendreSym.eq_one_iff' (pp n) hne, jacobiSym.legendreSym.to_jacobiSym,
    H1_jacobi_chain n h8, H1_J_three]

/-- `(2n+1)^2 = -3` in `ZMod (pp n)` (`4p = (2n+1)^2 + 3`). -/
lemma H1_w_sq (n : ℕ) : (((2 * n + 1 : ℕ) : ZMod (pp n))) ^ 2 = -3 := by
  have hnat : (2 * n + 1) ^ 2 + 3 = 4 * pp n := by unfold pp; ring
  have h : (((2 * n + 1) ^ 2 + 3 : ℕ) : ZMod (pp n)) = 4 * ((pp n : ℕ) : ZMod (pp n)) := by
    rw [hnat, Nat.cast_mul]; norm_num
  rw [ZMod.natCast_self, mul_zero] at h
  push_cast at h ⊢
  linear_combination h

/-- A fourth root of `-1` in `ZMod p` for `p ≡ 1 (mod 8)`: `ζ = (1+i)/√2`. -/
lemma H1_zeta (n : ℕ) [hF : Fact (pp n).Prime] (h8 : 8 ∣ n) : ∃ ζ : ZMod (pp n), ζ ^ 4 = -1 := by
  have hp8 : pp n % 8 = 1 := by
    rcases h8 with ⟨k, rfl⟩
    have : pp (8 * k) = 8 * (8 * k ^ 2 + k) + 1 := by unfold pp; ring
    omega
  have hp1 : 2 ≤ pp n := hF.out.two_le
  have hp2 : pp n ≠ 2 := by omega
  obtain ⟨i, hi⟩ := ZMod.exists_sq_eq_neg_one_iff.2 (by omega : pp n % 4 ≠ 3)
  obtain ⟨s, hs⟩ := (ZMod.exists_sq_eq_two_iff hp2).2 (Or.inl hp8)
  have h2 : ((2 : ℕ) : ZMod (pp n)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply h2
    rw [Nat.cast_ofNat, hs, mul_zero]
  refine ⟨(1 + i) / s, ?_⟩
  rw [div_pow, div_eq_iff (pow_ne_zero 4 hs0)]
  linear_combination (-(i ^ 2 + 4 * i + 5)) * hi - (s ^ 2 + 2) * hs

/-- `3` is a fourth power mod `p` iff `2n+1` is a square mod `p`. -/
lemma H1_fourth_iff_sq (n : ℕ) [hF : Fact (pp n).Prime] (h8 : 8 ∣ n) :
    (∃ z : ZMod (pp n), z ^ 4 = 3) ↔ IsSquare ((2 * n + 1 : ℕ) : ZMod (pp n)) := by
  obtain ⟨ζ, hζ⟩ := H1_zeta n h8
  have hw := H1_w_sq n
  set w : ZMod (pp n) := ((2 * n + 1 : ℕ) : ZMod (pp n)) with hwdef
  constructor
  · rintro ⟨z, hz⟩
    have hprod : ((ζ * z) ^ 2 - w) * ((ζ * z) ^ 2 + w) = 0 := by
      linear_combination z ^ 4 * hζ - hz - hw
    rcases mul_eq_zero.1 hprod with h | h
    · exact ⟨ζ * z, by linear_combination -h⟩
    · exact ⟨ζ ^ 2 * (ζ * z), by linear_combination h - (ζ * z) ^ 2 * hζ⟩
  · rintro ⟨r, hr⟩
    exact ⟨ζ * r, by linear_combination r ^ 4 * hζ - hw + (w + r * r) * hr⟩

theorem lem_2_2_fourth_power_proved (n : ℕ) (h8 : 8 ∣ n) (hp : (pp n).Prime) :
    (∃ z : ZMod (pp n), z ^ 4 = 3) ↔ 3 ∣ n := by
  have : Fact (pp n).Prime := ⟨hp⟩
  rw [H1_fourth_iff_sq n h8, H1_sq_iff n h8]

/-! ## Lemma 2.2, consequence: `σ = gcd(c, n) ≡ 2 (mod 4)` -/

/-- `3` is a square mod `p` (as `-3 = (2n+1)^2` and `-1 = (ζ^2)^2`). -/
lemma H1_three_sq (n : ℕ) [hF : Fact (pp n).Prime] (h8 : 8 ∣ n) :
    ∃ s : ZMod (pp n), s ^ 2 = 3 := by
  obtain ⟨ζ, hζ⟩ := H1_zeta n h8
  have hw := H1_w_sq n
  exact ⟨ζ ^ 2 * ((2 * n + 1 : ℕ) : ZMod (pp n)), by
    linear_combination (((2 * n + 1 : ℕ) : ZMod (pp n))) ^ 2 * hζ - hw⟩

theorem lem_2_2_sigma_proved (n : ℕ) (hn : n % 24 = 8) (hp : (pp n).Prime) {M : Type*} [Field M]
    (χ : MulChar (ZMod (pp n)) M) (g : (ZMod (pp n))ˣ) (hg : ∀ x : (ZMod (pp n))ˣ, x ∈ Subgroup.zpowers g)
    (hχg : IsPrimitiveRoot (χ (g : ZMod (pp n))) n) (ϖ : M) (hϖ : IsPrimitiveRoot ϖ n) (σ : ℕ) (hσ : σ ∣ n)
    (hσ0 : 0 < σ) (h3 : χ 3 = ϖ ^ σ) :
    σ % 4 = 2 ∧ ∀ e : ℕ, n = 2 ^ e → σ = 2 := by
  have hF : Fact (pp n).Prime := ⟨hp⟩
  have h8 : 8 ∣ n := by omega
  have hn0 : n ≠ 0 := by omega
  have hppn := H1_pp_ge n
  -- `3 ≠ 0` in `ZMod p`
  have h30 : (3 : ZMod (pp n)) ≠ 0 := by
    have : ((3 : ℕ) : ZMod (pp n)) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    simpa using this
  -- `3 = g^c`
  obtain ⟨c, hc⟩ : ∃ c : ℕ, ((g ^ c : (ZMod (pp n))ˣ) : ZMod (pp n)) = 3 := by
    obtain ⟨c, hc⟩ := (Submonoid.mem_powers_iff _ _).1
      (mem_powers_iff_mem_zpowers.2 (hg (Units.mk0 3 h30)))
    exact ⟨c, by rw [hc]; rfl⟩
  -- the order of `g` is `p - 1`, which is even
  have hord : orderOf g = pp n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have h2ord : 2 ∣ pp n - 1 := by
    have : pp n - 1 = n * (n + 1) := by unfold pp; rw [Nat.add_sub_cancel]; ring
    rw [this]
    exact Dvd.dvd.mul_right (by omega) _
  -- `c` is even: `3` is a square
  have hc2 : 2 ∣ c := by
    obtain ⟨s, hs⟩ := H1_three_sq n h8
    have hs0 : s ≠ 0 := by
      rintro rfl
      apply h30
      rw [← hs]; ring
    obtain ⟨d, hd⟩ := (Submonoid.mem_powers_iff _ _).1
      (mem_powers_iff_mem_zpowers.2 (hg (Units.mk0 s hs0)))
    have heq : g ^ c = g ^ (d * 2) := by
      apply Units.ext
      rw [hc, pow_mul, hd, Units.val_pow_eq_pow_val, Units.val_mk0, hs]
    rw [pow_eq_pow_iff_modEq, hord] at heq
    have := Nat.ModEq.of_dvd h2ord heq
    unfold Nat.ModEq at this
    omega
  -- `c` is not divisible by `4`: `3` is not a fourth power (first part, `3 ∤ n`)
  have hc4 : ¬ 4 ∣ c := by
    rintro ⟨j, rfl⟩
    have hz : ∃ z : ZMod (pp n), z ^ 4 = 3 :=
      ⟨((g ^ j : (ZMod (pp n))ˣ) : ZMod (pp n)), by
        rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm j 4]; exact hc⟩
    have := (lem_2_2_fourth_power_proved n h8 hp).1 hz
    omega
  have hc0 : c ≠ 0 := by omega
  -- `σ = gcd(n, c)` by comparing orders of `ϖ^σ = χ(g)^c`
  have hχ3 : χ 3 = (χ (g : ZMod (pp n))) ^ c := by
    rw [← hc, Units.val_pow_eq_pow_val, map_pow]
  have hord1 : orderOf (ϖ ^ σ) = n / σ := (hϖ.pow_of_dvd hσ0.ne' hσ).eq_orderOf.symm
  have hord2 : orderOf ((χ (g : ZMod (pp n))) ^ c) = n / Nat.gcd n c := by
    rw [orderOf_pow' _ hc0, ← hχg.eq_orderOf]
  rw [← h3, hχ3, hord2] at hord1
  have hσg : σ = Nat.gcd n c :=
    ((Nat.div_eq_iff_eq_of_dvd_dvd hn0 hσ (Nat.gcd_dvd_left n c)).1 hord1.symm)
  have hσ4 : σ % 4 = 2 := by
    have h2g : 2 ∣ Nat.gcd n c := Nat.dvd_gcd (by omega) hc2
    have h4g : ¬ 4 ∣ Nat.gcd n c := fun h => hc4 (dvd_trans h (Nat.gcd_dvd_right n c))
    rw [hσg]
    omega
  refine ⟨hσ4, fun e he => ?_⟩
  rw [he] at hσ
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hσ
  rw [hk] at hσ4 ⊢
  rcases k with _ | _ | k
  · norm_num at hσ4
  · rfl
  · have : 2 ^ (k + 2) = 2 ^ k * 4 := by ring
    rw [this] at hσ4
    omega

/-- Row 2c. -/
theorem pow2_range_proved (e : ℕ) (he : 3 ≤ e) : 2 ^ e % 24 = 8 ↔ Odd e := by
  rw [Nat.odd_iff]
  rcases Nat.even_or_odd' e with ⟨j, hj | hj⟩
  · have h := (H1_pow2_mod24 (j - 2)).2
    have : 4 + 2 * (j - 2) = e := by omega
    rw [this] at h
    constructor <;> intro <;> omega
  · have h := (H1_pow2_mod24 (j - 1)).1
    have : 3 + 2 * (j - 1) = e := by omega
    rw [this] at h
    constructor <;> intro <;> omega

theorem lem_2_2_pow2_proved (e : ℕ) (h8 : 8 ∣ 2 ^ e) (hp : (pp (2 ^ e)).Prime) :
    Odd e ∧ 2 ^ e % 24 = 8 := by
  have he : 3 ≤ e := by
    have : 2 ^ 3 ∣ 2 ^ e := by simpa using h8
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
  have hodd : Odd e := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨j, rfl⟩ := hev
    have h1 : 2 ^ (j + j) % 3 = 1 := by
      rw [← two_mul, pow_mul, Nat.pow_mod]; norm_num
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ (j + j) = 3 * k + 1 := ⟨2 ^ (j + j) / 3, by omega⟩
    have h3 : 3 ∣ pp (2 ^ (j + j)) := by
      rw [hk]; exact ⟨3 * k ^ 2 + 3 * k + 1, by unfold pp; ring⟩
    have hge := H1_pp_ge (2 ^ (j + j))
    have hpos : 8 ≤ 2 ^ (j + j) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (j + j) := Nat.pow_le_pow_right (by norm_num) he
    rcases Nat.Prime.eq_one_or_self_of_dvd hp 3 h3 with h | h <;> omega
  exact ⟨hodd, (pow2_range_proved e he).2 hodd⟩

/-! ## Introduction: summing (L2) -/

theorem intro_sum_L2_proved (n : ℕ) : (-(n : ZMod 3) = 1) ↔ n % 3 = 2 := by
  have h : (n : ZMod 3) = ((n % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod n 3).symm
  rw [h]
  obtain ⟨r, hr, hn⟩ : ∃ r, r < 3 ∧ n % 3 = r := ⟨n % 3, Nat.mod_lt _ (by norm_num), rfl⟩
  rw [hn]
  interval_cases r <;> decide

/-! ## Theorem 6.4, Step 1 -/

theorem thm_6_4_step1_proved (a r : ℕ) (ha : 3 ≤ a) (hr : Odd r) :
    (∃ k : ℕ, (r : ZMod (2 ^ a)) ^ k = -1) → (r : ZMod (2 ^ a)) = -1 := by
  rintro ⟨k, hk⟩
  have : NeZero (2 ^ a) := ⟨by positivity⟩
  -- `k` is odd: no square is `-1` modulo `4`
  have hkodd : Odd k := by
    by_contra hke
    rw [Nat.not_odd_iff_even] at hke
    obtain ⟨j, rfl⟩ := hke
    have h4 : 4 ∣ 2 ^ a := by
      have : 2 ^ 2 ∣ 2 ^ a := Nat.pow_dvd_pow 2 (by omega)
      simpa using this
    have hk4 := congrArg (ZMod.castHom h4 (ZMod 4)) hk
    rw [map_pow, map_neg, map_one, map_natCast, pow_add] at hk4
    have key : ∀ y : ZMod 4, y * y ≠ -1 := by decide
    exact key _ hk4
  -- `x := -r` has `x^k = 1`, `k` odd, and `x^(2^(a-1)) = 1` (Euler), so `x = 1`
  have hcop : Nat.Coprime r (2 ^ a) := Nat.Coprime.pow_right a (Nat.coprime_two_right.2 hr)
  have hx1 : (-(r : ZMod (2 ^ a))) ^ k = 1 := by
    rw [Odd.neg_pow hkodd, hk, neg_neg]
  have hx2 : (-(r : ZMod (2 ^ a))) ^ (2 ^ (a - 1)) = 1 := by
    have he := ZMod.pow_totient (-(ZMod.unitOfCoprime r hcop))
    rw [Nat.totient_prime_pow Nat.prime_two (by omega)] at he
    have he' := congrArg (fun u : (ZMod (2 ^ a))ˣ => (u : ZMod (2 ^ a))) he
    simp only [Units.val_pow_eq_pow_val, Units.val_neg, ZMod.coe_unitOfCoprime, Units.val_one] at he'
    simpa using he'
  have hgcd : Nat.gcd k (2 ^ (a - 1)) = 1 :=
    Nat.Coprime.pow_right (a - 1) (Nat.coprime_two_right.2 hkodd)
  have hx : (-(r : ZMod (2 ^ a))) ^ Nat.gcd k (2 ^ (a - 1)) = 1 := pow_gcd_eq_one.2 ⟨hx1, hx2⟩
  rw [hgcd, pow_one] at hx
  exact neg_eq_iff_eq_neg.1 hx

/-! ## Section 6.1 arithmetic -/

theorem sec_6_1_arith_proved (n e : ℕ) (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) :
    (n % 5 = 2 ∨ n % 5 = 3) ∧ (n ^ 2 : ZMod 5) = -1 ∧ (n ^ 4 : ZMod 5) = 1 ∧ pp n % 5 = n % 5 ∧
      ¬ 5 ∣ pp n * n ∧ legendreSym 5 (pp n : ℤ) = -1 ∧ 1 + (n - 1) * pp n = n ^ 3 := by
  obtain ⟨j, rfl⟩ := heo
  have hn' : n = 4 ^ j * 2 := by
    rw [hne, pow_succ, pow_mul]; norm_num
  have hmod : n % 5 = 2 ∨ n % 5 = 3 := by
    rcases H1_four_pow_mod5 j with h | h <;> omega
  have hcast : (n : ZMod 5) = ((n % 5 : ℕ) : ZMod 5) := (ZMod.natCast_mod n 5).symm
  have h2 : (n : ZMod 5) ^ 2 = -1 := by
    rw [hcast]; rcases hmod with h | h <;> rw [h] <;> decide
  have h4 : (n : ZMod 5) ^ 4 = 1 := by
    have : (n : ZMod 5) ^ 4 = ((n : ZMod 5) ^ 2) ^ 2 := by ring
    rw [this, h2]; norm_num
  have hpp5 : ((pp n : ℕ) : ZMod 5) = (n : ZMod 5) := by
    unfold pp; push_cast; rw [h2]; ring
  have hppmod : pp n % 5 = n % 5 := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hpp5
  have hn1 : 1 ≤ n := by rw [hne]; exact Nat.one_le_two_pow
  refine ⟨hmod, by exact_mod_cast h2, by exact_mod_cast h4, hppmod, ?_, ?_, ?_⟩
  · intro hd
    have h0 := Nat.mod_eq_zero_of_dvd hd
    rw [Nat.mul_mod, hppmod] at h0
    rcases hmod with h | h <;> rw [h] at h0 <;> norm_num at h0
  · rw [legendreSym.mod, ← Int.natCast_mod, hppmod]
    rcases hmod with h | h <;> rw [h] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    unfold pp; ring

#print axioms lem_2_2_fourth_power_proved
#print axioms lem_2_2_sigma_proved
#print axioms lem_2_2_pow2_proved
#print axioms pow2_range_proved
#print axioms intro_sum_L2_proved
#print axioms thm_6_4_step1_proved
#print axioms sec_6_1_arith_proved

end Xia.Proofs
