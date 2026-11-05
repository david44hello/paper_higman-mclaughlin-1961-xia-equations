/- Xia/Proofs/Prop61.lean — proofs of the rows prop_6_1 of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import Xia.Defs.Symmetry
import Xia.Defs.DiffSet
import Xia.Proofs.NumberTheory

namespace Xia.Proofs

open Xia Finset

/-! ## Generator lemmas for `(ZMod p)ˣ` and a multiplicative character -/

/-- Every nonzero `a ∈ ZMod p` is a NATURAL power of a generator `g` of `(ZMod p)ˣ`. -/
lemma H17_exists_pow (p : ℕ) [Fact p.Prime] (g : (ZMod p)ˣ)
    (hg : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (a : ZMod p) (ha : a ≠ 0) :
    ∃ k : ℕ, ((g ^ k : (ZMod p)ˣ) : ZMod p) = a := by
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1
    (mem_powers_iff_mem_zpowers.2 (hg (Units.mk0 a ha)))
  exact ⟨k, by rw [hk]; rfl⟩

/-- `χ(g^k) = χ(g)^k`. -/
lemma H17_chi_pow {p : ℕ} {M : Type*} [Field M] (χ : MulChar (ZMod p) M) (g : (ZMod p)ˣ) (k : ℕ) :
    χ ((g ^ k : (ZMod p)ˣ) : ZMod p) = χ (g : ZMod p) ^ k := by
  rw [Units.val_pow_eq_pow_val, map_pow]

/-- A character with `χ(g)^n = 1` on a generator is trivial on `H_{p,n}` (the nonzero `n`-th powers). -/
lemma H17_chi_Hpow (p n : ℕ) [Fact p.Prime] {M : Type*} [Field M] (χ : MulChar (ZMod p) M) (g : (ZMod p)ˣ)
    (hg : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hχg : IsPrimitiveRoot (χ (g : ZMod p)) n)
    (a : ZMod p) (ha : a ∈ Hpow p n) : χ a = 1 := by
  obtain ⟨b, hb0, rfl⟩ : ∃ b : ZMod p, b ≠ 0 ∧ a = b ^ n := ha
  obtain ⟨k, hk⟩ := H17_exists_pow p g hg b hb0
  rw [map_pow, ← hk, H17_chi_pow, ← pow_mul, mul_comm, pow_mul, hχg.pow_eq_one, one_pow]

/-- `n = 2^e`, `e ≥ 3` gives `8 ∣ n`. -/
lemma H17_eight_dvd (n e : ℕ) (hne : n = 2 ^ e) (he : 3 ≤ e) : 8 ∣ n := by
  rw [hne]
  exact pow_dvd_pow 2 he

/-- `5 ≠ 0` in `ZMod (pp n)` once `n ≥ 8` (as `pp n ≥ n + 1 > 5`). -/
lemma H17_five_ne_zero (n : ℕ) (h8 : 8 < n) : (5 : ZMod (pp n)) ≠ 0 := by
  have : ((5 : ℕ) : ZMod (pp n)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd (by norm_num) hd
    have := H1_pp_ge n
    omega
  simpa using this

/-! ## Row 20 — Proposition 6.1 (the deduction) -/

theorem prop_6_1_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) (Plane : Prop)
    (hX12 : Plane → (pp n).Prime ∧ 8 < n ∧ Even n ∧ IsDiffSet (pp n) (Hpow (pp n) n) (n + 1) 1)
    (hX41 : (pp n).Prime → IsDiffSet (pp n) (Hpow (pp n) n) (n + 1) 1 → n % 3 = 2 ∧ (2 : ZMod (pp n)) ∈ Hpow (pp n) n)
    {M : Type*} [Field M] (χ : MulChar (ZMod (pp n)) M) (g : (ZMod (pp n))ˣ)
    (hg : ∀ x : (ZMod (pp n))ˣ, x ∈ Subgroup.zpowers g) (hχg : IsPrimitiveRoot (χ (g : ZMod (pp n))) n)
    (hX35 : ∀ (μ : M) (σ : ℕ), IsPrimitiveRoot μ n → χ 5 = μ ^ σ →
      (-1 : ℤ) ^ σ = legendreSym 5 ((-1) ^ (n / 2) * (pp n : ℤ)))
    (hX34b : IsDiffSet (pp n) (Hpow (pp n) n) (n + 1) 1 → ∀ (μ : M) (σ θ : ℕ), IsPrimitiveRoot μ n →
      χ 5 = μ ^ σ → χ 2 = μ ^ θ →
      ∃ y : ZMod n → GaloisField 5 (n / Nat.gcd σ n),
        L1 5 (σ : ℤ) y ∧ L2 (((1 + (n - 1) * pp n : ℕ) : GaloisField 5 (n / Nat.gcd σ n))) y ∧
        L3 ((n : GaloisField 5 (n / Nat.gcd σ n)) * (1 - (pp n : GaloisField 5 (n / Nat.gcd σ n)))) y ∧
        ∀ s : ZMod n, s.val < n / 2 →
          ∑ t, sgn t * y t * y (2 * s - 2 * (θ : ZMod n) - t) = (y s + y (s + half n)) * S y) :
    Plane → (Xia5Set n).Nonempty := by
  intro hPlane
  obtain ⟨hp, h8lt, -, hds⟩ := hX12 hPlane
  obtain ⟨-, h2H⟩ := hX41 hp hds
  have : Fact (pp n).Prime := ⟨hp⟩
  obtain ⟨-, -, -, -, -, hleg, harith⟩ := sec_6_1_arith_proved n e hne he heo
  -- `χ(2) = 1`: `2 ∈ H_{p,n}` (Xia Lemma 4.1) and `χ` kills `n`-th powers
  have hχ2 : χ 2 = 1 := H17_chi_Hpow (pp n) n χ g hg hχg 2 h2H
  -- `5 = g^k`, so `χ(5) = χ(g)^k`
  obtain ⟨k, hk⟩ := H17_exists_pow (pp n) g hg 5 (H17_five_ne_zero n h8lt)
  have hχ5 : χ 5 = χ (g : ZMod (pp n)) ^ k := by rw [← hk, H17_chi_pow]
  -- `k` is odd (Xia Lemma 3.5: `(-1)^k = ((-1)^{n/2} p / 5) = (p/5) = -1`, as `n/2` is even)
  obtain ⟨x, hx⟩ := H17_eight_dvd n e hne he
  have hn2 : Even (n / 2) := ⟨2 * x, by omega⟩
  have hsign := hX35 _ k hχg hχ5
  rw [hn2.neg_one_pow, one_mul, hleg] at hsign
  have hkodd : Odd k := (neg_one_pow_eq_neg_one_iff_odd (by norm_num)).1 hsign
  -- hence `χ(5)` is a primitive `n`-th root (`k` odd, `n = 2^e`)
  have hcop : k.Coprime n := by
    rw [hne]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hkodd)
  have hμ : IsPrimitiveRoot (χ 5) n := by
    rw [hχ5]
    exact hχg.pow_of_coprime k hcop
  -- Xia Theorem 3.4(b) with `μ := χ(5)`, `σ = 1`, `θ = 0`
  have hex := hX34b hds (χ 5) 1 0 hμ (pow_one _).symm (by rw [pow_zero, hχ2])
  rw [Nat.gcd_one_left, Nat.div_one] at hex
  obtain ⟨y, hL1, hL2, hL3, hL4⟩ := hex
  refine ⟨y, ?_⟩
  show RSysEqs 5 1 y
  refine ⟨?_, ?_, hL3, ?_⟩
  · simpa only [Nat.cast_one] using hL1
  · rw [harith, Nat.cast_pow] at hL2
    exact hL2
  · intro s hs
    have h4 := hL4 s hs
    simpa only [Nat.cast_zero, mul_zero, sub_zero] using h4

/-! ## Xia's Lemma 3.5 for row 25 (the hypothesis `hX35r` of `cor_6_5_sign`) -/

/-- A primitive `n`-th root with `n` even has `ζ^{n/2} = -1`. -/
lemma H17_pow_half (n : ℕ) (hn0 : n ≠ 0) (h2 : 2 ∣ n) {M : Type*} [Field M] (ζ : M)
    (hζ : IsPrimitiveRoot ζ n) : ζ ^ (n / 2) = -1 := by
  have h := hζ.pow_of_dvd (show n / 2 ≠ 0 by omega) (Nat.div_dvd_of_dvd h2)
  rw [Nat.div_div_self h2 hn0] at h
  exact h.eq_neg_one_of_two_right

/-- Parities agree: if `(-1)^σ' = (-1)^k` in a field with `-1 ≠ 1`, then `(-1)^{|σ'|} = (-1)^k` in `ℤ`. -/
lemma H17_parity {M : Type*} [Field M] (hM : (-1 : M) ≠ 1) (σ' : ℤ) (k : ℕ)
    (h : (-1 : M) ^ σ' = (-1 : M) ^ k) : (-1 : ℤ) ^ σ'.natAbs = (-1 : ℤ) ^ k := by
  rcases Int.even_or_odd σ' with hs | hs <;> rcases Nat.even_or_odd k with hk | hk
  · rw [(Int.natAbs_even.2 hs).neg_one_pow, hk.neg_one_pow]
  · rw [hs.neg_one_zpow, hk.neg_one_pow] at h
    exact absurd h.symm hM
  · rw [hs.neg_one_zpow, hk.neg_one_pow] at h
    exact absurd h hM
  · rw [(Int.natAbs_odd.2 hs).neg_one_pow, hk.neg_one_pow]

/-- A generator `g` of `(ZMod p)ˣ` (`p` an odd prime) is a non-square, so `(g^k / p) = (-1)^k`. -/
lemma H17_legendre_gen (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (g : (ZMod p)ˣ)
    (hg : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (k : ℕ) :
    quadraticChar (ZMod p) ((g ^ k : (ZMod p)ˣ) : ZMod p) = (-1) ^ k := by
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
  rw [Units.val_pow_eq_pow_val, map_pow, quadraticChar_neg_one_iff_not_isSquare.2 hns]

/-- Xia's Lemma 3.5 (v7 pp. 11-12) for `r`, in the situation of row 25 (`n = 2^a · nodd`, `a ≥ 3`): for every
primitive `μ'` with `χ(r) = μ'^{σ'}`, `(-1)^{σ'} = ((-1)^{n/2} p / r)`. Route: `χ(r)^{n/2} = (-1)^{σ'}` and
`χ(r)^{n/2} = (-1)^k = (r/p)` (`r = g^k`, `g` a non-square); `(r/p) = (p/r)` by quadratic reciprocity (`p ≡ 1 mod 4`);
`(-1)^{n/2} = 1`. -/
theorem xia_lemma_3_5 (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a)
    (_hodd : Odd nodd) (hp : (pp n).Prime) (hr : ¬ r ∣ pp n * n) {M : Type*} [Field M] (χ : MulChar (ZMod (pp n)) M) (g : (ZMod (pp n))ˣ)
    (hg : ∀ x : (ZMod (pp n))ˣ, x ∈ Subgroup.zpowers g) (hχg : IsPrimitiveRoot (χ (g : ZMod (pp n))) n)
    (μ : M) (_hμ : IsPrimitiveRoot μ n) (σr : ℤ) (hχr : χ (r : ZMod (pp n)) = μ ^ σr) :
    ∀ (μ' : M) (σ' : ℤ), IsPrimitiveRoot μ' n → χ (r : ZMod (pp n)) = μ' ^ σ' →
      (-1 : ℤ) ^ σ'.natAbs = legendreSym r ((-1) ^ (n / 2) * (pp n : ℤ)) := by
  intro μ' σ' hμ' hχ'
  have : Fact (pp n).Prime := ⟨hp⟩
  have hn0 : n ≠ 0 := NeZero.ne n
  -- arithmetic: `8 ∣ n`, `n/2` even, `p ≡ 1 (mod 4)`, `r ≠ 2`, `p ∤ r`
  obtain ⟨x, hx⟩ : 8 ∣ n := by
    rw [hn]
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 ha) _
  have h2 : 2 ∣ n := ⟨4 * x, by omega⟩
  have hn2 : Even (n / 2) := ⟨2 * x, by omega⟩
  have hp4 : pp n % 4 = 1 := by
    have : pp n = 4 * (16 * x ^ 2 + 2 * x) + 1 := by unfold pp; rw [hx]; ring
    omega
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact hr (Dvd.dvd.mul_left h2 _)
  have hp2 : pp n ≠ 2 := by omega
  have hr0 : (r : ZMod (pp n)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq hp (Fact.out : r.Prime)).1 hd
    exact hr (this ▸ Dvd.dvd.mul_right (dvd_refl _) _)
  -- `r = g^k`
  obtain ⟨k, hk⟩ := H17_exists_pow (pp n) g hg (r : ZMod (pp n)) hr0
  -- in `M`: `χ(r)^{n/2} = (-1)^{σ'}` and `= (-1)^k`
  have hM : (-1 : M) ≠ 1 := by
    intro h
    have := H17_pow_half n hn0 h2 _ hχg
    rw [h] at this
    exact hχg.pow_ne_one_of_pos_of_lt (by omega) (by omega) this
  have hσ : χ (r : ZMod (pp n)) ^ (n / 2) = (-1 : M) ^ σ' := by
    rw [hχ', ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, H17_pow_half n hn0 h2 μ' hμ']
  have hkM : χ (r : ZMod (pp n)) ^ (n / 2) = (-1 : M) ^ k := by
    rw [← hk, H17_chi_pow, ← pow_mul, mul_comm, pow_mul, H17_pow_half n hn0 h2 _ hχg]
  have hpar := H17_parity hM σ' k (hσ.symm.trans hkM)
  -- in `ℤ`: `(r/p) = (-1)^k`
  have hleg : legendreSym (pp n) (r : ℤ) = (-1) ^ k := by
    unfold legendreSym
    rw [Int.cast_natCast, ← hk, H17_legendre_gen (pp n) hp2 g hg k]
  rw [hn2.neg_one_pow, one_mul, legendreSym.quadratic_reciprocity_one_mod_four hp4 hr2, hleg, hpar]

end Xia.Proofs

#print axioms Xia.Proofs.prop_6_1_proved
#print axioms Xia.Proofs.xia_lemma_3_5
