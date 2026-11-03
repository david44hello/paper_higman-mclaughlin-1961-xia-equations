/- Xia/Proofs/Prop61Final.lean — proofs of the rows prop_6_1_from_diffset of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Proofs.Prop61Uncond
import Xia.Proofs.Lemma41
import Xia.Proofs.Thm34b
import Xia.Proofs.CharExists

namespace Xia.Proofs

open Xia Finset

/-- `5 ≠ 0` in `ZMod (pp n)` for `n ≥ 2` (`pp n ≥ 7`). -/
lemma L10_five_ne_zero (n : ℕ) (hn : 2 ≤ n) : (5 : ZMod (pp n)) ≠ 0 := by
  have : ((5 : ℕ) : ZMod (pp n)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have h5 := Nat.le_of_dvd (by norm_num) hd
    have hpp : pp n = n ^ 2 + n + 1 := rfl
    nlinarith
  exact_mod_cast this

/-- Proposition 6.1 from the planar difference set onwards (s6_primes.tex:17-41 after Xia's Prop 1.2): for `n = 2^e`
(`e ≥ 3` odd), if `p = n^2+n+1` is prime and `H_{p,n}` is a `(p, n+1, 1)`-difference set, Xia's system (eq:xia125) has a
solution over `F_{5^n}`. No Xia hypothesis: Lemma 3.5 (`L10_hX35_of_lemma`), Lemma 4.1 (`L10_hX41_proved`) and Theorem
3.4(b) (`L10_hX34b_proved`) are proved in Lean. The steps are those of `prop_6_1_proved`. -/
theorem prop_6_1_from_diffset_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e)
    (hp : (pp n).Prime) (hD : IsDiffSet (pp n) (Hpow (pp n) n) (n + 1) 1) : (Xia5Set n).Nonempty := by
  obtain ⟨χ, g, hg, hχg⟩ := L10_char_data_exists n hp
  have : Fact (pp n).Prime := ⟨hp⟩
  obtain ⟨-, h2H⟩ := L10_hX41_proved n e hne he heo hp hD
  obtain ⟨-, -, -, -, -, hleg, harith⟩ := sec_6_1_arith_proved n e hne he heo
  -- `χ(2) = 1`: `2 ∈ H_{p,n}` (Xia Lemma 4.1) and `χ` kills `n`-th powers
  have hχ2 : χ 2 = 1 := H17_chi_Hpow (pp n) n χ g hg hχg 2 h2H
  -- `5 = g^k`, so `χ(5) = χ(g)^k`
  have hn2le : 2 ≤ n := by
    have := H17_eight_dvd n e hne he
    have : n ≠ 0 := NeZero.ne n
    omega
  obtain ⟨k, hk⟩ := H17_exists_pow (pp n) g hg 5 (L10_five_ne_zero n hn2le)
  have hχ5 : χ 5 = χ (g : ZMod (pp n)) ^ k := by rw [← hk, H17_chi_pow]
  -- `k` is odd (Xia Lemma 3.5: `(-1)^k = ((-1)^{n/2} p / 5) = (p/5) = -1`, as `n/2` is even)
  obtain ⟨x, hx⟩ := H17_eight_dvd n e hne he
  have hn2 : Even (n / 2) := ⟨2 * x, by omega⟩
  have hsign := L10_hX35_of_lemma n e hne he heo hp χ g hg hχg _ k hχg hχ5
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
  have hex := L10_hX34b_proved n e hne he heo hp χ g hg hχg hD (χ 5) 1 0 hμ (pow_one _).symm
    (by rw [pow_zero, hχ2])
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

end Xia.Proofs

#print axioms Xia.Proofs.L10_five_ne_zero
#print axioms Xia.Proofs.prop_6_1_from_diffset_proved
