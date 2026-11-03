/- Xia/Proofs/Prop61Uncond.lean — lemmas used by the proofs.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Proofs.Prop61

namespace Xia.Proofs

open Xia

/-- For `n = 2^e` (`e ≥ 3` odd) and `p = n^2+n+1` prime, the hypothesis `hX35` of row 20 (`prop_6_1`) holds: it is Xia's
Lemma 3.5 for `r = 5`, proved in Lean as `xia_lemma_3_5`. -/
theorem L10_hX35_of_lemma (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e)
    (hp : (pp n).Prime) {M : Type*} [Field M] (χ : MulChar (ZMod (pp n)) M) (g : (ZMod (pp n))ˣ)
    (hg : ∀ x : (ZMod (pp n))ˣ, x ∈ Subgroup.zpowers g) (hχg : IsPrimitiveRoot (χ (g : ZMod (pp n))) n) :
    ∀ (μ : M) (σ : ℕ), IsPrimitiveRoot μ n → χ 5 = μ ^ σ →
      (-1 : ℤ) ^ σ = legendreSym 5 ((-1) ^ (n / 2) * (pp n : ℤ)) := by
  intro μ σ hμ h5
  have hn1 : n = 2 ^ e * 1 := by rw [hne, mul_one]
  have hr : ¬ 5 ∣ pp n * n := (sec_6_1_arith_proved n e hne he heo).2.2.2.2.1
  have h5' : χ ((5 : ℕ) : ZMod (pp n)) = μ ^ (σ : ℤ) := by
    rw [zpow_natCast]
    simpa using h5
  have key := xia_lemma_3_5 n e 1 5 hn1 he odd_one hp hr χ g hg hχg μ hμ (σ : ℤ) h5' μ (σ : ℤ) hμ h5'
  simpa using key

end Xia.Proofs

#print axioms Xia.Proofs.L10_hX35_of_lemma
