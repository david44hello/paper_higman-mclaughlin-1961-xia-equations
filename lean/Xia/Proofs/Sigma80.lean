/- Xia/Proofs/Sigma80.lean — proofs of the rows table4_sigma80 of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import Xia.Defs.Symmetry
import Xia.Proofs.NumberTheory

namespace Xia.Proofs

open Xia Finset

/-- `p = pp 80 = 6481` is prime. -/
lemma H34_pp80_prime : (pp 80).Prime := by
  norm_num [pp]

/-- `3^24 = 1` in `ZMod (pp 80)` (as `3^8 ≡ 80` and `80^3 ≡ 1 (mod 80^2+80+1)`). -/
lemma H34_three_pow24 : (3 : ZMod (pp 80)) ^ 24 = 1 := by
  have h : ((3 : ℕ) : ZMod (pp 80)) ^ 24 = ((1 : ℕ) : ZMod (pp 80)) := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_natCast_iff']
    norm_num [pp]
  simpa using h

/-- Arithmetic endgame: the only divisor `σ` of `80` with `80 ∣ 24σ` and `σ ≡ 2 (mod 4)` is `10`. -/
lemma H34_arith (σ : ℕ) (hσ : σ ∣ 80) (h80 : 80 ∣ σ * 24) (h4 : σ % 4 = 2) : σ = 10 := by
  have hle : σ ≤ 80 := Nat.le_of_dvd (by norm_num) hσ
  interval_cases σ <;> omega

theorem table4_sigma80_proved {M : Type*} [Field M] (χ : MulChar (ZMod (pp 80)) M) (g : (ZMod (pp 80))ˣ)
    (hg : ∀ x : (ZMod (pp 80))ˣ, x ∈ Subgroup.zpowers g) (hχg : IsPrimitiveRoot (χ (g : ZMod (pp 80))) 80)
    (ϖ : M) (hϖ : IsPrimitiveRoot ϖ 80) (σ : ℕ) (hσ : σ ∣ 80) (hσ0 : 0 < σ) (h3 : χ 3 = ϖ ^ σ) : σ = 10 := by
  -- `σ ≡ 2 (mod 4)` from Lemma 2.2 (n = 80 ≡ 8 mod 24)
  have h4 : σ % 4 = 2 :=
    (lem_2_2_sigma_proved 80 (by norm_num) H34_pp80_prime χ g hg hχg ϖ hϖ σ hσ hσ0 h3).1
  -- `ϖ^(σ·24) = χ(3)^24 = χ(3^24) = χ(1) = 1`
  have hpow : ϖ ^ (σ * 24) = 1 := by
    rw [pow_mul, ← h3, ← map_pow, H34_three_pow24, map_one]
  exact H34_arith σ hσ (hϖ.dvd_of_pow_eq_one _ hpow) h4

end Xia.Proofs

#print axioms Xia.Proofs.table4_sigma80_proved
