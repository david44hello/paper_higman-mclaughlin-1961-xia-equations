/- Xia/Proofs/R3.lean — proofs of the rows thm_6_4_r3 of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry

namespace Xia.Proofs

open Xia Finset

/-- `3 ∤ pp n * n` forces `n = 3k + 2`. -/
theorem H41_mod3 (n : ℕ) (hr : ¬ 3 ∣ pp n * n) : n = 3 * (n / 3) + 2 := by
  obtain ⟨k, hk | hk | hk⟩ : ∃ k, n = 3 * k ∨ n = 3 * k + 1 ∨ n = 3 * k + 2 := ⟨n / 3, by omega⟩
  · exact absurd (Dvd.dvd.mul_left ⟨k, hk⟩ (pp n)) hr
  · have h3 : 3 ∣ pp n := ⟨3 * k ^ 2 + 3 * k + 1, by unfold pp; rw [hk]; ring⟩
    exact absurd (Dvd.dvd.mul_right h3 n) hr
  · omega

/-- In characteristic 3, `n = 3k + 2` casts to `2`. -/
theorem H41_cast_two {K : Type*} [CommRing K] [CharP K 3] (n : ℕ) (hr : ¬ 3 ∣ pp n * n) :
    (n : K) = 2 := by
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  rw [H41_mod3 n hr]
  push_cast
  linear_combination ((n / 3 : ℕ) : K) * h3

/-- In characteristic 3, the (L3_r) constant `n(1-p)` is `0`. -/
theorem H41_L3const {K : Type*} [CommRing K] [CharP K 3] (n : ℕ) (hr : ¬ 3 ∣ pp n * n) :
    (n : K) * (1 - (pp n : K)) = 0 := by
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  unfold pp
  push_cast
  rw [H41_cast_two n hr]
  linear_combination (-4 : K) * h3

/-- In characteristic 3, the `R(m)` value `n^4` is `1`. -/
theorem H41_Rconst {K : Type*} [CommRing K] [CharP K 3] (n : ℕ) (hr : ¬ 3 ∣ pp n * n) :
    (n : K) ^ 4 = 1 := by
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  rw [H41_cast_two n hr]
  linear_combination (5 : K) * h3

/-- In characteristic 3 with `3 ∤ pn`, the norm-free `r = 3` equations are the norm-free equations. -/
theorem H41_eqs_iff {K : Type*} [CommRing K] [CharP K 3] (n : ℕ) [NeZero n] (hr : ¬ 3 ∣ pp n * n)
    (σ : ℤ) (y : ZMod n → K) : NFrEqs 3 σ y ↔ NormFreeEqs σ y := by
  unfold NFrEqs NormFreeEqs
  rw [H41_L3const n hr, H41_Rconst n hr]

/-- Changing the field index along an equality of indices. -/
theorem H41_index_equiv (n : ℕ) [NeZero n] (σ : ℤ) (m m' : ℕ) (h : m = m') :
    Nonempty ({y : ZMod n → GaloisField 3 m // NormFreeEqs σ y} ≃
      {y : ZMod n → GaloisField 3 m' // NormFreeEqs σ y}) := by
  subst h
  exact ⟨Equiv.refl _⟩

/-- `n / gcd(σ, n) = n / σ` for `σ ∣ n`. -/
theorem H41_index (n σ : ℕ) (hσ : σ ∣ n) : n / Int.gcd (σ : ℤ) n = n / σ := by
  rw [Int.gcd_natCast_natCast, Nat.gcd_eq_left hσ]

theorem thm_6_4_r3_proved (n : ℕ) [NeZero n] (hr : ¬ 3 ∣ pp n * n) (σ : ℕ) (hσ : σ ∣ n) :
    n / Int.gcd (σ : ℤ) n = n / σ ∧
    (∀ y : ZMod n → GaloisField 3 (n / Int.gcd (σ : ℤ) n), y ∈ NFrSet n 3 (σ : ℤ) ↔ NormFreeEqs (σ : ℤ) y) ∧
    Nonempty (NFrSet n 3 (σ : ℤ) ≃ NFSet n σ) ∧ Nat.card (NFrSet n 3 (σ : ℤ)) = Nat.card (NFSet n σ) := by
  have h1 : n / Int.gcd (σ : ℤ) n = n / σ := H41_index n σ hσ
  have h2 : ∀ y : ZMod n → GaloisField 3 (n / Int.gcd (σ : ℤ) n),
      y ∈ NFrSet n 3 (σ : ℤ) ↔ NormFreeEqs (σ : ℤ) y := fun y => H41_eqs_iff n hr (σ : ℤ) y
  obtain ⟨e⟩ := H41_index_equiv n (σ : ℤ) _ _ h1
  have h3 : Nonempty (NFrSet n 3 (σ : ℤ) ≃ NFSet n σ) :=
    ⟨(Equiv.subtypeEquivRight h2).trans (e.trans (Equiv.subtypeEquivRight (fun _ => Iff.rfl)))⟩
  obtain ⟨e3⟩ := h3
  exact ⟨h1, h2, ⟨e3⟩, Nat.card_congr e3⟩

end Xia.Proofs

#print axioms Xia.Proofs.thm_6_4_r3_proved
