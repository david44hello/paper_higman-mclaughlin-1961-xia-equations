/- Xia/Proofs/CharExists.lean — lemmas used by the proofs.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.DiffSet

namespace Xia.Proofs

open Xia Finset

/-- `#(ZMod (pp n))ˣ = n^2 + n` when `pp n` is prime. -/
theorem H32_card_units (n : ℕ) [Fact (pp n).Prime] [Fintype (ZMod (pp n))ˣ] :
    Fintype.card (ZMod (pp n))ˣ = n ^ 2 + n := by
  have : NeZero (pp n) := ⟨(Fact.out : (pp n).Prime).ne_zero⟩
  rw [ZMod.card_units_eq_totient, Nat.totient_prime Fact.out]
  simp [pp]

/-- The unit `exp(2πi/n)` is a `#(ZMod (pp n))ˣ`-th root of unity. -/
theorem H32_mem_rootsOfUnity (n : ℕ) [NeZero n] [Fact (pp n).Prime] [Fintype (ZMod (pp n))ˣ] :
    ((Complex.isPrimitiveRoot_exp n (NeZero.ne n)).isUnit (NeZero.ne n)).unit ∈
      rootsOfUnity (Fintype.card (ZMod (pp n))ˣ) ℂ := by
  have hζ := Complex.isPrimitiveRoot_exp n (NeZero.ne n)
  rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one,
    hζ.pow_eq_one_iff_dvd, H32_card_units]
  exact ⟨n + 1, by ring⟩

theorem L10_char_data_exists (n : ℕ) [NeZero n] (hp : (pp n).Prime) :
    ∃ (χ : MulChar (ZMod (pp n)) ℂ) (g : (ZMod (pp n))ˣ),
      (∀ x : (ZMod (pp n))ˣ, x ∈ Subgroup.zpowers g) ∧ IsPrimitiveRoot (χ (g : ZMod (pp n))) n := by
  classical
  have : Fact (pp n).Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod (pp n))ˣ)
  refine ⟨MulChar.ofRootOfUnity (H32_mem_rootsOfUnity n) hg, g, hg, ?_⟩
  rw [MulChar.ofRootOfUnity_spec, IsUnit.unit_spec]
  exact Complex.isPrimitiveRoot_exp n (NeZero.ne n)

end Xia.Proofs

#print axioms Xia.Proofs.L10_char_data_exists
