/- Xia/Proofs/PrimRoot.lean — lemmas used by the proofs.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry

namespace Xia.Proofs

/-- If `3 ∤ n`, an algebraically closed field of characteristic 3 contains a primitive `n`-th root of unity. -/
theorem L10_exists_prim_algclosed (n : ℕ) [NeZero n] (h3 : ¬ 3 ∣ n) {L : Type*} [Field L] [CharP L 3] [IsAlgClosed L] :
    ∃ ω : L, IsPrimitiveRoot ω n := by
  have : NeZero ((n : ℕ) : L) := ⟨by rw [Ne, CharP.cast_eq_zero_iff L 3]; exact h3⟩
  exact HasEnoughRootsOfUnity.exists_isPrimitiveRoot L n

end Xia.Proofs

#print axioms Xia.Proofs.L10_exists_prim_algclosed
