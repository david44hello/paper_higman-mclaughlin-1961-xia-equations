/- Xia/Defs/Fig2.lean — definitions (fig2Layer).
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Fourier

namespace Xia

open Finset

/-- Figure 2 (s4_normfree.tex:72), `n = 80`, exponent model `ξ = ω^k` (`ω` a primitive 80th root of unity, so
`μ_80 ≅ ℤ/80`): write `ξ = ζα` with `ζ ∈ μ_16` (`16·z = 0`) and `α ∈ μ_5` (`5·w = 0`); "An element `ξ = ζα` lies in layer
`j` when `ζ` has order `2^j`". -/
noncomputable def fig2Layer (j : ℕ) : Finset (ZMod 80) := by
  classical
  exact univ.filter (fun k => ∃ z w : ZMod 80, k = z + w ∧ (16 : ZMod 80) * z = 0 ∧ (5 : ZMod 80) * w = 0 ∧
    addOrderOf z = 2 ^ j)

end Xia
