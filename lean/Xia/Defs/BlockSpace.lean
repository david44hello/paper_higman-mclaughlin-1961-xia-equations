/- Xia/Defs/BlockSpace.lean — definitions (nuData, topOf, Vfib, Tsh, VfibPlus, VfibMinus, Ycoef, VfibBlock, ...).
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry

namespace Xia

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

/-- The `ν`-data of a function on `ℤ/n`: `k ↦ h(k) h(k+m)` (`= ŷ(ρ)ŷ(-ρ)` at `ρ = ω^k`; s5_twonorms.tex:26-31). -/
def nuData (h : ZMod n → L) (k : ZMod n) : L := h k * h (k + half n)

/-- The top data of a sequence: its transform on the top layer (odd `k`), `0` on the lower layers. -/
noncomputable def topOf {F : Type*} [CommRing F] [Algebra F L] (ω : L) (y : ZMod n → F) : ZMod n → L :=
  fun k => if Odd k.val then dftA ω y k else 0

/-- `V` of the fibre with `ν`-data `ν` (s5_twonorms.tex:33 and :170-174): the formal top functions. -/
def Vfib (ω : L) (ν : ZMod n → L) : Set (ZMod n → L) :=
  {h | (∀ k : ZMod n, Even k.val → h k = 0) ∧
    (∀ k : ZMod n, Odd k.val → h (3 * k) = (ω ^ k.val) ^ 6 * h k ^ 3) ∧
    ∀ k : ZMod n, Odd k.val → h (-k) * ν k = -h (k + half n)}

/-- `T`: the substitution `y ↦ y^{(u)}` on formal top functions, `top_{Tv}(ξ) = top_v(-ξ)` ((P2), s5_twonorms.tex:187). -/
def Tsh (h : ZMod n → L) : ZMod n → L := fun k => h (k + half n)

/-- The `+1` and `-1` eigenspaces `V_±` of `T` on `Vfib` (Thm 5.1(d)). -/
def VfibPlus (ω : L) (ν : ZMod n → L) : Set (ZMod n → L) := {h | h ∈ Vfib ω ν ∧ Tsh h = h}

def VfibMinus (ω : L) (ν : ZMod n → L) : Set (ZMod n → L) := {h | h ∈ Vfib ω ν ∧ Tsh h = -h}

/-- `𝒴_s(v) := y^-_s(v) = n^{-1} ∑_{ξ ∈ 𝓛_a} top_v(ξ) ξ^{-s}` (s5_twonorms.tex:181-183); `𝒴_0`, `𝒴_1` are `s = 0, 1`.
(`h` vanishes off the top layer on `Vfib`, so the sum over all `k` is the sum over `𝓛_a`.) -/
def Ycoef (ω : L) (s : ℕ) (h : ZMod n → L) : L := (n : L)⁻¹ * ∑ k : ZMod n, h k * ((ω ^ k.val)⁻¹) ^ s

/-- The block subspace of `Vfib` for a block `B` (functions supported on the orbits of `B`). -/
def VfibBlock (ω : L) (ν : ZMod n → L) (B : Finset (Finset (ZMod n))) : Set (ZMod n → L) :=
  {h | h ∈ Vfib ω ν ∧ ∀ k : ZMod n, k ∉ B.biUnion id → h k = 0}

/-- Restriction of `h` to the orbits of a block (zero elsewhere). -/
noncomputable def restrictBlock (B : Finset (Finset (ZMod n))) (h : ZMod n → L) : ZMod n → L :=
  fun k => if k ∈ B.biUnion id then h k else 0

end Xia
