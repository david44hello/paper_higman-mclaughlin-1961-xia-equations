/- Xia/Defs/Symmetry.lean — definitions (ySubst, yTrans, fibre, lowerData, kappa).
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Decoupling

namespace Xia

variable {n : ℕ} [NeZero n] {K : Type*}

/-- The substitution `y^{(u)}_t := y_{ut}`, `u := 1 + n/2` (P10s_main.tex:182; s5_twonorms.tex:10). -/
def ySubst (y : ZMod n → K) : ZMod n → K := fun t => y ((1 + half n) * t)

/-- The translation `y_t ↦ y_{t+c}` (Remark 3.3 with `c = 1`; `c = n/2` gives `ȳ` on the norm-free system). -/
def yTrans (c : ZMod n) (y : ZMod n → K) : ZMod n → K := fun t => y (t + c)

/-- A fibre (Theorem B, P10s_main.tex:183-184; s5_twonorms.tex:74): the solutions of the norm-free system whose `ŷ` has
the same values as `ŷ` of `y` on the lower layers `μ_{n/2}` (exponent model: even `k`). -/
noncomputable def fibre {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (y : ZMod n → GaloisField 3 (n / 2)) :
    Set (ZMod n → GaloisField 3 (n / 2)) :=
  {y' | y' ∈ NFSet n 2 ∧ ∀ k : ZMod n, Even k.val → dftA ω y' k = dftA ω y k}

/-- `ŷ` restricted to the lower layers `μ_{n/2}` (even `k`): the label of a fibre. -/
noncomputable def lowerData {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (y : ZMod n → GaloisField 3 (n / 2)) :
    {k : ZMod n // Even k.val} → L :=
  fun k => dftA ω y k.1

variable (n) in
/-- `κ := n^2 p` in a ring (s6_primes.tex:47, :133). -/
def kappa (K : Type*) [CommRing K] : K := (n : K) ^ 2 * (pp n : K)

end Xia
