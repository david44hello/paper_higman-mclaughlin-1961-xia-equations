/- Xia/Defs/DiffSet.lean — definitions (Hpow, IsDiffSet).
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry

namespace Xia

variable (p : ℕ)

/-- `H_{q,m} := {a^m : a ∈ F_q^×}`, the non-zero `m`-th powers (Xia v7 p. 2; `H_{v,n}` in Prop 1.2). -/
def Hpow (m : ℕ) : Set (ZMod p) := {a | ∃ b : ZMod p, b ≠ 0 ∧ a = b ^ m}

/-- `D` is a `(|G|, k, λ)`-difference set in `F_p^+` (Xia v7 p. 2: `|D| = k` and every non-identity `a` is `a_s - a_t`
for exactly `λ` ordered pairs `(a_s, a_t) ∈ D × D`). -/
def IsDiffSet (D : Set (ZMod p)) (k lam : ℕ) : Prop :=
  D.ncard = k ∧ ∀ d : ZMod p, d ≠ 0 → Nat.card {pr : ZMod p × ZMod p // pr.1 ∈ D ∧ pr.2 ∈ D ∧ pr.1 - pr.2 = d} = lam

end Xia
