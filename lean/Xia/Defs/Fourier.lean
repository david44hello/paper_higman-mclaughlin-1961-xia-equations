/- Xia/Defs/Fourier.lean — definitions (dft, dftA, F1, F3, F4, F3r, orbit, topLayer, ...).
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import Xia.Defs.System

namespace Xia

open Finset

section DFT

variable {n : ℕ} [NeZero n] {L : Type*} [CommRing L]

/-- `ŷ(ξ) := ∑_{t ∈ ℤ/n} y_t ξ^t` at `ξ = ω^k` (P10s_main.tex:145; s2_xia.tex:75). -/
def dft (ω : L) (y : ZMod n → L) (k : ZMod n) : L := ∑ t, y t * (ω ^ k.val) ^ t.val

/-- `ŷ` of a sequence `y ∈ F^n`, computed in an extension `L ⊇ F` that contains `μ_n`. -/
def dftA {F : Type*} [CommRing F] [Algebra F L] (ω : L) (y : ZMod n → F) (k : ZMod n) : L :=
  dft ω (fun t => algebraMap F L (y t)) k

end DFT

section Laws

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

/-- (F1_σ) with exponent `r` (`ξ = ω^k`): `ŷ(ξ^r) = ξ^{rσ} ŷ(ξ)^r`. `r = 3, σ = 2` is (F1) of Prop 2.4
(s2_xia.tex:83); `r = 3` is (F1_σ) (s4_normfree.tex:155); general `r` is (F1_r) (s6_primes.tex:134). -/
def F1 (r : ℕ) (σ : ℤ) (ω : L) (h : ZMod n → L) : Prop :=
  ∀ k : ZMod n, h ((r : ZMod n) * k) = (ω ^ k.val) ^ ((r : ℤ) * σ) * h k ^ r

/-- (F3): `ŷ(ξ) ŷ(ξ^{-1}) = ξ^m` for all `ξ ∈ μ_n` (s2_xia.tex:84). -/
def F3 (ω : L) (h : ZMod n → L) : Prop := ∀ k : ZMod n, h k * h (-k) = (ω ^ k.val) ^ (n / 2)

/-- (F4): `ŷ(ξ) ŷ(-ξ) = ŷ(-1) ŷ(ξ^2)` for all `ξ ∈ μ_n` (s2_xia.tex:85; = (F4_r)). -/
def F4 (h : ZMod n → L) : Prop := ∀ k : ZMod n, h k * h (k + half n) = h (half n) * h (2 * k)

/-- (F3_r) with constant `κ`: `ŷ(ξ) ŷ(ξ^{-1}) = κ ξ^m` for `ξ ≠ 1`, and `ŷ(1)^2 = n^2` (s6_primes.tex:56, :134). -/
def F3r (κ : L) (ω : L) (h : ZMod n → L) : Prop :=
  (∀ k : ZMod n, k ≠ 0 → h k * h (-k) = κ * (ω ^ k.val) ^ (n / 2)) ∧ h 0 ^ 2 = (n : L) ^ 2

end Laws

section Orbits

variable {n : ℕ} [NeZero n]

open Classical in
/-- The orbit `{r^i k : i ∈ ℕ}` of `k ∈ ℤ/n` under `k ↦ rk` (exponent model of `ξ ↦ ξ^r`). -/
noncomputable def orbit (r : ℕ) (k : ZMod n) : Finset (ZMod n) :=
  univ.filter (fun j => ∃ i : ℕ, j = (r : ZMod n) ^ i * k)

variable (n) in
/-- The top layer `𝓛_a` (exponent model): `ξ = ω^k` has order divisible by `2^a` iff `k` is odd
(P10s_main.tex:143; s4_normfree.tex:11). -/
def topLayer : Finset (ZMod n) := univ.filter (fun k => Odd k.val)

variable (n) in
/-- The orbits of `ξ ↦ ξ^r` on the top layer. -/
noncomputable def topOrbits (r : ℕ) : Finset (Finset (ZMod n)) := (topLayer n).image (orbit r)

/-- `O^{-1}` (exponent model: negation). -/
def inv (O : Finset (ZMod n)) : Finset (ZMod n) := O.image Neg.neg

/-- `-O` (exponent model: add `n/2`). -/
def negO (O : Finset (ZMod n)) : Finset (ZMod n) := O.image (· + half n)

variable (n) in
/-- The index set `I` of pairs `{O, O^{-1}}` of top orbits (P10s_main.tex:143-144; s4_normfree.tex:15). -/
noncomputable def topPairs (r : ℕ) : Finset (Finset (Finset (ZMod n))) :=
  (topOrbits n r).image (fun O => {O, inv O})

/-- The common length `L_i` of a pair `{O, O^{-1}}`: half the size of `O ∪ O^{-1}` (equal to `|O|` once
`O ≠ O^{-1}` and `|O| = |O^{-1}|`, which Thm 4.1 states). -/
def pairLen (P : Finset (Finset (ZMod n))) : ℕ := (P.biUnion id).card / 2

variable (n) in
/-- `∏_{i ∈ I} (r^{L_i} - 1)` (Thm A, Thm 4.1, Thm 6.4). -/
noncomputable def pairProd (r : ℕ) : ℕ := ∏ P ∈ topPairs n r, (r ^ pairLen P - 1)

/-- Case A orbit (s5_twonorms.tex:20): `-O = O`. -/
def IsCaseA (O : Finset (ZMod n)) : Prop := negO O = O

/-- Case B orbit (s5_twonorms.tex:20): `-O = O^{-1}`. -/
def IsCaseB (O : Finset (ZMod n)) : Prop := negO O = inv O

/-- The block of an orbit: `{O, O^{-1}}` in cases A and B, `{O, O^{-1}, -O, -O^{-1}}` in case C (as a set of orbits,
the same formula covers all three cases). -/
def blockOf (O : Finset (ZMod n)) : Finset (Finset (ZMod n)) := {O, inv O, negO O, negO (inv O)}

variable (n) in
/-- All blocks of the top orbits for `r = 3` (s5_twonorms.tex:21). -/
noncomputable def blocks : Finset (Finset (Finset (ZMod n))) := (topOrbits n 3).image blockOf

/-- Orbit length `L` of a block: size of its union divided by its number of orbits. -/
def blockLen (B : Finset (Finset (ZMod n))) : ℕ := (B.biUnion id).card / B.card

open Classical in
variable (n) in
/-- The blocks of case A (`𝒜`), of case B (`ℬ`), of case C (`𝒞`). -/
noncomputable def blocksA : Finset (Finset (Finset (ZMod n))) := (blocks n).filter (fun B => ∃ O ∈ B, IsCaseA O)

open Classical in
variable (n) in
noncomputable def blocksB : Finset (Finset (Finset (ZMod n))) := (blocks n).filter (fun B => ∃ O ∈ B, IsCaseB O)

open Classical in
variable (n) in
noncomputable def blocksC : Finset (Finset (Finset (ZMod n))) :=
  (blocks n).filter (fun B => ∀ O ∈ B, ¬ IsCaseA O ∧ ¬ IsCaseB O)

/-- `q_O := 3^{L/2}` for a block of case A or B (s5_twonorms.tex:22). -/
def qO (B : Finset (Finset (ZMod n))) : ℕ := 3 ^ (blockLen B / 2)

variable (n) in
/-- Size `Φ` of a non-empty fibre (Thm 5.1(c)): `∏_𝒜 (q_O+1) ∏_ℬ (q_O-1) ∏_𝒞 (3^L-1)`. -/
noncomputable def fibreSize : ℕ :=
  (∏ B ∈ blocksA n, (qO B + 1)) * (∏ B ∈ blocksB n, (qO B - 1)) * (∏ B ∈ blocksC n, (3 ^ blockLen B - 1))

variable (n) in
/-- `∏_𝒜 (q_O-1) ∏_ℬ (q_O+1) ∏_𝒞 (3^L-1)`: the number of non-empty fibres is 4 times it (Thm 5.1(c)), the bound of
Cor 5.2 is 16 times it. -/
noncomputable def fibreProd : ℕ :=
  (∏ B ∈ blocksA n, (qO B - 1)) * (∏ B ∈ blocksB n, (qO B + 1)) * (∏ B ∈ blocksC n, (3 ^ blockLen B - 1))

end Orbits

end Xia
