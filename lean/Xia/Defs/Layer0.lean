/- Xia/Defs/Layer0.lean — definitions (layer0', topData, topData0, Ggrp, tauG, Gprime, Pmap).
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry

namespace Xia

open Finset

variable {n : ℕ} [NeZero n] {L : Type*} [Field L]

variable (n) in
/-- `μ_{n_odd} ∖ {1}` (exponent model): the non-zero multiples of `2^a` (s4_normfree.tex:97). -/
def layer0' (a : ℕ) : Finset (ZMod n) := univ.filter (fun k => 2 ^ a ∣ k.val ∧ k ≠ 0)

variable (n) in
/-- Top data `𝒟` (s4_normfree.tex:73-76, r = 3; s6_primes.tex:165-166 for r): functions on the top layer (odd `k`) with
(F1_r) along the orbits `ŷ(ξ^r) = ξ^{rσ} ŷ(ξ)^r` and (F3_r) between `O` and `O^{-1}`, `ŷ(ξ)ŷ(ξ^{-1}) = κ ξ^m`;
value 0 off the top layer. (`r = 3`, `σ = 2`, `κ = 1` gives `𝒟` of Theorem 4.1.) -/
def topData (r : ℕ) (σ : ℤ) (κ : L) (ω : L) : Set (ZMod n → L) :=
  {h | (∀ k : ZMod n, Odd k.val → h ((r : ZMod n) * k) = (ω ^ k.val) ^ ((r : ℤ) * σ) * h k ^ r ∧
      h k * h (-k) = κ * (ω ^ k.val) ^ (n / 2)) ∧ ∀ k : ZMod n, Even k.val → h k = 0}

variable (n) in
/-- The homogeneous top data `𝒟^0` (s4_normfree.tex:76-77): `λ` on the top layer with (h1) `λ(ξ^r) = λ(ξ)^r` and (h3)
`λ(ξ)λ(ξ^{-1}) = 1`; value 1 off the top layer. -/
def topData0 (r : ℕ) : Set (ZMod n → L) :=
  {lam | (∀ k : ZMod n, Odd k.val → lam ((r : ZMod n) * k) = lam k ^ r ∧ lam k * lam (-k) = 1) ∧
    ∀ k : ZMod n, Even k.val → lam k = 1}

variable (n) in
/-- The group `G` (s4_normfree.tex:103-104; with `r` for 3, s6_primes.tex:180): maps `g` on `μ_{n_odd} ∖ {1}` with
`g(α^r) = g(α)^r` and `g(α^{-1}) = g(α)^{-1}`; value 1 elsewhere. -/
def Ggrp (a r : ℕ) : Set (ZMod n → L) :=
  {g | (∀ k ∈ layer0' n a, g ((r : ZMod n) * k) = g k ^ r ∧ g (-k) * g k = 1) ∧ ∀ k ∉ layer0' n a, g k = 1}

variable (n) in
/-- `(τ g)(α) := g(α^2)` on `μ_{n_odd} ∖ {1}` (value 1 elsewhere) (s4_normfree.tex:104-105). -/
noncomputable def tauG (a : ℕ) (g : ZMod n → L) : ZMod n → L :=
  fun k => if k ∈ layer0' n a then g (2 * k) else 1

variable (n) in
/-- `G'` (s4_normfree.tex:106): `f` on `μ_{n_odd} ∖ {1}` with (E2_r) `f(α^r) = α^{rσ} f(α)^r` and
(E3_r) `f(α)f(α^{-1}) = κ α^m`; value 1 elsewhere. (`G''` is the same set with `κ = 1`, s4_normfree.tex:106-107.) -/
def Gprime (a r : ℕ) (σ : ℤ) (κ : L) (ω : L) : Set (ZMod n → L) :=
  {f | (∀ k ∈ layer0' n a, f ((r : ZMod n) * k) = (ω ^ k.val) ^ ((r : ℤ) * σ) * f k ^ r ∧
      f k * f (-k) = κ * (ω ^ k.val) ^ (n / 2)) ∧ ∀ k ∉ layer0' n a, f k = 1}

variable (n) in
/-- `P_λ(α) := ∏_{ρ ∈ 𝓛_a, ρ^{2^{a-1}} = -α} λ(ρ)` on `μ_{n_odd} ∖ {1}` (value 1 elsewhere): the map `Π` of Step 6
(s4_normfree.tex:116-118); the same formula with `ŷ` gives `P` of Step 4 (:94). -/
noncomputable def Pmap (a : ℕ) (lam : ZMod n → L) : ZMod n → L :=
  fun k => if k ∈ layer0' n a then
    ∏ ρ ∈ (topLayer n).filter (fun ρ => (2 ^ (a - 1) : ZMod n) * ρ = k + half n), lam ρ else 1

end Xia
