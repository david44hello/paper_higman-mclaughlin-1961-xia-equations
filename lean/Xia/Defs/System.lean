/- Xia/Defs/System.lean — definitions (sgn, half, R, S, L1, L2, L3, L4, ...).
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Mathlib

namespace Xia

open Finset

/-- `5` is prime (needed for `GaloisField 5 _`; Mathlib registers only 2 and 3). -/
instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

section Equations

variable {K : Type*} [CommRing K] {n : ℕ} [NeZero n]

/-- `(-1)^t` for `t ∈ ℤ/n`, computed on the representative `t.val ∈ {0,…,n-1}` (the paper's sums run over
`t = 0,…,n-1`; for even `n` this is the same as any other representative). -/
def sgn (t : ZMod n) : K := (-1) ^ t.val

/-- The index `n/2` in `ℤ/n` (the paper's `m = n/2`). -/
def half (n : ℕ) : ZMod n := ((n / 2 : ℕ) : ZMod n)

/-- Periodic autocorrelation `R(s) := ∑_t y_t y_{t+s}`, `s ∈ ℤ/n` (P10s_main.tex:122-123; s2_xia.tex:59). -/
def R (y : ZMod n → K) (s : ZMod n) : K := ∑ t, y t * y (t + s)

/-- `S := ∑_{t=0}^{n-1} (-1)^t y_t` (s2_xia.tex:62; s6_primes.tex:26). -/
def S (y : ZMod n → K) : K := ∑ t, sgn t * y t

/-- (L1) with shift `σ` and exponent `r`: `y_{s+σ} = y_s^r` for EVERY `s ∈ ℤ/n` (eq:xia12 (L1) for `r = 3`;
(L1_5) s6_primes.tex:23 with `σ = 1`; (L1_r) s6_primes.tex:128 with any integer `σ_r`). -/
def L1 (r : ℕ) (σ : ℤ) (y : ZMod n → K) : Prop := ∀ s : ZMod n, y (s + σ) = y s ^ r

/-- (L2) with constant `c`: `y_s y_{s+n/2} = c` for `s = 0,1,…,n/2-1` ONLY (eq:xia12 (L2), `c = -1`;
(L2_5)/(L2_r), `c = n^3`). -/
def L2 (c : K) (y : ZMod n → K) : Prop := ∀ s : ZMod n, s.val < n / 2 → y s * y (s + half n) = c

/-- (L3) with constant `c`: `∑_{t=0}^{n-1} y_t y_{s+t} = c` for `s = 0,1,…,n/2-1` ONLY (eq:xia12 (L3), `c = 0`;
(L3_5)/(L3_r), `c = n(1-p)`). Index range matters: for all `s` it would force `R(n/2) = c`. -/
def L3 (c : K) (y : ZMod n → K) : Prop := ∀ s : ZMod n, s.val < n / 2 → ∑ t, y t * y (s + t) = c

/-- (L4): `∑_{t=0}^{n-1} (-1)^t y_t y_{2s-t} = (y_s + y_{s+n/2}) ∑_{t=0}^{n-1} (-1)^t y_t` for `s = 0,1,…,n/2-1`
ONLY (eq:xia12 (L4); the factor multiplies the whole alternating sum, s2_xia.tex:14). -/
def L4 (y : ZMod n → K) : Prop :=
  ∀ s : ZMod n, s.val < n / 2 → ∑ t, sgn t * y t * y (2 * s - t) = (y s + y (s + half n)) * S y

/-- Xia's system (1) = eq:xia12 (P10s_main.tex:90) with shift `σ`: (L1) `y_{s+σ} = y_s^3`, (L2) `= -1`,
(L3) `= 0`, (L4). -/
def XiaEqs (σ : ℤ) (y : ZMod n → K) : Prop := L1 3 σ y ∧ L2 (-1) y ∧ L3 0 y ∧ L4 y

/-- Definition 2.3 (s2_xia.tex:64): the norm-free system with shift `σ` = (L1), (L3), `R(m) = 1`, (L4). -/
def NormFreeEqs (σ : ℤ) (y : ZMod n → K) : Prop := L1 3 σ y ∧ L3 0 y ∧ R y (half n) = 1 ∧ L4 y

/-- `p := n^2 + n + 1` (s2_xia.tex:8). -/
def pp (n : ℕ) : ℕ := n ^ 2 + n + 1

/-- Xia's system in characteristic `r` (s6_primes.tex:128; eq:xia125 for `r = 5`, `σ_r = 1`):
(L1_r) `y_{s+σ_r} = y_s^r`, (L2_r) `y_s y_{s+m} = n^3`, (L3_r) `∑_t y_t y_{s+t} = n(1-p)`, (L4_r) = (L4). -/
def RSysEqs (r : ℕ) (σr : ℤ) (y : ZMod n → K) : Prop :=
  L1 r σr y ∧ L2 ((n : K) ^ 3) y ∧ L3 ((n : K) * (1 - (pp n : K))) y ∧ L4 y

/-- The norm-free `r`-system (s6_primes.tex:45 for `r = 5`; :132 in general): (L1_r), (L3_r), `R(m) = n^4`, (L4_r). -/
def NFrEqs (r : ℕ) (σr : ℤ) (y : ZMod n → K) : Prop :=
  L1 r σr y ∧ L3 ((n : K) * (1 - (pp n : K))) y ∧ R y (half n) = (n : K) ^ 4 ∧ L4 y

end Equations

section Sets

variable (n : ℕ) [NeZero n]

/-- Solutions of Xia's system (1) with shift `σ` in `F_{3^{n/σ}}^n` (Thm 2.1, s2_xia.tex:11). -/
def XiaSet (σ : ℕ) : Set (ZMod n → GaloisField 3 (n / σ)) := {y | XiaEqs (σ : ℤ) y}

/-- Solutions of the norm-free system with shift `σ` in `F_{3^{n/σ}}^n` (Def 2.3). For `σ = 2` this is
`NF(n) ⊂ F^n`, `F = F_{3^{n/2}}` (s4_normfree.tex:7). -/
def NFSet (σ : ℕ) : Set (ZMod n → GaloisField 3 (n / σ)) := {y | NormFreeEqs (σ : ℤ) y}

/-- Solutions of eq:xia125 (s6_primes.tex:21) in `F_{5^n}^n`: Xia's `r = 5` system with `σ_5 = 1`. -/
def Xia5Set : Set (ZMod n → GaloisField 5 n) := {y | RSysEqs 5 1 y}

/-- Solutions of the norm-free `r = 5` system (s6_primes.tex:45) in `F_{5^n}^n`. -/
def NF5Set : Set (ZMod n → GaloisField 5 n) := {y | NFrEqs 5 1 y}

/-- Solutions of the norm-free `r`-system with any integer shift `σ_r` in `F_{r^{n/g}}^n`, `g = gcd(σ_r, n)`
(s6_primes.tex:132). -/
def NFrSet (r : ℕ) [Fact r.Prime] (σr : ℤ) : Set (ZMod n → GaloisField r (n / Int.gcd σr n)) :=
  {y | NFrEqs r σr y}

end Sets

section Norms

variable {K : Type*} [Monoid K]

/-- `N(x) := x^{1+3^{n/4}}`, the norm from `F_{3^{n/2}}` to `F_{3^{n/4}}` (P10s_main.tex:127; s2_xia.tex:53
`N(x) = x x̄`, `x̄ = x^Q`, `Q = 3^{m/2}`). -/
def Nm (n : ℕ) (x : K) : K := x ^ (1 + 3 ^ (n / 4))

/-- `N_5(x) := x^{1+5^{n/2}}` (s6_primes.tex:108). -/
def Nm5 (n : ℕ) (x : K) : K := x ^ (1 + 5 ^ (n / 2))

/-- `x̄ := x^Q`, `Q = 3^{n/4}` (s2_xia.tex:52; the involution of `F` over `k_0`). -/
def bar (n : ℕ) (x : K) : K := x ^ (3 ^ (n / 4))

end Norms

end Xia
