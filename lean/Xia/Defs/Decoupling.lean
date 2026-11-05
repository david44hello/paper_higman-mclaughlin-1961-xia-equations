/- Xia/Defs/Decoupling.lean — definitions (QQ, qq, iota, Vsp, Tmap, Vplus, Vminus, Lam, ...).
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import Xia.Defs.Fourier

namespace Xia

open Finset

variable (n : ℕ) {F : Type*} [Field F]

/-- `Q := 3^{m/2} = 3^{n/4}` (s2_xia.tex:52). -/
def QQ : ℕ := 3 ^ (n / 4)

/-- `q := 3^{m/4} = 3^{n/8}` (s3_pow2.tex:85). -/
def qq : ℕ := 3 ^ (n / 8)

/-- `ι := ξ_0^{n/4}` (s3_pow2.tex:85). -/
def iota (ξ0 : F) : F := ξ0 ^ (n / 4)

/-- `V := {x ∈ F : x^Q = -x}` (s3_pow2.tex:85). -/
def Vsp : Set F := {x | x ^ QQ n = -x}

/-- `T(x) := ι x^q` (Thm 3.4(a), s3_pow2.tex:106). -/
def Tmap (ξ0 x : F) : F := iota n ξ0 * x ^ qq n

/-- `V_+ := {x ∈ V : T x = x}` (Thm 3.4(a)). -/
def Vplus (ξ0 : F) : Set F := {x | x ∈ Vsp n ∧ Tmap n ξ0 x = x}

/-- `V_- := {x ∈ V : T x = -x}` (Thm 3.4(a)). -/
def Vminus (ξ0 : F) : Set F := {x | x ∈ Vsp n ∧ Tmap n ξ0 x = -x}

/-- `Λ_ν(x) := ∑_{k=0}^{m/4-1} (ξ_0^{2k3^k} - ξ_0^{-2k3^k} (ιν)^{-3^k}) x^{3^k}` (s3_pow2.tex:99; `m/4 = n/8`). -/
def Lam (ξ0 ν x : F) : F :=
  ∑ k ∈ range (n / 8),
    (ξ0 ^ ((2 * k * 3 ^ k : ℕ) : ℤ) - ξ0 ^ (-((2 * k * 3 ^ k : ℕ) : ℤ)) * (iota n ξ0 * ν) ^ (-((3 ^ k : ℕ) : ℤ)))
      * x ^ (3 ^ k)

/-- `Λ'_ν(x) := ∑_{k=0}^{m/4-1} (ξ_0^{(2k-1)3^k} + ξ_0^{-(2k-1)3^k} (ιν)^{-3^k}) x^{3^k}` (s3_pow2.tex:100). -/
def Lam' (ξ0 ν x : F) : F :=
  ∑ k ∈ range (n / 8),
    (ξ0 ^ ((2 * (k : ℤ) - 1) * 3 ^ k) + ξ0 ^ (-((2 * (k : ℤ) - 1) * 3 ^ k)) * (iota n ξ0 * ν) ^ (-((3 ^ k : ℕ) : ℤ)))
      * x ^ (3 ^ k)

/-- `x^+ := (x + x̄)/2` (Remark 2.6; s3_pow2.tex:94: `y_j^± = (y_j ± \overline{y_j})/2`). -/
noncomputable def yPlus (x : F) : F := (x + bar n x) / 2

/-- `x^- := (x - x̄)/2`. -/
noncomputable def yMinus (x : F) : F := (x - bar n x) / 2

/-- The parameter map of Theorem 3.1: `y ↦ (ŷ(ξ_0), S, ŷ(1))` (`ξ_0 = ω^1`, `1 = ω^0`). -/
def paramMap [NeZero n] (ξ0 : F) (y : ZMod n → F) : F × F × F := (dft ξ0 y 1, S y, dft ξ0 y 0)

end Xia
