/-
Xia/Paper/Statements.lean — one Lean theorem per claim of the paper "Xia's equations for the Higman–McLaughlin (1961)
conjecture: exact counts and the two norm conditions" (Dave Goel). Copyright (C) Dave Goel 2026--now. All rights reserved.
A claim with several parts has one row per part and a row for the printed conjunction. Pointers "file:line" are lines
of the paper's TeX sources (P10s_main.tex, s2_xia.tex, ..., s6_primes.tex). Every row is proved; the status of each row
and each printed claim, as Lean reports it, is in AUDIT.md; modelling choices are in AUDIT_NOTES.md.
Exponent model of μ_n: see Xia/Defs/Fourier.lean (h k = ŷ(ω^k); -ξ ↔ k + n/2; ξ^{-1} ↔ -k; top layer ↔ odd k).
-/
import Xia.Defs.Symmetry
import Xia.Proofs.VBlocks
import Xia.Proofs.Lemma41
import Xia.Proofs.Thm34b
import Xia.Proofs.Prop61Final
import Xia.Proofs.VcV
import Xia.Proofs.VdV
import Xia.Proofs.Thm64Step67
import Xia.Proofs.Thm34bc
import Xia.Proofs.Thm41Steps57
import Xia.Proofs.Thm41Steps26
import Xia.Proofs.Thm62
import Xia.Proofs.FourierR
import Xia.Proofs.Prop61
import Xia.Proofs.Prop61Uncond
import Xia.Proofs.Prop24
import Xia.Proofs.Decoupling34
import Xia.Proofs.Coverage
import Xia.Proofs.Thm31
import Xia.Proofs.Rem44
import Xia.Proofs.Thm64
import Xia.Proofs.FibreCount
import Xia.Proofs.PrimRoot
import Xia.Proofs.Sec5
import Xia.Proofs.Thm41
import Xia.Proofs.Links
import Xia.Proofs.FourierSteps
import Xia.Proofs.Combinatorics
import Xia.Proofs.Signs
import Xia.Proofs.Pow2Arith
import Xia.Defs.Layer0
import Xia.Defs.DiffSet
import Xia.Defs.BlockSpace
import Xia.Proofs.NumberTheory
import Xia.Proofs.Sec22
import Xia.Proofs.BSubst
import Xia.Proofs.BIff
import Xia.Proofs.EPow3
import Xia.Proofs.SigmaOfN
import Xia.Proofs.Sigma80
import Xia.Proofs.Cor35Fibre
import Xia.Proofs.R3
import Xia.Proofs.Fig2
import Xia.Proofs.NormLayers

namespace Xia.Paper

open Xia Finset

/-! ## Section 2.1 — Xia's theorem and Lemma 2.2 -/

/-- Row 2a — Lemma 2.2, first sentence (s2_xia.tex:20-21): let `8 ∣ n` and `p = n^2+n+1` be prime; then `3` is a
fourth power modulo `p` if and only if `3 ∣ n`. -/
theorem lem_2_2_fourth_power (n : ℕ) (h8 : 8 ∣ n) (hp : (pp n).Prime) :
    (∃ z : ZMod (pp n), z ^ 4 = 3) ↔ 3 ∣ n :=
  Xia.Proofs.lem_2_2_fourth_power_proved n h8 hp

/-- Row 2b — Lemma 2.2, "Consequently" (s2_xia.tex:21-22, proof :35-42): let `n ≡ 8 (mod 24)` and `p` prime. Let `χ` be
a multiplicative character on `F_p` of order `n` (`χ(g)` a primitive `n`-th root of unity for a generator `g`), with
values in any field `M` (Xia: `M = ℂ_3`), `ϖ ∈ M` a primitive `n`-th root of unity and `σ` a positive divisor of `n`
with `χ(3) = ϖ^σ` (Xia's `σ`, s2_xia.tex:15-17). Then `σ ≡ 2 (mod 4)`, and `σ = 2` when `n` is a power of `2`. -/
theorem lem_2_2_sigma (n : ℕ) (hn : n % 24 = 8) (hp : (pp n).Prime) {M : Type*} [Field M]
    (χ : MulChar (ZMod (pp n)) M) (g : (ZMod (pp n))ˣ) (hg : ∀ x : (ZMod (pp n))ˣ, x ∈ Subgroup.zpowers g)
    (hχg : IsPrimitiveRoot (χ (g : ZMod (pp n))) n) (ϖ : M) (hϖ : IsPrimitiveRoot ϖ n) (σ : ℕ) (hσ : σ ∣ n)
    (hσ0 : 0 < σ) (h3 : χ 3 = ϖ ^ σ) :
    σ % 4 = 2 ∧ ∀ e : ℕ, n = 2 ^ e → σ = 2 :=
  Xia.Proofs.lem_2_2_sigma_proved n hn hp χ g hg hχg ϖ hϖ σ hσ hσ0 h3

/-- Row 2c — proof of Lemma 2.2, last sentence (s2_xia.tex:42-43): a power `n = 2^e` with `8 ∣ n` and `p` prime has
`e` odd, so it lies in the range `n ≡ 8 (mod 24)`. -/
theorem lem_2_2_pow2 (e : ℕ) (h8 : 8 ∣ 2 ^ e) (hp : (pp (2 ^ e)).Prime) : Odd e ∧ 2 ^ e % 24 = 8 :=
  Xia.Proofs.lem_2_2_pow2_proved e h8 hp

/-! ## Section 2.2 — the case σ = 2 and the norm-free system -/

/-- Row 3a — s2_xia.tex:53-55: for `n ≡ 8 (mod 24)` and `σ = 2`, (L1) gives `y_{2k} = φ^k(y_0)`,
`y_{2k+1} = φ^k(y_1)` and `y_{t+m} = ȳ_t` (`φ(x) = x^3`, `x̄ = x^Q`, `Q = 3^{m/2}`). -/
theorem sec_2_2_frobenius (n : ℕ) [NeZero n] (hn : n % 24 = 8) (y : ZMod n → GaloisField 3 (n / 2))
    (h1 : L1 3 2 y) :
    (∀ k : ℕ, y ((2 * k : ℕ) : ZMod n) = y 0 ^ (3 ^ k) ∧ y ((2 * k + 1 : ℕ) : ZMod n) = y 1 ^ (3 ^ k)) ∧
      ∀ t : ZMod n, y (t + half n) = bar n (y t) :=
  Xia.Proofs.sec_2_2_frobenius_proved n hn y h1

/-- Row 3b — s2_xia.tex:57: hence (L2) holds if and only if `N(y_0) = N(y_1) = -1`. -/
theorem sec_2_2_L2_iff (n : ℕ) [NeZero n] (hn : n % 24 = 8) (y : ZMod n → GaloisField 3 (n / 2)) (h1 : L1 3 2 y) :
    L2 (-1) y ↔ Nm n (y 0) = -1 ∧ Nm n (y 1) = -1 :=
  Xia.Proofs.sec_2_2_L2_iff_proved n hn y h1

/-- Row 3c — s2_xia.tex:59-60 (also P10s_main.tex:121-122): `R(-s) = R(s)`; (L3) gives `R(s) = 0` for every `s ≢ m`;
(L2) gives `R(m) = ∑_t (-1) = -n`. (Any even `n`, any commutative ring.) -/
theorem sec_2_2_R (n : ℕ) [NeZero n] (hn : Even n) {K : Type*} [CommRing K] (y : ZMod n → K) :
    (∀ s, R y (-s) = R y s) ∧ (L3 0 y → ∀ s, s ≠ half n → R y s = 0) ∧
      (L2 (-1) y → R y (half n) = -(n : K)) :=
  Xia.Proofs.sec_2_2_R_proved n hn y

/-- Row 3d — s2_xia.tex:68 (also P10s_main.tex:126-127): for `n ≡ 8 (mod 24)`, every solution of (1) with `σ = 2`
solves the norm-free system, and the solutions of (1) are exactly the norm-free solutions with `N(y_0) = N(y_1) = -1`. -/
theorem sec_2_2_xia_eq (n : ℕ) [NeZero n] (hn : n % 24 = 8) :
    XiaSet n 2 ⊆ NFSet n 2 ∧ XiaSet n 2 = {y | y ∈ NFSet n 2 ∧ Nm n (y 0) = -1 ∧ Nm n (y 1) = -1} :=
  Xia.Proofs.sec_2_2_xia_eq_proved n hn

/-- Row 27 — Theorem A, last sentence (P10s_main.tex:154-155; with s2_xia.tex:60): for `n ≡ 8 (mod 24)` and EVERY
divisor `σ` of `n`, every solution of Xia's system (1) with shift `σ` solves the norm-free system with shift `σ`. -/
theorem xia_sub_nf (n : ℕ) [NeZero n] (hn : n % 24 = 8) (σ : ℕ) (hσ : σ ∣ n) : XiaSet n σ ⊆ NFSet n σ :=
  Xia.Proofs.xia_sub_nf_proved n hn σ hσ

/-- Coverage — P10s_main.tex:121-125: `-n = 1` in `F_3` exactly when `n ≡ 2 (mod 3)`; so only then does summing (L2)
give `R(n/2) = 1`. -/
theorem intro_sum_L2 (n : ℕ) : (-(n : ZMod 3) = 1) ↔ n % 3 = 2 :=
  Xia.Proofs.intro_sum_L2_proved n

/-- Coverage — P10s_main.tex:158-160: deleting the norm equation leaves the trivial solution `y = 0` of (L1), (L3),
(L4); the consequence `R(n/2) = 1` excludes `y = 0`. -/
theorem intro_zero (n σ : ℕ) [NeZero n] :
    (L1 3 (σ : ℤ) (0 : ZMod n → GaloisField 3 (n / σ)) ∧ L3 0 (0 : ZMod n → GaloisField 3 (n / σ)) ∧
      L4 (0 : ZMod n → GaloisField 3 (n / σ))) ∧ R (0 : ZMod n → GaloisField 3 (n / σ)) (half n) ≠ 1 :=
  Xia.Proofs.intro_zero_proved n σ

/-! ## Section 2.3 — Fourier form (n even, 3 ∤ n, F = F_{3^{n/2}}, L ⊇ F with a primitive n-th root ω) -/

/-- Row 4a — Proposition 2.4 (s2_xia.tex:79-81): `y ↦ ŷ` is a bijection from the solutions of the norm-free system
onto the functions `ŷ : μ_n → L` with (F1), (F3), (F4). -/
theorem prop_2_4_bij (n : ℕ) [NeZero n] (hn : Even n) (h3 : ¬ 3 ∣ n) {L : Type*} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) :
    Set.BijOn (dftA ω) (NFSet n 2) {h | F1 3 2 ω h ∧ F3 ω h ∧ F4 h} :=
  Xia.Proofs.prop_2_4_bij_proved n hn h3 ω hω

/-- Row 4b — Proposition 2.4 (s2_xia.tex:87): (F1) is equivalent to (L1). -/
theorem prop_2_4_F1 (n : ℕ) [NeZero n] (hn : Even n) (h3 : ¬ 3 ∣ n) {L : Type*} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2)) :
    L1 3 2 y ↔ F1 3 2 ω (dftA ω y) :=
  Xia.Proofs.prop_2_4_F1_proved n hn h3 ω hω y

/-- Row 4c — Proposition 2.4 (s2_xia.tex:87): (F3) is equivalent to (L3) together with `R(m) = 1`. -/
theorem prop_2_4_F3 (n : ℕ) [NeZero n] (hn : Even n) (h3 : ¬ 3 ∣ n) {L : Type*} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2)) :
    (L3 0 y ∧ R y (half n) = 1) ↔ F3 ω (dftA ω y) :=
  Xia.Proofs.prop_2_4_F3_proved n hn h3 ω hω y

/-- Row 4d — Proposition 2.4 (s2_xia.tex:87): (F4) is equivalent to (L4). -/
theorem prop_2_4_F4 (n : ℕ) [NeZero n] (hn : Even n) (h3 : ¬ 3 ∣ n) {L : Type*} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2)) :
    L4 y ↔ F4 (dftA ω y) :=
  Xia.Proofs.prop_2_4_F4_proved n hn h3 ω hω y

/-- Row 4e — Proposition 2.4 (s2_xia.tex:87-89): for a solution, `ŷ` has no zero on `μ_n`,
`ŷ(ξ^{3^j}) = ξ^{2j3^j} ŷ(ξ)^{3^j}` for every `j ≥ 0`, and `S^2 = (-1)^m`. -/
theorem prop_2_4_more (n : ℕ) [NeZero n] (hn : Even n) (h3 : ¬ 3 ∣ n) {L : Type*} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2))
    (hy : y ∈ NFSet n 2) :
    (∀ k, dftA ω y k ≠ 0) ∧
      (∀ (j : ℕ) (k : ZMod n), dftA ω y ((3 : ZMod n) ^ j * k) = (ω ^ k.val) ^ (2 * j * 3 ^ j) * dftA ω y k ^ (3 ^ j)) ∧
      S y ^ 2 = (-1) ^ (n / 2) :=
  Xia.Proofs.prop_2_4_more_proved n hn h3 ω hω y hy

/-- Coverage — s2_xia.tex:75, :77: the inversion formula `y_t = n^{-1} ∑_ξ ŷ(ξ) ξ^{-t}` (whenever `n` is invertible in
`L`), and `S = ŷ(-1)`. -/
theorem fourier_inversion (n : ℕ) [NeZero n] (hn : Even n) {L : Type*} [Field L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (hnL : (n : L) ≠ 0) (y : ZMod n → L) :
    (∀ t : ZMod n, y t = (n : L)⁻¹ * ∑ k : ZMod n, dft ω y k * ((ω ^ k.val)⁻¹) ^ t.val) ∧
      dft ω y (half n) = S y :=
  Xia.Proofs.fourier_inversion_proved n hn ω hω hnL y

/-- Row 6 — Remark 2.6 (s2_xia.tex:115-127), `m` even (`4 ∣ n`), `y` a solution of the norm-free system:
`y^± := (y ± ȳ)/2`; `y^+` has period `m` and values in `k_0`; `\overline{y^-_t} = -y^-_t`, `y^-_{t+m} = -y^-_t`; the cross
terms of (L3) and (L4) vanish; (L3) splits (`y^±` have zero autocorrelation off `s ∈ {0, m}`); `ŷ^+` vanishes on the
top layer and `ŷ^-` on `μ_m`, so `ŷ = ŷ^+` on `μ_m` and `ŷ = ŷ^-` on the top layer; (L4) reads
`ŷ^+(ξ)ŷ^+(-ξ) = S ŷ^+(ξ^2)` on `μ_m` and `ŷ^-(ξ)ŷ^-(-ξ) = S ŷ^+(ξ^2)` on the top layer; the right side of (L4) is
`2 S y^+_s`; and (L2) holds iff `(y^+_t)^2 - (y^-_t)^2 = -1` for every `t`. -/
theorem rem_2_6 (n : ℕ) [NeZero n] (h4 : 4 ∣ n) (h3 : ¬ 3 ∣ n) {L : Type*} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2))
    (hy : y ∈ NFSet n 2) :
    let yp : ZMod n → GaloisField 3 (n / 2) := fun t => yPlus n (y t)
    let ym : ZMod n → GaloisField 3 (n / 2) := fun t => yMinus n (y t)
    (∀ t, yp (t + half n) = yp t ∧ bar n (yp t) = yp t ∧ bar n (ym t) = -ym t ∧ ym (t + half n) = -ym t) ∧
      (∀ s, ∑ t, yp t * ym (t + s) = 0 ∧ ∑ t, sgn t * yp t * ym (2 * s - t) = 0) ∧
      (∀ s, s ≠ 0 → s ≠ half n → R yp s = 0 ∧ R ym s = 0) ∧
      (∀ k : ZMod n, Odd k.val → dftA ω yp k = 0) ∧ (∀ k : ZMod n, Even k.val → dftA ω ym k = 0) ∧
      (∀ k : ZMod n, Even k.val → dftA ω y k = dftA ω yp k) ∧ (∀ k : ZMod n, Odd k.val → dftA ω y k = dftA ω ym k) ∧
      (∀ k : ZMod n, Even k.val →
        dftA ω yp k * dftA ω yp (k + half n) = algebraMap _ L (S y) * dftA ω yp (2 * k)) ∧
      (∀ k : ZMod n, Odd k.val →
        dftA ω ym k * dftA ω ym (k + half n) = algebraMap _ L (S y) * dftA ω yp (2 * k)) ∧
      (∀ s : ZMod n, S y * (y s + y (s + half n)) = 2 * S y * yp s) ∧
      (L2 (-1) y ↔ ∀ t, yp t ^ 2 - ym t ^ 2 = -1) :=
  Xia.Proofs.rem_2_6_of n h4 h3 ω hω y hy
    (prop_2_4_F4 n (Xia.Proofs.H9_even_of_four_dvd h4) h3 ω hω y)

/-! ## Section 3.1 — n = 2^e: one parameter and two signs -/

/-- Row 7a — Theorem 3.1 "fix `ξ_0 ∈ F` of order `n`" (s3_pow2.tex:11) with Step 1 (:20-21, `μ_n ⊂ k_0 ⊂ F`): for
`n = 2^e`, `e ≥ 3`, `F` contains a primitive `n`-th root of unity, and every `n`-th root of unity in `F` lies in `k_0`
(`ξ^Q = ξ`). -/
theorem thm_3_1_xi0 (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) :
    (∃ ξ0 : GaloisField 3 (n / 2), IsPrimitiveRoot ξ0 n) ∧
      ∀ ξ : GaloisField 3 (n / 2), ξ ^ n = 1 → ξ ^ QQ n = ξ :=
  Xia.Proofs.thm_3_1_xi0_proved n e hne he

/-- Row 7d — s3_pow2.tex:17: `{θ ∈ F : θ^{Q-1} = -1}` has `Q-1` elements; `2(Q-1)` divides `3^m - 1`; the set is
`μ_{2(Q-1)} ∖ μ_{Q-1}`. -/
theorem thm_3_1_theta_set (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) :
    Nat.card {θ : GaloisField 3 (n / 2) // θ ^ (QQ n - 1) = -1} = QQ n - 1 ∧ 2 * (QQ n - 1) ∣ 3 ^ (n / 2) - 1 ∧
      {θ : GaloisField 3 (n / 2) | θ ^ (QQ n - 1) = -1} =
        {θ | θ ^ (2 * (QQ n - 1)) = 1} \ {θ | θ ^ (QQ n - 1) = 1} :=
  Xia.Proofs.thm_3_1_theta_set_proved n e hne he

/-- Row 7e — proof of Theorem 3.1, Step 1 (s3_pow2.tex:20-24): `v_2(3^m - 1) = e+1` and `v_2(Q-1) = e`;
`(ℤ/2^e)^× = {±1} × ⟨3⟩` with `ord(3) = 2^{e-2}`; the elements of order `n` form the two orbits `{ξ_0^{3^k}}` and
`{ξ_0^{-3^k}}` (exponent model: `{3^k}` and `{-3^k}` in `ℤ/n`), exchanged by inversion and disjoint; every element of
order `2^j`, `1 ≤ j ≤ e-1`, has exactly two square roots `±ξ` in `μ_n`, both of order `2^{j+1}`. -/
theorem thm_3_1_step1 (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) :
    padicValNat 2 (3 ^ (n / 2) - 1) = e + 1 ∧ padicValNat 2 (QQ n - 1) = e ∧
      orderOf (3 : ZMod n) = 2 ^ (e - 2) ∧
      (∀ x : ZMod n, IsUnit x → ∃ k : ℕ, x = (3 : ZMod n) ^ k ∨ x = -(3 : ZMod n) ^ k) ∧
      (∀ k : ℕ, (-1 : ZMod n) ≠ (3 : ZMod n) ^ k) ∧
      (∀ x : ZMod n, Odd x.val → orbit 3 x = orbit 3 1 ∨ orbit 3 x = inv (orbit 3 1)) ∧
      Disjoint (orbit 3 (1 : ZMod n)) (inv (orbit 3 1)) ∧
      ∀ (j : ℕ), 1 ≤ j → j ≤ e - 1 → ∀ x : ZMod n, addOrderOf x = 2 ^ j →
        ∃ z : ZMod n, addOrderOf z = 2 ^ (j + 1) ∧ {w : ZMod n | 2 * w = x} = {z, z + half n} ∧
          addOrderOf (z + half n) = 2 ^ (j + 1) :=
  Xia.Proofs.thm_3_1_step1_proved n e hne he

/-- Row 7b — Theorem 3.1 (s3_pow2.tex:10-15): `n = 2^e`, `e ≥ 3`, `ξ_0 ∈ F` of order `n`. The map
`y ↦ (ŷ(ξ_0), S, ŷ(1))` is a bijection from the solutions of the norm-free system onto
`{θ ∈ F : θ^{Q-1} = -1} × {1,-1} × {1,-1}`. -/
theorem thm_3_1_bij (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) :
    Set.BijOn (paramMap n ξ0) (NFSet n 2)
      ({θ | θ ^ (QQ n - 1) = -1} ×ˢ (({1, -1} : Set (GaloisField 3 (n / 2))) ×ˢ {1, -1})) :=
  Xia.Proofs.thm_3_1_bij_of n e hne he ξ0 hξ0
    (prop_2_4_bij n (Xia.Proofs.H4_even_of_pow2 hne he) (Xia.Proofs.H4_not3_of_pow2 hne) ξ0 hξ0) (thm_3_1_step1 n e hne he)

/-- Row 7c — Theorem 3.1 (s3_pow2.tex:11): the norm-free system has exactly `4(Q-1)` solutions `y ∈ F^n`. -/
theorem thm_3_1_card (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) : Nat.card (NFSet n 2) = 4 * (QQ n - 1) :=
  Xia.Proofs.thm_3_1_card_of n e hne he (thm_3_1_xi0 n e hne he)
    (fun ω hω => prop_2_4_bij n (Xia.Proofs.H4_even_of_pow2 hne he) (Xia.Proofs.H4_not3_of_pow2 hne) ω hω)
    (thm_3_1_step1 n e hne he) (thm_3_1_theta_set n e hne he)

/-- Coverage — s3_pow2.tex:5-6 and :71: for `e ≥ 3`, `n = 2^e` lies in Xia's range `n ≡ 8 (mod 24)` exactly when `e` is
odd. -/
theorem pow2_range (e : ℕ) (he : 3 ≤ e) : 2 ^ e % 24 = 8 ↔ Odd e :=
  Xia.Proofs.pow2_range_proved e he

/-- Row 8 — Corollary 3.2 (s3_pow2.tex:64-68): `n = 2^e`, `e ≥ 3` odd. Xia's system with `σ = 2` has a solution iff
some `θ` with `θ^{Q-1} = -1` and some signs `S`, `ŷ(1)` give `N(y_0) = N(y_1) = -1` for the `y` built from
`(θ, S, ŷ(1))` (the unique norm-free solution with these parameters, Theorem 3.1). -/
theorem cor_3_2 (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) :
    (XiaSet n 2).Nonempty ↔
      ∃ θ s1 h1 : GaloisField 3 (n / 2), θ ^ (QQ n - 1) = -1 ∧ (s1 = 1 ∨ s1 = -1) ∧ (h1 = 1 ∨ h1 = -1) ∧
        ∃ y ∈ NFSet n 2, paramMap n ξ0 y = (θ, s1, h1) ∧ Nm n (y 0) = -1 ∧ Nm n (y 1) = -1 :=
  Xia.Proofs.cor_3_2_proved n e hne he heo ξ0 hξ0

/-- Row 9 — Remark 3.3 (s3_pow2.tex:75-79): the translation `y_t ↦ y_{t+1}` maps the norm-free system to itself; in the
parameters of Theorem 3.1 it acts by `(θ, S, ŷ(1)) ↦ (ξ_0^{-1}θ, -S, ŷ(1))`, and it maps `y_0` to `y_1`. -/
theorem rem_3_3 (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2) :
    yTrans 1 y ∈ NFSet n 2 ∧ paramMap n ξ0 (yTrans 1 y) = (ξ0⁻¹ * dft ξ0 y 1, -S y, dft ξ0 y 0) ∧
      yTrans 1 y 0 = y 1 :=
  Xia.Proofs.rem_3_3_proved n e hne he ξ0 hξ0 y hy

/-! ## Section 3.2 — n = 2^e, e ≥ 4: the two norm conditions on the eigenspaces of T -/

/-- Coverage — s3_pow2.tex:84-95 (set-up of Section 3.2), `n = 2^e`, `e ≥ 4`: `Q = q^2`; `ι` has order 4 and
`ι^Q = ι`, `ι^9 = ι` (`ι ∈ F_9 ⊂ k_0`); `V` is closed under addition; the non-zero elements of `V` are exactly the
parameters `θ` of Theorem 3.1; `q ≡ 1 (mod 4)`, so `ι^q = ι`; (eq:qmodn) `q ≡ 1 + n/2 (mod n)`; for a parameter `θ`
and `ν := θ^{1+q}`: `ν^{q-1} = -1`, `ν^q = -ν`, `ν^Q = ν`; and `N(x) = (x^+)^2 - (x^-)^2` for `x ∈ F`. -/
theorem sec_3_2_setup (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 4 ≤ e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) :
    QQ n = qq n ^ 2 ∧ orderOf (iota n ξ0) = 4 ∧ iota n ξ0 ^ QQ n = iota n ξ0 ∧ iota n ξ0 ^ 9 = iota n ξ0 ∧
      (∀ x ∈ (Vsp n : Set (GaloisField 3 (n / 2))), ∀ x' ∈ (Vsp n : Set (GaloisField 3 (n / 2))), x + x' ∈ Vsp n) ∧
      (∀ θ : GaloisField 3 (n / 2), (θ ∈ Vsp n ∧ θ ≠ 0) ↔ θ ^ (QQ n - 1) = -1) ∧
      qq n % 4 = 1 ∧ iota n ξ0 ^ qq n = iota n ξ0 ∧ qq n % n = 1 + n / 2 ∧
      (∀ θ : GaloisField 3 (n / 2), θ ^ (QQ n - 1) = -1 →
        (θ ^ (1 + qq n)) ^ (qq n - 1) = -1 ∧ (θ ^ (1 + qq n)) ^ qq n = -θ ^ (1 + qq n) ∧
          (θ ^ (1 + qq n)) ^ QQ n = θ ^ (1 + qq n)) ∧
      ∀ x : GaloisField 3 (n / 2), Nm n x = yPlus n x ^ 2 - yMinus n x ^ 2 :=
  Xia.Proofs.sec_3_2_setup_proved n e hne he ξ0 hξ0

/-- Row 11a — Theorem 3.4(a) (s3_pow2.tex:106-107): `T(x) = ι x^q` is an `F_3`-linear involution of `V`; hence
`V = V_+ ⊕ V_-`, and each of `V_+`, `V_-` is a line over `F_q` (closed under `F_q`-scalars, `q` elements). -/
theorem thm_3_4_a (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 4 ≤ e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) :
    (∀ x ∈ Vsp n, Tmap n ξ0 x ∈ Vsp n ∧ Tmap n ξ0 (Tmap n ξ0 x) = x) ∧
      (∀ x x' : GaloisField 3 (n / 2), Tmap n ξ0 (x + x') = Tmap n ξ0 x + Tmap n ξ0 x') ∧
      (∀ x ∈ Vsp n, ∃! pm : GaloisField 3 (n / 2) × GaloisField 3 (n / 2),
        pm.1 ∈ Vplus n ξ0 ∧ pm.2 ∈ Vminus n ξ0 ∧ x = pm.1 + pm.2) ∧
      (∀ c : GaloisField 3 (n / 2), c ^ qq n = c →
        (∀ x ∈ Vplus n ξ0, c * x ∈ Vplus n ξ0) ∧ ∀ x ∈ Vminus n ξ0, c * x ∈ Vminus n ξ0) ∧
      Nat.card (Vplus n ξ0) = qq n ∧ Nat.card (Vminus n ξ0) = qq n :=
  Xia.Proofs.thm_3_4_a_proved n e hne he ξ0 hξ0

/-- Row 11b — Theorem 3.4(b) (s3_pow2.tex:108-111): for every solution, with `θ = ŷ(ξ_0)` and `ν = θ^{1+q}`,
`y_0^- = n^{-1} Λ_ν(θ + Tθ)` and `y_1^- = n^{-1} Λ'_ν(θ - Tθ)`. -/
theorem thm_3_4_b (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 4 ≤ e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2) :
    yMinus n (y 0) = (n : GaloisField 3 (n / 2))⁻¹ *
        Lam n ξ0 (dft ξ0 y 1 ^ (1 + qq n)) (dft ξ0 y 1 + Tmap n ξ0 (dft ξ0 y 1)) ∧
      yMinus n (y 1) = (n : GaloisField 3 (n / 2))⁻¹ *
        Lam' n ξ0 (dft ξ0 y 1 ^ (1 + qq n)) (dft ξ0 y 1 - Tmap n ξ0 (dft ξ0 y 1)) :=
  Xia.Proofs.thm_3_4_b_proved n e hne he ξ0 hξ0 y hy

/-- Row 11c — Theorem 3.4(c) (s3_pow2.tex:112-115) and its proof's identity (:175, :204): `θ^{1+q} = -ι θ T(θ)` for
every `θ ∈ V`, i.e. `θ_+^2 - θ_-^2 = ιν` with `θ_± = (θ ± Tθ)/2 ∈ V_±` (and `θ + Tθ = -θ_+`, `θ - Tθ = -θ_-`, :121);
`y_0^+`, `y_1^+` depend only on `(ν, S, ŷ(1))`; `y_0` only on `(ν, S, ŷ(1), θ_+)`, `y_1` only on `(ν, S, ŷ(1), θ_-)`;
`T` sends parameters to parameters and keeps `ν`; `y_0(Tθ) = y_0(θ)` and `y_1(Tθ) = \overline{y_1(θ)}` (same signs). -/
theorem thm_3_4_c (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 4 ≤ e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) :
    let T := Tmap n ξ0
    let θ : (ZMod n → GaloisField 3 (n / 2)) → GaloisField 3 (n / 2) := fun y => dft ξ0 y 1
    (∀ x ∈ Vsp n, x ^ (1 + qq n) = -iota n ξ0 * x * T x ∧
      ((x + T x) / 2) ^ 2 - ((x - T x) / 2) ^ 2 = iota n ξ0 * x ^ (1 + qq n) ∧
      (x + T x) / 2 ∈ Vplus n ξ0 ∧ (x - T x) / 2 ∈ Vminus n ξ0 ∧
      x + T x = -((x + T x) / 2) ∧ x - T x = -((x - T x) / 2)) ∧
    (∀ y ∈ NFSet n 2, ∀ y' ∈ NFSet n 2, θ y ^ (1 + qq n) = θ y' ^ (1 + qq n) → S y = S y' →
      dft ξ0 y 0 = dft ξ0 y' 0 →
        yPlus n (y 0) = yPlus n (y' 0) ∧ yPlus n (y 1) = yPlus n (y' 1) ∧
        ((θ y + T (θ y)) / 2 = (θ y' + T (θ y')) / 2 → y 0 = y' 0) ∧
        ((θ y - T (θ y)) / 2 = (θ y' - T (θ y')) / 2 → y 1 = y' 1)) ∧
    (∀ x : GaloisField 3 (n / 2), x ^ (QQ n - 1) = -1 →
      T x ^ (QQ n - 1) = -1 ∧ T x ^ (1 + qq n) = x ^ (1 + qq n)) ∧
    (∀ y ∈ NFSet n 2, ∀ y' ∈ NFSet n 2, paramMap n ξ0 y' = (T (θ y), S y, dft ξ0 y 0) →
      y' 0 = y 0 ∧ y' 1 = bar n (y 1)) :=
  Xia.Proofs.thm_3_4_c_proved n e hne he ξ0 hξ0

/-- Row 11d — Theorem 3.4(d) (s3_pow2.tex:116-117): for every `ν ∈ k_0` with `ν^{q-1} = -1`, `Λ_ν` is injective on
`V_+` and `Λ'_ν` on `V_-`; hence `x ↦ n^{-1}Λ_ν(x + Tx)` on `V` has kernel exactly `V_-`. -/
theorem thm_3_4_d (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 4 ≤ e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) (ν : GaloisField 3 (n / 2)) (hνk : ν ^ QQ n = ν) (hν : ν ^ (qq n - 1) = -1) :
    Set.InjOn (Lam n ξ0 ν) (Vplus n ξ0) ∧ Set.InjOn (Lam' n ξ0 ν) (Vminus n ξ0) ∧
      ∀ x ∈ Vsp n, ((n : GaloisField 3 (n / 2))⁻¹ * Lam n ξ0 ν (x + Tmap n ξ0 x) = 0 ↔ x ∈ Vminus n ξ0) :=
  Xia.Proofs.thm_3_4_d_proved n e hne he ξ0 hξ0 ν hνk hν

/-- Row 12a — Corollary 3.5(i) (s3_pow2.tex:127-132): `n = 2^e`, `e ≥ 5` odd. Xia's system with `σ = 2` has a solution
iff there are `ν` with `ν^{q-1} = -1`, signs `S`, `ŷ(1)`, and `(θ_+, θ_-) ∈ V_+ × V_-` on the conic
`θ_+^2 - θ_-^2 = ιν` with `N(y_0^+ + n^{-1}Λ_ν(-θ_+)) = -1` and `N(y_1^+ + n^{-1}Λ'_ν(-θ_-)) = -1`, where `y_0^+, y_1^+`
are the values determined by `(ν, S, ŷ(1))` (those of any norm-free solution with these data). -/
theorem cor_3_5_i (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 5 ≤ e) (heo : Odd e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) :
    (XiaSet n 2).Nonempty ↔
      ∃ ν s1 h1 θp θm : GaloisField 3 (n / 2), ν ^ (qq n - 1) = -1 ∧ (s1 = 1 ∨ s1 = -1) ∧ (h1 = 1 ∨ h1 = -1) ∧
        θp ∈ Vplus n ξ0 ∧ θm ∈ Vminus n ξ0 ∧ θp ^ 2 - θm ^ 2 = iota n ξ0 * ν ∧
        ∃ y ∈ NFSet n 2, dft ξ0 y 1 ^ (1 + qq n) = ν ∧ S y = s1 ∧ dft ξ0 y 0 = h1 ∧
          Nm n (yPlus n (y 0) + (n : GaloisField 3 (n / 2))⁻¹ * Lam n ξ0 ν (-θp)) = -1 ∧
          Nm n (yPlus n (y 1) + (n : GaloisField 3 (n / 2))⁻¹ * Lam' n ξ0 ν (-θm)) = -1 :=
  Xia.Proofs.cor_3_5_i_proved n e hne he heo ξ0 hξ0

/-- Row 12b — Corollary 3.5(ii) (s3_pow2.tex:133-135): above each triple `(ν, S, ŷ(1))` Xia's system (`σ = 2`) has at
most 4 solutions; if it has any, they are the orbit `{±θ_+ ± θ_-}` of `⟨T, θ ↦ -θ⟩` (so 0, 2 or 4 of them); in total
at most `16(q-1) = 16(3^{n/8}-1)` solutions. -/
theorem cor_3_5_ii (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 5 ≤ e) (heo : Odd e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) :
    let above : GaloisField 3 (n / 2) → GaloisField 3 (n / 2) → GaloisField 3 (n / 2) →
        Set (ZMod n → GaloisField 3 (n / 2)) := fun ν s1 h1 =>
      {y | y ∈ XiaSet n 2 ∧ dft ξ0 y 1 ^ (1 + qq n) = ν ∧ S y = s1 ∧ dft ξ0 y 0 = h1}
    (∀ ν s1 h1, (above ν s1 h1).ncard ≤ 4 ∧ (above ν s1 h1).ncard ∈ ({0, 2, 4} : Set ℕ) ∧
      ∀ y ∈ above ν s1 h1, ∀ y' ∈ NFSet n 2,
        (y' ∈ above ν s1 h1 ↔ paramMap n ξ0 y' ∈ ({dft ξ0 y 1, -dft ξ0 y 1, Tmap n ξ0 (dft ξ0 y 1),
          -Tmap n ξ0 (dft ξ0 y 1)} : Set _) ×ˢ ({s1} ×ˢ {h1}))) ∧
      Nat.card (XiaSet n 2) ≤ 16 * (qq n - 1) :=
  Xia.Proofs.cor_3_5_ii_proved n e hne he heo ξ0 hξ0

/-- Row 13 — Remark 3.6(a),(b) (s3_pow2.tex:216-219): (a) `T(ξ_0^{-1}θ) = -ξ_0^{-1}Tθ` for `θ ∈ V`, so
`θ ↦ ξ_0^{-1}θ` maps `V_-` onto `V_+` (`e ≥ 4`); (b) for `n = 8`: `q = 3 ≢ 5 (mod 8)` and `T^2 = -1` on `V`. -/
theorem rem_3_6 :
    (∀ (n e : ℕ) [NeZero n], n = 2 ^ e → 4 ≤ e → ∀ ξ0 : GaloisField 3 (n / 2), IsPrimitiveRoot ξ0 n →
      (∀ θ ∈ Vsp n, Tmap n ξ0 (ξ0⁻¹ * θ) = -(ξ0⁻¹ * Tmap n ξ0 θ)) ∧
      Set.BijOn (fun θ => ξ0⁻¹ * θ) (Vminus n ξ0) (Vplus n ξ0)) ∧
    (qq 8 = 3 ∧ qq 8 % 8 ≠ 5 ∧ ∀ ξ0 : GaloisField 3 (8 / 2), IsPrimitiveRoot ξ0 8 →
      ∀ x ∈ Vsp 8, Tmap 8 ξ0 (Tmap 8 ξ0 x) = -x) :=
  Xia.Proofs.rem_3_6_proved

/-! ## Section 4 — the norm-free system for every n (n = 2^a n_odd, a ≥ 3, n_odd odd, 3 ∤ n) -/

/-- Row 14a — Theorem 4.1 (s4_normfree.tex:15-16): the orbits of `ξ ↦ ξ^3` on `𝓛_a` come in pairs `{O, O^{-1}}` with
`O ≠ O^{-1}` and `|O| = |O^{-1}|`, and `∑_{i ∈ I} L_i = n/4`. -/
theorem thm_4_1_pairs (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n) :
    (∀ O ∈ topOrbits n 3, inv O ∈ topOrbits n 3 ∧ inv O ≠ O ∧ (inv O).card = O.card) ∧
      ∑ P ∈ topPairs n 3, pairLen P = n / 4 :=
  Xia.Proofs.thm_4_1_pairs_proved n a nodd hn ha hodd h3

/-- Row 14e — proof of Theorem 4.1, Step 2 (s4_normfree.tex:79-83), algebraically closed `L` of characteristic 3: the top
data `𝒟` ((F1) along each top orbit with its wrap, (F3) from `O` to `O^{-1}`) number `∏_i (3^{L_i}-1)`; so do the homogeneous
top data `𝒟^0`, which form a group under pointwise multiplication. -/
theorem thm_4_1_step2 (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type*} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (hω : IsPrimitiveRoot ω n) :
    Nat.card (topData n 3 2 (1 : L) ω) = pairProd n 3 ∧ Nat.card (topData0 n 3 : Set (ZMod n → L)) = pairProd n 3 ∧
      (1 : ZMod n → L) ∈ (topData0 n 3 : Set (ZMod n → L)) ∧
      ∀ l1 ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ l2 ∈ (topData0 n 3 : Set (ZMod n → L)),
        l1 * l2 ∈ (topData0 n 3 : Set (ZMod n → L)) ∧ l1⁻¹ ∈ (topData0 n 3 : Set (ZMod n → L)) :=
  Xia.Proofs.thm_4_1_step2_proved n a nodd hn ha hodd h3 ω hω

/-- Row 14f — proof of Theorem 4.1, Step 4 (s4_normfree.tex:97-107), layer 0: for a solution, with `f := ŷ|_{μ_{n_odd}}` and
`P(α) := S ŷ(-α)`: `P(α) = ∏_{ρ ∈ 𝓛_a, ρ^{2^{a-1}} = -α} ŷ(ρ)` (so `P` does not depend on `S`) and (E1) `f(α^2) = P(α)f(α)`
for every `α ∈ μ_{n_odd}`; `P(1) = 1`, `f(1) = ±1`; on `μ_{n_odd} ∖ {1}`: (E2) `f(α^3) = α^6 f(α)^3`, (E3)
`f(α)f(α^{-1}) = α^m`, and `P(α^3) = α^6 P(α)^3`, `P(α)P(α^{-1}) = α^m`. -/
theorem thm_4_1_step4 (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2) :
    (∀ k : ZMod n, 2 ^ a ∣ k.val →
      algebraMap _ L (S y) * dftA ω y (k + half n) =
          ∏ ρ ∈ (topLayer n).filter (fun ρ => (2 ^ (a - 1) : ZMod n) * ρ = k + half n), dftA ω y ρ ∧
        dftA ω y (2 * k) = algebraMap _ L (S y) * dftA ω y (k + half n) * dftA ω y k) ∧
    algebraMap _ L (S y) * dftA ω y (half n) = 1 ∧ (dftA ω y 0 = 1 ∨ dftA ω y 0 = -1) ∧
    ∀ k ∈ layer0' n a,
      dftA ω y (3 * k) = (ω ^ k.val) ^ 6 * dftA ω y k ^ 3 ∧ dftA ω y k * dftA ω y (-k) = (ω ^ k.val) ^ (n / 2) ∧
      algebraMap _ L (S y) * dftA ω y (3 * k + half n) =
        (ω ^ k.val) ^ 6 * (algebraMap _ L (S y) * dftA ω y (k + half n)) ^ 3 ∧
      (algebraMap _ L (S y) * dftA ω y (k + half n)) * (algebraMap _ L (S y) * dftA ω y (-k + half n)) =
        (ω ^ k.val) ^ (n / 2) :=
  Xia.Proofs.thm_4_1_step4_of n a nodd hn ha hodd h3 ω hω y hy
    (prop_2_4_F1 n (Xia.Proofs.H9_even_halves hn (by omega)).1 h3 ω hω y) (prop_2_4_F3 n (Xia.Proofs.H9_even_halves hn (by omega)).1 h3 ω hω y)
    (prop_2_4_F4 n (Xia.Proofs.H9_even_halves hn (by omega)).1 h3 ω hω y)

/-- Row 14g — proof of Theorem 4.1, Step 5 (s4_normfree.tex:109-121), algebraically closed `L` of characteristic 3: `G` is a
finite group under pointwise multiplication, `τ` is an automorphism of it; `G'` (= `G''` for `r = 3`) is a `G`-torsor and is
non-empty; `f ↦ τf/f` maps `G'` into `G''`; for `P ∈ G''` and `f_0 ∈ G'`, the `f ∈ G'` with (E1) `f(α^2) = P(α)f(α)` exist iff
`P ∈ G''_0 := (τf_0/f_0)(τ-1)G`, and then there are exactly `|G^τ|` of them (a `G^τ`-torsor). -/
theorem thm_4_1_step5 (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type*} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (hω : IsPrimitiveRoot ω n) :
    let G : Set (ZMod n → L) := Ggrp n a 3
    let G' : Set (ZMod n → L) := Gprime n a 3 2 1 ω
    let τ : (ZMod n → L) → ZMod n → L := tauG n a
    (G.Finite ∧ (1 : ZMod n → L) ∈ G ∧ (∀ g ∈ G, ∀ g' ∈ G, g * g' ∈ G ∧ g⁻¹ ∈ G) ∧ Set.BijOn τ G G ∧
      ∀ g ∈ G, ∀ g' ∈ G, τ (g * g') = τ g * τ g') ∧
    G'.Nonempty ∧ (∀ f ∈ G', ∀ f' ∈ G', f' / f ∈ G) ∧ (∀ g ∈ G, ∀ f ∈ G', g * f ∈ G') ∧
    (∀ f ∈ G', τ f / f ∈ G') ∧
    ∀ P ∈ G', ∀ f0 ∈ G',
      ((∃ f ∈ G', ∀ k ∈ layer0' n a, f (2 * k) = P k * f k) ↔ ∃ g ∈ G, P = τ f0 / f0 * (τ g / g)) ∧
      ((∃ f ∈ G', ∀ k ∈ layer0' n a, f (2 * k) = P k * f k) →
        Nat.card {f : ZMod n → L // f ∈ G' ∧ ∀ k ∈ layer0' n a, f (2 * k) = P k * f k} =
          Nat.card {g : ZMod n → L // g ∈ G ∧ τ g = g}) :=
  Xia.Proofs.thm_4_1_step5_proved n a nodd hn ha hodd h3 ω hω

/-- Row 14h — proof of Theorem 4.1, Step 6 (s4_normfree.tex:123-139): `Π : 𝒟^0 → G`, `λ ↦ P_λ`, is a homomorphism onto `G`. -/
theorem thm_4_1_step6 (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type*} [Field L] [CharP L 3] [IsAlgClosed L] :
    (∀ lam ∈ (topData0 n 3 : Set (ZMod n → L)), Pmap n a lam ∈ (Ggrp n a 3 : Set (ZMod n → L))) ∧
    (∀ l1 ∈ (topData0 n 3 : Set (ZMod n → L)), ∀ l2 ∈ (topData0 n 3 : Set (ZMod n → L)),
      Pmap n a (l1 * l2) = Pmap n a l1 * Pmap n a l2) ∧
    Set.SurjOn (Pmap n a) (topData0 n 3 : Set (ZMod n → L)) (Ggrp n a 3) :=
  Xia.Proofs.thm_4_1_step6_proved n a nodd hn ha hodd h3

/-- Row 14i — proof of Theorem 4.1, Step 7 (s4_normfree.tex:141-146): `|(τ-1)G| · |G^τ| = |G|`, and
`|K_n| = 4 ∏_i (3^{L_i}-1)` for the group `K_n` of solutions of (h1), (h3), (h4) (algebraically closed `L`, char 3). -/
theorem thm_4_1_step7 (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type*} [Field L] [CharP L 3] [IsAlgClosed L] :
    Nat.card ((fun g => tauG n a g / g) '' (Ggrp n a 3 : Set (ZMod n → L))) *
        Nat.card {g : ZMod n → L // g ∈ (Ggrp n a 3 : Set (ZMod n → L)) ∧ tauG n a g = g} =
      Nat.card (Ggrp n a 3 : Set (ZMod n → L)) ∧
    Nat.card {lam : ZMod n → L // (∀ k, lam (3 * k) = lam k ^ 3) ∧ (∀ k, lam k * lam (-k) = 1) ∧
      ∀ k, lam k * lam (k + half n) = lam (half n) * lam (2 * k)} = 4 * pairProd n 3 :=
  (Xia.Proofs.L10_exists_prim_algclosed n h3 (L := L)).elim fun ω hω =>
    Xia.Proofs.thm_4_1_step7_of n a nodd hn ha hodd h3 ω hω (thm_4_1_step2 n a nodd hn ha hodd h3 ω hω)
      (thm_4_1_step6 n a nodd hn ha hodd h3)

/-- Row 14b — Theorem 4.1 (s4_normfree.tex:16-21): `|NF(n)| = 4 ∏_{i ∈ I} (3^{L_i} - 1)`; in particular `NF(n)` is not
empty, and `|NF(n)| = 4 Q ∏_i (1 - 3^{-L_i})` with `Q = 3^{n/4}`. -/
theorem thm_4_1_count (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n) :
    Nat.card (NFSet n 2) = 4 * pairProd n 3 ∧ (NFSet n 2).Nonempty ∧
      (Nat.card (NFSet n 2) : ℚ) = 4 * 3 ^ (n / 4) * ∏ P ∈ topPairs n 3, (1 - (3 : ℚ) ^ (-(pairLen P : ℤ))) :=
  Xia.Proofs.thm_4_1_count_of_steps n a nodd hn ha hodd h3 (thm_4_1_step2 n a nodd hn ha hodd h3)
    (thm_4_1_step5 n a nodd hn ha hodd h3) (thm_4_1_step6 n a nodd hn ha hodd h3) (thm_4_1_step7 n a nodd hn ha hodd h3)

/-- Coverage — s4_normfree.tex:24: for `n = 2^e` there is one pair, `L_1 = n/4`. -/
theorem thm_4_1_pow2 (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) :
    (topPairs n 3).card = 1 ∧ ∀ P ∈ topPairs n 3, pairLen P = n / 4 :=
  Xia.Proofs.thm_4_1_pow2_proved n e hne he

/-- Row 15 — Corollary 4.2 (s4_normfree.tex:26-29): for `n ≡ 8 (mod 24)`, Xia's system with `σ = 2` has a solution iff
some point of `NF(n)` has `N(y_0) = N(y_1) = -1`; and `NF(n)` is not empty (so a proof of no solution must use (L2)
beyond `R(m) = 1`). -/
theorem cor_4_2 (n : ℕ) [NeZero n] (hn : n % 24 = 8) :
    ((XiaSet n 2).Nonempty ↔ ∃ y ∈ NFSet n 2, Nm n (y 0) = -1 ∧ Nm n (y 1) = -1) ∧ (NFSet n 2).Nonempty :=
  Xia.Proofs.cor_4_2_of n hn (fun a nodd h1 h2 h4 h5 => thm_4_1_count n a nodd h1 h2 h4 h5)

/-- Row 16a — Proposition 4.3, even part (s4_normfree.tex:148-150): for an even divisor `σ` of `n`, the norm-free
system with shift `σ` has exactly `4 ∏_i (3^{L_i} - 1)` solutions. -/
theorem prop_4_3_even (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    (σ : ℕ) (hσ : σ ∣ n) (hσe : Even σ) : Nat.card (NFSet n σ) = 4 * pairProd n 3 :=
  Xia.Proofs.prop_4_3_even_of n a nodd hn ha hodd h3 σ hσ hσe (thm_4_1_step2 n a nodd hn ha hodd h3)
    (thm_4_1_step5 n a nodd hn ha hodd h3) (thm_4_1_step6 n a nodd hn ha hodd h3) (thm_4_1_step7 n a nodd hn ha hodd h3)

/-- Row 16b — Proposition 4.3, odd part (s4_normfree.tex:150, proof :163-164): for an odd divisor `σ` of `n`, the
norm-free system with shift `σ` has no solution (the set is EMPTY). -/
theorem prop_4_3_odd (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    (σ : ℕ) (hσ : σ ∣ n) (hσo : Odd σ) : NFSet n σ = ∅ :=
  Xia.Proofs.prop_4_3_odd_proved n a nodd hn ha hodd h3 σ hσ hσo

/-! ## Section 5 — the two norm conditions for every n -/

/-- Row 18a — Theorem 5.1(a) (s5_twonorms.tex:55-57): `y ↦ y^{(u)}`, `u = 1 + m`, is an involution of `NF(n)` and of
the solution set of (1) with `σ = 2`; it keeps `S` and `ŷ` on `μ_m`, satisfies `\widehat{y^{(u)}}(ξ) = ŷ(-ξ)` on `𝓛_a`,
keeps `y_0`, and sends `y_1` to `\overline{y_1}`. -/
theorem thm_5_1_a (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) :
    (∀ y : ZMod n → GaloisField 3 (n / 2), ySubst (ySubst y) = y) ∧
      (∀ y ∈ XiaSet n 2, ySubst y ∈ XiaSet n 2) ∧
      ∀ y ∈ NFSet n 2, ySubst y ∈ NFSet n 2 ∧ S (ySubst y) = S y ∧
        (∀ k : ZMod n, Even k.val → dftA ω (ySubst y) k = dftA ω y k) ∧
        (∀ k : ZMod n, Odd k.val → dftA ω (ySubst y) k = dftA ω y (k + half n)) ∧
        ySubst y 0 = y 0 ∧ ySubst y 1 = bar n (y 1) :=
  Xia.Proofs.thm_5_1_a_proved n a nodd hn ha hodd h3 ω hω

/-- Row 18b — Theorem 5.1(b) (s5_twonorms.tex:58): for `a ≥ 4` only cases A and C occur; for `a = 3` only B and C. -/
theorem thm_5_1_b (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n) :
    ∀ O ∈ topOrbits n 3, (4 ≤ a → ¬ IsCaseB O) ∧ (a = 3 → ¬ IsCaseA O) :=
  Xia.Proofs.thm_5_1_b_proved n a nodd hn ha hodd h3

/-- Row 18c (counting part) — Theorem 5.1(c) (s5_twonorms.tex:61-67) with the identification of fibres
(:74-77, P10s_main.tex:183-184): every non-empty fibre has `Φ` elements, and there are
`|NF(n)|/Φ = 4 ∏_𝒜 (q_O-1) ∏_ℬ (q_O+1) ∏_𝒞 (3^L-1)` non-empty fibres. -/
theorem thm_5_1_c_count (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) :
    (∀ y ∈ NFSet n 2, Nat.card (fibre ω y) = fibreSize n) ∧
      Nat.card (lowerData ω '' NFSet n 2) = 4 * fibreProd n ∧
      Nat.card (NFSet n 2) = fibreSize n * (4 * fibreProd n) :=
  Xia.Proofs.thm_5_1_c_count_of n a nodd hn ha hodd h3 ω hω (thm_4_1_count n a nodd hn ha hodd h3)

/-- Row 19 (counting part) — Corollary 5.2 (s5_twonorms.tex:79-86): for `n ≡ 8 (mod 24)`, each fibre contains at most 4
solutions of (1) with `σ = 2` (0, 2 or 4); if it contains any, they form one orbit of `⟨T, v ↦ -v⟩` — on solutions
`T` is `y ↦ y^{(u)}` (Thm 5.1(c)) and `v ↦ -v` negates the top data, which is `y ↦ ȳ = (y_{t+m})_t`; Xia's system has at
most `16 ∏_𝒜 (q_O-1) ∏_ℬ (q_O+1) ∏_𝒞 (3^L-1) ≤ 16 (4/3)^b 3^{n/8}` solutions, `b = |ℬ|`. -/
theorem cor_5_2 (n : ℕ) [NeZero n] (hn : n % 24 = 8) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L]
    (ω : L) (hω : IsPrimitiveRoot ω n) :
    (∀ y ∈ NFSet n 2, (fibre ω y ∩ XiaSet n 2).ncard ∈ ({0, 2, 4} : Set ℕ) ∧
      ∀ y' ∈ fibre ω y ∩ XiaSet n 2,
        fibre ω y ∩ XiaSet n 2 = ({y', ySubst y', yTrans (half n) y', ySubst (yTrans (half n) y')} : Set _)) ∧
      Nat.card (XiaSet n 2) ≤ 16 * fibreProd n ∧
      (16 * fibreProd n : ℝ) ≤ 16 * (4 / 3 : ℝ) ^ (blocksB n).card * 3 ^ (n / 8) :=
  Xia.Proofs.cor_5_2_of n hn ω hω
    (fun ω' hω' hnL z => Xia.Paper.fourier_inversion n (Xia.Proofs.H19_even_of24 hn) ω' hω' hnL z)
    (fun a nodd hn' ha hodd h3 => Xia.Paper.thm_5_1_c_count n a nodd hn' ha hodd h3 ω hω)

/-! ## Section 6 — other characteristics -/

/-- Row 20a — s6_primes.tex:14-15 and the arithmetic of Proposition 6.1's proof (:36, :40): for `n = 2^e`, `e ≥ 3`
odd: `n ≡ 2` or `3 (mod 5)`, `n^2 ≡ -1`, `n^4 ≡ 1`, `p ≡ n (mod 5)`, so `p ≡ 2` or `3`, `5 ∤ pn`, `(p/5) = -1`; and
`1 + (n-1)p = n^3`. -/
theorem sec_6_1_arith (n e : ℕ) (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) :
    (n % 5 = 2 ∨ n % 5 = 3) ∧ (n ^ 2 : ZMod 5) = -1 ∧ (n ^ 4 : ZMod 5) = 1 ∧ pp n % 5 = n % 5 ∧
      ¬ 5 ∣ pp n * n ∧ legendreSym 5 (pp n : ℤ) = -1 ∧ 1 + (n - 1) * pp n = n ^ 3 :=
  Xia.Proofs.sec_6_1_arith_proved n e hne he heo

/-- Coverage — s6_primes.tex:44-49: for any even `n` and `y` over a commutative ring: `R(-s) = R(s)`; (L3_5) gives
`R(s) = n(1-p)` for `s ≢ m`; (L2_5) gives `R(m) = n^4`; and for `n = 2^e`, `e ≥ 3` odd: `κ = n^2 p = -p` is a non-square
of `F_5` and `κ^2 = -1`. -/
theorem sec_6_1_R_kappa (n : ℕ) [NeZero n] (hn : Even n) {K : Type*} [CommRing K] (y : ZMod n → K) :
    (L3 ((n : K) * (1 - (pp n : K))) y → ∀ s, s ≠ half n → R y s = (n : K) * (1 - (pp n : K))) ∧
      (L2 ((n : K) ^ 3) y → R y (half n) = (n : K) ^ 4) ∧
      ∀ e : ℕ, n = 2 ^ e → 3 ≤ e → Odd e →
        kappa n (ZMod 5) = -(pp n : ZMod 5) ∧ ¬ IsSquare (kappa n (ZMod 5)) ∧ kappa n (ZMod 5) ^ 2 = -1 :=
  Xia.Proofs.sec_6_1_R_kappa_proved n hn y

/-- Coverage — s6_primes.tex:51-62 (Fourier form for `r = 5`): `n = 2^e`, `e ≥ 3` odd, `L ⊇ F_{5^n}` with a primitive
`n`-th root `ω`: `y ↦ ŷ` is a bijection from the norm-free system in characteristic `5` onto the functions with (F1_5), (F3_5), (F4_5);
the iterate `ŷ(ξ^{5^j}) = ξ^{j5^j} ŷ(ξ)^{5^j}` holds; and `S = ŷ(-1)`. -/
theorem sec_6_2_fourier (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) {L : Type*} [Field L]
    [Algebra (GaloisField 5 n) L] (ω : L) (hω : IsPrimitiveRoot ω n) :
    Set.BijOn (dftA ω) (NF5Set n) {h | F1 5 1 ω h ∧ F3r (kappa n L) ω h ∧ F4 h} ∧
      ∀ y ∈ NF5Set n, (∀ (j : ℕ) (k : ZMod n),
        dftA ω y ((5 : ZMod n) ^ j * k) = (ω ^ k.val) ^ (j * 5 ^ j) * dftA ω y k ^ (5 ^ j)) ∧
        dftA ω y (half n) = algebraMap _ L (S y) :=
  Xia.Proofs.H20_sec_6_2_fourier n e hne he heo ω hω

/-- Row 21 — Theorem 6.2 (s6_primes.tex:65-69) with :72-74: `n = 2^e`, `e ≥ 3` odd, `Q_5 = 5^{n/4}`, `ξ_0 ∈ F_{5^n}` of
order `n`, `ι_5 = ξ_0^{n/4}`: `y ↦ (ŷ(ξ_0), S, ŷ(1))` is a bijection from the norm-free system in characteristic `5` onto
`{θ' : θ'^{Q_5-1} = -ι_5} × {S : S^2 = κ} × {n, -n}`; it has exactly `4(Q_5-1)` solutions; the first set has
`Q_5 - 1` elements and the second lies in `F_25` (two elements). Also `F_{5^n}` contains such a `ξ_0`. -/
theorem thm_6_2 (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) :
    (∃ ξ0 : GaloisField 5 n, IsPrimitiveRoot ξ0 n) ∧
    ∀ ξ0 : GaloisField 5 n, IsPrimitiveRoot ξ0 n →
      Set.BijOn (paramMap n ξ0) (NF5Set n)
        ({θ | θ ^ (5 ^ (n / 4) - 1) = -ξ0 ^ (n / 4)} ×ˢ ({s | s ^ 2 = kappa n _} ×ˢ {(n : GaloisField 5 n), -(n : GaloisField 5 n)})) ∧
      Nat.card (NF5Set n) = 4 * (5 ^ (n / 4) - 1) ∧
      Nat.card {θ : GaloisField 5 n // θ ^ (5 ^ (n / 4) - 1) = -ξ0 ^ (n / 4)} = 5 ^ (n / 4) - 1 ∧
      Nat.card {s : GaloisField 5 n // s ^ 2 = kappa n _} = 2 ∧
      ∀ s : GaloisField 5 n, s ^ 2 = kappa n _ → s ^ 25 = s :=
  Xia.Proofs.thm_6_2_proved n e hne he heo

/-- Row 22 — Corollary 6.3 (s6_primes.tex:107-108): `y` satisfies (eq:xia125) iff it solves the norm-free `r = 5`
system and `N_5(y_0) = n^3`, `N_5(x) := x^{1+5^{n/2}}`. -/
theorem cor_6_3 (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) (y : ZMod n → GaloisField 5 n) :
    y ∈ Xia5Set n ↔ y ∈ NF5Set n ∧ Nm5 n (y 0) = (n : GaloisField 5 n) ^ 3 :=
  Xia.Proofs.cor_6_3_proved n e hne he heo y

/-- Coverage — s6_primes.tex:132-136 (Fourier form, every `r`): `n = 2^a n_odd`, `a ≥ 3`, `r` prime, `r ∤ pn`, any
integer `σ_r`: `y ↦ ŷ` is a bijection from the norm-free system in characteristic `r` onto the functions with (F1_r), (F3_r), (F4_r), and
(F3_r) at `-1` gives `S^2 = κ`. -/
theorem sec_6_3_fourier (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a)
    (hodd : Odd nodd) (hr : ¬ r ∣ pp n * n) (σr : ℤ) {L : Type*} [Field L]
    [Algebra (GaloisField r (n / Int.gcd σr n)) L] (ω : L) (hω : IsPrimitiveRoot ω n) :
    Set.BijOn (dftA ω) (NFrSet n r σr) {h | F1 r σr ω h ∧ F3r (kappa n L) ω h ∧ F4 h} ∧
      ∀ y ∈ NFrSet n r σr, S y ^ 2 = kappa n _ :=
  Xia.Proofs.sec_6_3_fourier_proved n a nodd r hn ha hodd hr σr ω hω

/-- Row 24(pairs) — Theorem 6.4 = Theorem C (s6_primes.tex:138-146; P10s_main.tex:216-222): `n = 2^a n_odd`, `a ≥ 3`
(`3 ∣ n` allowed), `r` prime, `r ∤ pn`, `r ≢ -1 (mod 2^a)`, `σ_r` ANY integer. The orbits of `ξ ↦ ξ^r` on `𝓛_a` come in
pairs `{O, O^{-1}}`, `O ≠ O^{-1}`, with `∑ L_i = n/4` [here; (i), (ii) are the next rows; `(-1)^{σ.natAbs} = (-1)^σ`
since `|σ|` and `σ` have the same parity]; (i) if `(-1)^{σ_r} ≠ (p/r)` the norm-free system in characteristic `r` has no
solution (EMPTY); (ii) if `(-1)^{σ_r} = (p/r)` it has exactly `4 ∏_i (r^{L_i} - 1)` solutions. -/
theorem thm_6_4_pairs (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a)
    (hodd : Odd nodd) (hr : ¬ r ∣ pp n * n) (hr1 : r % 2 ^ a ≠ 2 ^ a - 1) :
    (∀ O ∈ topOrbits n r, inv O ∈ topOrbits n r ∧ inv O ≠ O ∧ (inv O).card = O.card) ∧
      ∑ P ∈ topPairs n r, pairLen P = n / 4 :=
  Xia.Proofs.thm_6_4_pairs_proved n a nodd r hn ha hodd hr hr1

/-- Row 24(i) — Theorem 6.4(i) (s6_primes.tex:143): if `(-1)^{σ_r} ≠ (p/r)`, the norm-free system in characteristic `r` has no solution
(EMPTY). (Hypotheses as in row 24; `r ≢ -1` is not needed for (i), but it is the theorem's hypothesis.) -/
theorem thm_6_4_i (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (hr : ¬ r ∣ pp n * n) (hr1 : r % 2 ^ a ≠ 2 ^ a - 1) (σr : ℤ)
    (hsign : (-1 : ℤ) ^ σr.natAbs ≠ legendreSym r (pp n : ℤ)) : NFrSet n r σr = ∅ :=
  Xia.Proofs.thm_6_4_i_proved n a nodd r hn ha hodd hr hr1 σr hsign

/-- Row 24a — proof of Theorem 6.4, Step 2 (s6_primes.tex:166-167), algebraically closed `L` of characteristic `r`: the top data
for `r` ((F1_r) along the orbits with the wrap, (F3_r) between `O` and `O^{-1}`) number `∏_i (r^{L_i}-1)`; so do the homogeneous
top data. -/
theorem thm_6_4_step2 (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a)
    (hodd : Odd nodd) (hr : ¬ r ∣ pp n * n) (hr1 : r % 2 ^ a ≠ 2 ^ a - 1) (σr : ℤ) {L : Type*} [Field L] [CharP L r]
    [IsAlgClosed L] (ω : L) (hω : IsPrimitiveRoot ω n) :
    Nat.card (topData n r σr (kappa n L) ω) = pairProd n r ∧
      Nat.card (topData0 n r : Set (ZMod n → L)) = pairProd n r :=
  Xia.Proofs.thm_6_4_step2_proved n a nodd r hn ha hodd hr hr1 σr ω hω

/-- Row 24b — proof of Theorem 6.4, Step 3 (s6_primes.tex:169-175): with `S^2 = κ`, one layer down (F1_r) becomes
`ŷ(ξ^r) = (-1)^{σ_r} S^{r-1} ξ^{rσ_r} ŷ(ξ)^r` for `ŷ(η^2) := S^{-1}ŷ(η)ŷ(-η)`, and `S^{r-1} = (κ/r) = (p/r)` (Euler's criterion),
so the descent closes iff `(-1)^{σ_r} = (p/r)`; (F3_r) passes down: `(S^{-1}ŷ(η)ŷ(-η))(S^{-1}ŷ(η^{-1})ŷ(-η^{-1})) = κ η^{2m}`. -/
theorem thm_6_4_step3 (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a)
    (hodd : Odd nodd) (hr : ¬ r ∣ pp n * n) (σr : ℤ) {L : Type*} [Field L] [CharP L r] (ω : L)
    (hω : IsPrimitiveRoot ω n) (h : ZMod n → L) (s0 : L) (hs : s0 ^ 2 = kappa n L) (x : ZMod n)
    (hF1 : ∀ z ∈ ({x, x + half n} : Set (ZMod n)), h ((r : ZMod n) * z) = (ω ^ z.val) ^ ((r : ℤ) * σr) * h z ^ r)
    (hF3 : ∀ z ∈ ({x, x + half n} : Set (ZMod n)), h z * h (-z) = kappa n L * (ω ^ z.val) ^ (n / 2)) :
    s0⁻¹ * h ((r : ZMod n) * x) * h ((r : ZMod n) * x + half n) =
        (-1) ^ σr.natAbs * s0 ^ (r - 1) * (ω ^ (2 * x).val) ^ ((r : ℤ) * σr) * (s0⁻¹ * h x * h (x + half n)) ^ r ∧
      s0 ^ (r - 1) = (legendreSym r (pp n : ℤ) : L) ∧
      (s0⁻¹ * h x * h (x + half n)) * (s0⁻¹ * h (-x) * h (-x + half n)) = kappa n L * (ω ^ (2 * x).val) ^ (n / 2) :=
  Xia.Proofs.thm_6_4_step3_proved n a nodd r hn ha hodd hr σr ω hω h s0 hs x hF1 hF3

/-- Row 24b' — proof of Theorem 6.4, Step 3, last sentence (s6_primes.tex:173-175): for a solution, with `Ξ_a` the elements of
order `2^a` of `μ_{2^a}` (exponent model: `k` of additive order `2^a`, i.e. `2^a k = 0 ≠ 2^{a-1} k`): `∏_{ζ ∈ Ξ_a} ŷ(ζ) = (-κ)^{2^{a-2}} = S^{2^{a-1}}`, and (F1_r) at
`-1` reads `(-1)^{σ_r} S^{r-1} = 1`. -/
theorem thm_6_4_step3b (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a)
    (hodd : Odd nodd) (hr : ¬ r ∣ pp n * n) (σr : ℤ) {L : Type*} [Field L]
    [Algebra (GaloisField r (n / Int.gcd σr n)) L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (y : ZMod n → GaloisField r (n / Int.gcd σr n)) (hy : y ∈ NFrSet n r σr) :
    ∏ k ∈ univ.filter (fun k : ZMod n => (2 ^ a : ZMod n) * k = 0 ∧ (2 ^ (a - 1) : ZMod n) * k ≠ 0), dftA ω y k =
        (-kappa n L) ^ (2 ^ (a - 2)) ∧
      (-kappa n L) ^ (2 ^ (a - 2)) = algebraMap _ L (S y) ^ (2 ^ (a - 1)) ∧
      (-1) ^ σr.natAbs * algebraMap _ L (S y) ^ (r - 1) = 1 :=
  Xia.Proofs.thm_6_4_step3b_of n a nodd r hn ha hodd hr σr ω hω y hy (sec_6_3_fourier n a nodd r hn ha hodd hr σr ω hω)

/-- Row 24c — proof of Theorem 6.4, Steps 4-5 (s6_primes.tex:177-182), algebraically closed `L` of characteristic `r`: for a
solution (with `(-1)^{σ_r} = (p/r)`), `P(α) := S^{-1}ŷ(-α)` satisfies `P(α) = κ^{-2^{a-2}} ∏_{ρ^{2^{a-1}} = -α} ŷ(ρ)` and (E1)
`f(α^2) = P(α)f(α)`; `f(1) = ±n`; `P` lies in `G''` (laws `P(α^r) = α^{rσ_r}P(α)^r`, `P(α)P(α^{-1}) = α^m`) and `f` in `G'`
((E2_r), (E3_r) with `κ`); `G'` is non-empty and `f ↦ τf/f` maps `G'` into `G''` (κ cancels). -/
theorem thm_6_4_step45 (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a)
    (hodd : Odd nodd) (hr : ¬ r ∣ pp n * n) (hr1 : r % 2 ^ a ≠ 2 ^ a - 1) (σr : ℤ) {L : Type*} [Field L] [CharP L r]
    [IsAlgClosed L] [Algebra (GaloisField r (n / Int.gcd σr n)) L] (ω : L) (hω : IsPrimitiveRoot ω n) :
    (∀ y ∈ NFrSet n r σr,
      (∀ k : ZMod n, 2 ^ a ∣ k.val →
        (algebraMap _ L (S y))⁻¹ * dftA ω y (k + half n) = (kappa n L)⁻¹ ^ (2 ^ (a - 2)) *
          ∏ ρ ∈ (topLayer n).filter (fun ρ => (2 ^ (a - 1) : ZMod n) * ρ = k + half n), dftA ω y ρ ∧
        dftA ω y (2 * k) = (algebraMap _ L (S y))⁻¹ * dftA ω y (k + half n) * dftA ω y k) ∧
      (dftA ω y 0 = (n : L) ∨ dftA ω y 0 = -(n : L)) ∧
      (∀ k ∈ layer0' n a,
        (algebraMap _ L (S y))⁻¹ * dftA ω y ((r : ZMod n) * k + half n) =
          (ω ^ k.val) ^ ((r : ℤ) * σr) * ((algebraMap _ L (S y))⁻¹ * dftA ω y (k + half n)) ^ r ∧
        ((algebraMap _ L (S y))⁻¹ * dftA ω y (k + half n)) * ((algebraMap _ L (S y))⁻¹ * dftA ω y (-k + half n)) =
          (ω ^ k.val) ^ (n / 2)) ∧
      ∀ k ∈ layer0' n a, dftA ω y ((r : ZMod n) * k) = (ω ^ k.val) ^ ((r : ℤ) * σr) * dftA ω y k ^ r ∧
        dftA ω y k * dftA ω y (-k) = kappa n L * (ω ^ k.val) ^ (n / 2)) ∧
    (Gprime n a r σr (kappa n L) ω).Nonempty ∧
    ∀ f ∈ Gprime n a r σr (kappa n L) ω, tauG n a f / f ∈ Gprime n a r σr 1 ω :=
  Xia.Proofs.thm_6_4_step45_of n a nodd r hn ha hodd hr hr1 σr ω hω (sec_6_3_fourier n a nodd r hn ha hodd hr σr ω hω)

/-- Row 24d — proof of Theorem 6.4, Steps 6-7 (s6_primes.tex:184-185, "word for word"), algebraically closed `L` of
characteristic `r`: `Π : 𝒟^0 → G` is onto, `|(τ-1)G| · |G^τ| = |G|`, and the group of solutions of the homogeneous laws for `r`
has `4 ∏_i (r^{L_i}-1)` elements. -/
theorem thm_6_4_step67 (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a)
    (hodd : Odd nodd) (hr : ¬ r ∣ pp n * n) (hr1 : r % 2 ^ a ≠ 2 ^ a - 1) {L : Type*} [Field L] [CharP L r]
    [IsAlgClosed L] :
    Set.SurjOn (Pmap n a) (topData0 n r : Set (ZMod n → L)) (Ggrp n a r) ∧
    Nat.card ((fun g => tauG n a g / g) '' (Ggrp n a r : Set (ZMod n → L))) *
        Nat.card {g : ZMod n → L // g ∈ (Ggrp n a r : Set (ZMod n → L)) ∧ tauG n a g = g} =
      Nat.card (Ggrp n a r : Set (ZMod n → L)) ∧
    Nat.card {lam : ZMod n → L // (∀ k, lam ((r : ZMod n) * k) = lam k ^ r) ∧ (∀ k, lam k * lam (-k) = 1) ∧
      ∀ k, lam k * lam (k + half n) = lam (half n) * lam (2 * k)} = 4 * pairProd n r :=
  Xia.Proofs.thm_6_4_step67_proved n a nodd r hn ha hodd hr hr1

/-- Row 24(ii) — Theorem 6.4(ii) (s6_primes.tex:144): if `(-1)^{σ_r} = (p/r)`, the norm-free system in characteristic `r` has exactly
`4 ∏_i (r^{L_i} - 1)` solutions. -/
theorem thm_6_4_ii (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (hr : ¬ r ∣ pp n * n) (hr1 : r % 2 ^ a ≠ 2 ^ a - 1) (σr : ℤ)
    (hsign : (-1 : ℤ) ^ σr.natAbs = legendreSym r (pp n : ℤ)) : Nat.card (NFrSet n r σr) = 4 * pairProd n r :=
  Xia.Proofs.thm_6_4_ii_of n a nodd r hn ha hodd hr hr1 σr hsign
    (fun _ _ _ ω hω => sec_6_3_fourier n a nodd r hn ha hodd hr σr ω hω)
    (fun _ _ _ _ => thm_6_4_step67 n a nodd r hn ha hodd hr hr1)

/-- Coverage — proof of Theorem 6.4, Step 1 (s6_primes.tex:162-164): for `a ≥ 3`, `-1 ∈ ⟨r⟩ (mod 2^a)` only if
`r ≡ -1 (mod 2^a)`. -/
theorem thm_6_4_step1 (a r : ℕ) (ha : 3 ≤ a) (hr : Odd r) :
    (∃ k : ℕ, (r : ZMod (2 ^ a)) ^ k = -1) → (r : ZMod (2 ^ a)) = -1 :=
  Xia.Proofs.thm_6_4_step1_proved a r ha hr

/-- Coverage — s6_primes.tex:148-150: for `r = 3` and `n ≡ 2 (mod 3)`: `κ = 1` in `F_3` and `(p/3) = 1`; for `r = 5`,
`n = 2^e`, `e ≥ 3` odd, there is one pair of top `5`-orbits, of length `n/4`. -/
theorem thm_6_4_remarks :
    (∀ n : ℕ, n % 3 = 2 → kappa n (ZMod 3) = 1 ∧ legendreSym 3 (pp n : ℤ) = 1) ∧
    (∀ n e : ℕ, n = 2 ^ e → 3 ≤ e → Odd e → ∀ [NeZero n],
      (topPairs n 5).card = 1 ∧ ∀ P ∈ topPairs n 5, pairLen P = n / 4) :=
  Xia.Proofs.thm_6_4_remarks_proved

/-- SUPERSEDED by cor_6_5_sign_uncond (no such hypothesis: Xia's Lemma 3.5 `hX35r` is proved in Lean as xia_lemma_3_5). Row 25a — Corollary 6.5, sign part (s6_primes.tex:152-154), PROVED GIVEN Xia's Lemma 3.5 (Xia's shift is tied
to a character: `χ` of order `n` on `F_p` with values in a field `M` (Xia: `r`-adic, `M = ℂ_r`), `μ` primitive, `χ(r) = μ^{σ_r}`;
hypothesis `hX35r` = Xia Lemma 3.5 for `r`, v7 pp. 11-12: `χ(r) = μ'^{σ'}` ⇒ `(-1)^{σ'} = ((-1)^{n/2} p / r)`):
let `p` be prime; for every prime `r ∤ pn`, Xia's shift satisfies `(-1)^{σ_r} = (p/r)` (as `4 ∣ n`), so case (ii) of
Theorem 6.4 applies; hence for every `r ≢ -1 (mod 2^a)`, and for every `r` when `n = 2^a` (Prop 6.6), the norm-free
`r`-system is solvable. -/
theorem cor_6_5_sign (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a)
    (hodd : Odd nodd) (hp : (pp n).Prime) (hr : ¬ r ∣ pp n * n) {M : Type*} [Field M] (χ : MulChar (ZMod (pp n)) M) (g : (ZMod (pp n))ˣ)
    (_hg : ∀ x : (ZMod (pp n))ˣ, x ∈ Subgroup.zpowers g) (_hχg : IsPrimitiveRoot (χ (g : ZMod (pp n))) n)
    (μ : M) (hμ : IsPrimitiveRoot μ n) (σr : ℤ) (hχr : χ (r : ZMod (pp n)) = μ ^ σr)
    (hX35r : ∀ (μ' : M) (σ' : ℤ), IsPrimitiveRoot μ' n → χ (r : ZMod (pp n)) = μ' ^ σ' →
      (-1 : ℤ) ^ σ'.natAbs = legendreSym r ((-1) ^ (n / 2) * (pp n : ℤ))) :
    (-1 : ℤ) ^ σr.natAbs = legendreSym r (pp n : ℤ) :=
  Xia.Proofs.cor_6_5_sign_proved n a nodd r hn ha hodd hp hr σr (hX35r μ σr hμ hχr)

/-- Row 26(i) — Proposition 6.6, first case (s6_primes.tex:188-191): `n = 2^a`, `a ≥ 3`, `r` prime, `r ∤ p`, `r ≡ -1 (mod 2^a)`: if
`(-1)^{σ_r} ≠ (p/r)` the norm-free system in characteristic `r` has no solution (EMPTY); if `=`, exactly `4(r+1)^{n/4}` solutions. -/
theorem prop_6_6_i (n a r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a) (ha : 3 ≤ a) (hr : ¬ r ∣ pp n)
    (hr1 : r % 2 ^ a = 2 ^ a - 1) (σr : ℤ) (hsign : (-1 : ℤ) ^ σr.natAbs ≠ legendreSym r (pp n : ℤ)) :
    NFrSet n r σr = ∅ :=
  Xia.Proofs.prop_6_6_i_proved n a r hn ha hr hr1 σr hsign

/-- Row 26(ii) — Proposition 6.6, second case (s6_primes.tex:190): if `(-1)^{σ_r} = (p/r)`, exactly `4(r+1)^{n/4}`. -/
theorem prop_6_6_ii (n a r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a) (ha : 3 ≤ a) (hr : ¬ r ∣ pp n)
    (hr1 : r % 2 ^ a = 2 ^ a - 1) (σr : ℤ) (hsign : (-1 : ℤ) ^ σr.natAbs = legendreSym r (pp n : ℤ)) :
    Nat.card (NFrSet n r σr) = 4 * (r + 1) ^ (n / 4) :=
  Xia.Proofs.prop_6_6_ii_of n a r hn ha hr hr1 σr hsign
    (fun hn' hodd' hr' _ _ _ ω hω => sec_6_3_fourier n a 1 r hn' ha hodd' hr' σr ω hω)

/-- SUPERSEDED by cor_6_5_solvable_uncond (no such hypothesis: Xia's Lemma 3.5 `hX35r` is proved in Lean as xia_lemma_3_5). Row 25b — Corollary 6.5, "Hence" (s6_primes.tex:154-156), PROVED GIVEN Xia's Lemma 3.5 (hypothesis `hX35r`): for
every `r ≢ -1 (mod 2^a)`, and for every `r` when `n = 2^a` (Prop 6.6), the norm-free system in characteristic `r` is solvable. -/
theorem cor_6_5_solvable (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a)
    (hodd : Odd nodd) (hp : (pp n).Prime) (hr : ¬ r ∣ pp n * n) {M : Type*} [Field M] (χ : MulChar (ZMod (pp n)) M) (g : (ZMod (pp n))ˣ)
    (hg : ∀ x : (ZMod (pp n))ˣ, x ∈ Subgroup.zpowers g) (hχg : IsPrimitiveRoot (χ (g : ZMod (pp n))) n)
    (μ : M) (hμ : IsPrimitiveRoot μ n) (σr : ℤ) (hχr : χ (r : ZMod (pp n)) = μ ^ σr)
    (hX35r : ∀ (μ' : M) (σ' : ℤ), IsPrimitiveRoot μ' n → χ (r : ZMod (pp n)) = μ' ^ σ' →
      (-1 : ℤ) ^ σ'.natAbs = legendreSym r ((-1) ^ (n / 2) * (pp n : ℤ))) :
    r % 2 ^ a ≠ 2 ^ a - 1 ∨ nodd = 1 → (NFrSet n r σr).Nonempty :=
  Xia.Proofs.cor_6_5_solvable_of n a nodd r hn ha hodd hp hr χ g hg hχg μ hμ σr hχr hX35r
    (fun hr1 hsign => thm_6_4_ii n a nodd r hn ha hodd hr hr1 σr hsign)
    (fun hn' hr' hr1 hsign => prop_6_6_ii n a r hn' ha hr' hr1 σr hsign)

/-! ## The main theorems of the introduction (restatements of body results) -/

/-- Theorem A (P10s_main.tex:147-156) = Theorem 4.1 + Proposition 4.3 + row 27: for every even divisor `σ` of `n` the
norm-free system with shift `σ` has exactly `4 ∏_i (3^{L_i}-1)` solutions, in particular one; for odd `σ` none; for
`n ≡ 8 (mod 24)` every solution of Xia's system solves the norm-free system with the same `σ`. -/
theorem thm_A (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n) :
    (∀ σ : ℕ, σ ∣ n → Even σ → Nat.card (NFSet n σ) = 4 * pairProd n 3 ∧ (NFSet n σ).Nonempty) ∧
      (∀ σ : ℕ, σ ∣ n → Odd σ → NFSet n σ = ∅) ∧
      (n % 24 = 8 → ∀ σ : ℕ, σ ∣ n → XiaSet n σ ⊆ NFSet n σ) :=
  Xia.Proofs.thm_A_of n a nodd hn ha hodd h3 (fun σ hσ he => prop_4_3_even n a nodd hn ha hodd h3 σ hσ he)

/-- Theorem C (P10s_main.tex:216-222) = Theorem 6.4 (i), (ii). -/
theorem thm_C (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (hr : ¬ r ∣ pp n * n) (hr1 : r % 2 ^ a ≠ 2 ^ a - 1) (σr : ℤ) :
    ((-1 : ℤ) ^ σr.natAbs ≠ legendreSym r (pp n : ℤ) → NFrSet n r σr = ∅) ∧
      ((-1 : ℤ) ^ σr.natAbs = legendreSym r (pp n : ℤ) → Nat.card (NFrSet n r σr) = 4 * pairProd n r) :=
  ⟨fun hs => thm_6_4_i n a nodd r hn ha hodd hr hr1 σr hs, fun hs => thm_6_4_ii n a nodd r hn ha hodd hr hr1 σr hs⟩

/-! ## Printed claims that were split (one row per printed claim) and coverage links -/

/-- Row 16 — Proposition 4.3 AS PRINTED (s4_normfree.tex:148-150) = rows 16a + 16b. -/
theorem prop_4_3 (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    (σ : ℕ) (hσ : σ ∣ n) :
    (Even σ → Nat.card (NFSet n σ) = 4 * pairProd n 3) ∧ (Odd σ → NFSet n σ = ∅) :=
  ⟨fun he => prop_4_3_even n a nodd hn ha hodd h3 σ hσ he, fun ho => prop_4_3_odd n a nodd hn ha hodd h3 σ hσ ho⟩

/-- Row 24 — Theorem 6.4 AS PRINTED (s6_primes.tex:138-146) = rows 24(pairs), 24(i), 24(ii). -/
theorem thm_6_4 (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (hr : ¬ r ∣ pp n * n) (hr1 : r % 2 ^ a ≠ 2 ^ a - 1) (σr : ℤ) :
    ((∀ O ∈ topOrbits n r, inv O ∈ topOrbits n r ∧ inv O ≠ O ∧ (inv O).card = O.card) ∧
      ∑ P ∈ topPairs n r, pairLen P = n / 4) ∧
    ((-1 : ℤ) ^ σr.natAbs ≠ legendreSym r (pp n : ℤ) → NFrSet n r σr = ∅) ∧
    ((-1 : ℤ) ^ σr.natAbs = legendreSym r (pp n : ℤ) → Nat.card (NFrSet n r σr) = 4 * pairProd n r) :=
  ⟨thm_6_4_pairs n a nodd r hn ha hodd hr hr1, fun hs => thm_6_4_i n a nodd r hn ha hodd hr hr1 σr hs,
    fun hs => thm_6_4_ii n a nodd r hn ha hodd hr hr1 σr hs⟩

/-- Row 26 — Proposition 6.6 AS PRINTED (s6_primes.tex:188-191) = rows 26(i) + 26(ii). -/
theorem prop_6_6 (n a r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a) (ha : 3 ≤ a) (hr : ¬ r ∣ pp n)
    (hr1 : r % 2 ^ a = 2 ^ a - 1) (σr : ℤ) :
    ((-1 : ℤ) ^ σr.natAbs ≠ legendreSym r (pp n : ℤ) → NFrSet n r σr = ∅) ∧
      ((-1 : ℤ) ^ σr.natAbs = legendreSym r (pp n : ℤ) → Nat.card (NFrSet n r σr) = 4 * (r + 1) ^ (n / 4)) :=
  ⟨fun hs => prop_6_6_i n a r hn ha hr hr1 σr hs, fun hs => prop_6_6_ii n a r hn ha hr hr1 σr hs⟩

/-- SUPERSEDED by cor_6_5_sign_uncond + cor_6_5_solvable_uncond (no such hypothesis: Xia's Lemma 3.5 `hX35r` is proved in Lean as xia_lemma_3_5). Row 25 — Corollary 6.5 AS PRINTED (s6_primes.tex:152-156) = rows 25a + 25b, PROVED GIVEN Xia's Lemma 3.5. -/
theorem cor_6_5 (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (hp : (pp n).Prime) (hr : ¬ r ∣ pp n * n) {M : Type*} [Field M] (χ : MulChar (ZMod (pp n)) M) (g : (ZMod (pp n))ˣ)
    (hg : ∀ x : (ZMod (pp n))ˣ, x ∈ Subgroup.zpowers g) (hχg : IsPrimitiveRoot (χ (g : ZMod (pp n))) n)
    (μ : M) (hμ : IsPrimitiveRoot μ n) (σr : ℤ) (hχr : χ (r : ZMod (pp n)) = μ ^ σr)
    (hX35r : ∀ (μ' : M) (σ' : ℤ), IsPrimitiveRoot μ' n → χ (r : ZMod (pp n)) = μ' ^ σ' →
      (-1 : ℤ) ^ σ'.natAbs = legendreSym r ((-1) ^ (n / 2) * (pp n : ℤ))) :
    (-1 : ℤ) ^ σr.natAbs = legendreSym r (pp n : ℤ) ∧
      (r % 2 ^ a ≠ 2 ^ a - 1 ∨ nodd = 1 → (NFrSet n r σr).Nonempty) :=
  ⟨cor_6_5_sign n a nodd r hn ha hodd hp hr χ g hg hχg μ hμ σr hχr hX35r,
    cor_6_5_solvable n a nodd r hn ha hodd hp hr χ g hg hχg μ hμ σr hχr hX35r⟩

/-- Coverage — s3_pow2.tex:87 (review N1): `V` has `Q = 3^{m/2}` elements (`F_3`-dimension `m/2`), `n = 2^e`, `e ≥ 4`. -/
theorem sec_3_2_V_card (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 4 ≤ e) :
    Nat.card (Vsp n : Set (GaloisField 3 (n / 2))) = QQ n :=
  Xia.Proofs.sec_3_2_V_card_proved n e hne he

/-- Coverage — s2_xia.tex:52-53 (review N3): for `4 ∣ n`, `N(x) = x x̄` and `N(x) ∈ k_0` (`\overline{N(x)} = N(x)`), and
`x ↦ x̄` is an involution of `F` (`x̿ = x`). -/
theorem sec_2_2_norm (n : ℕ) (h4 : 4 ∣ n) (x : GaloisField 3 (n / 2)) :
    Nm n x = x * bar n x ∧ bar n (Nm n x) = Nm n x ∧ bar n (bar n x) = x :=
  Xia.Proofs.sec_2_2_norm_proved n h4 x

/-- Coverage — s6_primes.tex:72-74 (review N2): `4(Q_5-1)` divides `5^n - 1 = (Q_5-1)(Q_5+1)(Q_5^2+1)`, and
`x ↦ x^{Q_5-1}` maps `μ_{4(Q_5-1)}` (in `F_{5^n}`) onto `μ_4`, which contains `-ι_5`. -/
theorem thm_6_2_sets (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) (ξ0 : GaloisField 5 n)
    (hξ0 : IsPrimitiveRoot ξ0 n) :
    4 * (5 ^ (n / 4) - 1) ∣ 5 ^ n - 1 ∧
      5 ^ n - 1 = (5 ^ (n / 4) - 1) * (5 ^ (n / 4) + 1) * ((5 ^ (n / 4)) ^ 2 + 1) ∧
      (fun x : GaloisField 5 n => x ^ (5 ^ (n / 4) - 1)) '' {x | x ^ (4 * (5 ^ (n / 4) - 1)) = 1} = {z | z ^ 4 = 1} ∧
      (-ξ0 ^ (n / 4)) ^ 4 = 1 :=
  Xia.Proofs.thm_6_2_sets_proved n e hne he heo ξ0 hξ0

/-- Coverage — P10s_main.tex:178, s5_twonorms.tex:22 (review S3(b)): in cases A and B the length `L` of `O` is even. -/
theorem caseAB_even (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n) :
    ∀ O ∈ topOrbits n 3, IsCaseA O ∨ IsCaseB O → Even O.card :=
  Xia.Proofs.caseAB_even_proved n a nodd hn ha hodd h3

/-- Coverage — s5_twonorms.tex:4 (review S3(c)): a fibre is not a linear space (it does not contain `0`). -/
theorem fibre_not_linear (n : ℕ) [NeZero n] {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L)
    (y : ZMod n → GaloisField 3 (n / 2)) : (0 : ZMod n → GaloisField 3 (n / 2)) ∉ fibre ω y :=
  Xia.Proofs.fibre_not_linear_proved n ω y

/-- Coverage — P10s_main.tex:205-206 (review S2(a)): for `n = 2^e`, `e ≥ 5` odd, the points of a fibre form a conic in `V`
(Thm 3.4(c)), not a product of a subset of `V_+` and a subset of `V_-`. -/
theorem intro_conic_not_product (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 5 ≤ e) (heo : Odd e)
    (ξ0 : GaloisField 3 (n / 2)) (hξ0 : IsPrimitiveRoot ξ0 n) (ν : GaloisField 3 (n / 2)) (hν : ν ^ (qq n - 1) = -1) :
    ¬ ∃ A B : Set (GaloisField 3 (n / 2)),
      {pr : GaloisField 3 (n / 2) × GaloisField 3 (n / 2) |
        pr.1 ∈ Vplus n ξ0 ∧ pr.2 ∈ Vminus n ξ0 ∧ pr.1 ^ 2 - pr.2 ^ 2 = iota n ξ0 * ν} = A ×ˢ B :=
  Xia.Proofs.intro_conic_not_product_proved n e hne he heo ξ0 hξ0 ν hν

/-! ## WAVE 2 — named proof steps, Section 4.1, Theorem B, Remark 4.4, numeric links -/

/-- Row 7f — proof of Theorem 3.1, Step 2 (s3_pow2.tex:26-35): for a solution, `θ := ŷ(ξ_0)` is non-zero and
`θ^{Q-1} = -1`. Conversely, for `θ` with `θ^{Q-1} = -1`, the values `t_k := ξ_0^{2k3^k} θ^{3^k}` (at `ξ_0^{3^k} ∈ O`)
satisfy (F1) along `O` (`t_{k+1} = (ξ_0^{3^k})^6 t_k^3`), close up at the wrap (`t_{k+m/2} = t_k`), and the values
`-1/t_k` that (F3) puts on `O^{-1}` satisfy (F1) there. -/
theorem thm_3_1_step2 (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) :
    (∀ y ∈ NFSet n 2, dft ξ0 y 1 ≠ 0 ∧ dft ξ0 y 1 ^ (QQ n - 1) = -1) ∧
    ∀ θ : GaloisField 3 (n / 2), θ ^ (QQ n - 1) = -1 →
      (∀ k : ℕ, ξ0 ^ (2 * (k + 1) * 3 ^ (k + 1)) * θ ^ (3 ^ (k + 1)) =
        (ξ0 ^ (3 ^ k)) ^ 6 * (ξ0 ^ (2 * k * 3 ^ k) * θ ^ (3 ^ k)) ^ 3) ∧
      (∀ k : ℕ, ξ0 ^ (2 * (k + n / 4) * 3 ^ (k + n / 4)) * θ ^ (3 ^ (k + n / 4)) = ξ0 ^ (2 * k * 3 ^ k) * θ ^ (3 ^ k)) ∧
      (∀ k : ℕ, -1 / (ξ0 ^ (2 * (k + 1) * 3 ^ (k + 1)) * θ ^ (3 ^ (k + 1))) =
        ((ξ0 ^ (3 ^ k))⁻¹) ^ 6 * (-1 / (ξ0 ^ (2 * k * 3 ^ k) * θ ^ (3 ^ k))) ^ 3) :=
  Xia.Proofs.thm_3_1_step2_proved n e hne he ξ0 hξ0

/-- Row 7g — proof of Theorem 3.1, Step 3 (s3_pow2.tex:37-51), the layer recursion: if (F1) and (F3) hold at `ξ` and
`-ξ` (exponent model: at `x` and `x + n/2`) and `S^2 = 1`, then `ŷ(η) := S ŷ(ξ)ŷ(-ξ)` at `η = ξ^2` satisfies (F1),
`S ŷ(ξ^3)ŷ(-ξ^3) = η^6 (S ŷ(ξ)ŷ(-ξ))^3`, and (F3), `(S ŷ(ξ)ŷ(-ξ))(S ŷ(ξ^{-1})ŷ(-ξ^{-1})) = η^m` (any field, `4 ∣ n`). -/
theorem thm_3_1_step3 (n : ℕ) [NeZero n] (h4 : 4 ∣ n) {L : Type*} [Field L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (h : ZMod n → L) (s0 : L) (hs : s0 ^ 2 = 1) (x : ZMod n)
    (hF1 : ∀ z ∈ ({x, x + half n} : Set (ZMod n)), h (3 * z) = (ω ^ z.val) ^ 6 * h z ^ 3)
    (hF3 : ∀ z ∈ ({x, x + half n} : Set (ZMod n)), h z * h (-z) = (ω ^ z.val) ^ (n / 2)) :
    s0 * h (3 * x) * h (3 * x + half n) = (ω ^ (2 * x).val) ^ 6 * (s0 * h x * h (x + half n)) ^ 3 ∧
      (s0 * h x * h (x + half n)) * (s0 * h (-x) * h (-x + half n)) = (ω ^ (2 * x).val) ^ (n / 2) :=
  Xia.Proofs.thm_3_1_step3_proved n h4 ω hω h s0 hs x hF1 hF3

/-- Row 7h — proof of Theorem 3.1, Step 4 (s3_pow2.tex:54-57), `ι = ξ_0^{n/4}`: (F3) gives `ŷ(ι)ŷ(-ι) = ι^m = 1`, so
the step `j = 1` gives `ŷ(-1) = S`; (F3) at `1` forces `ŷ(1)^2 = 1`, and then (F1) at `1` holds; (F3) at `-1` gives
`S^2 = 1` (any field). -/
theorem thm_3_1_step4 (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) {L : Type*} [Field L] (ω : L)
    (hω : IsPrimitiveRoot ω n) (h : ZMod n → L) (hF3 : F3 ω h) :
    h ((n / 4 : ℕ) : ZMod n) * h (((n / 4 : ℕ) : ZMod n) + half n) = 1 ∧ h 0 ^ 2 = 1 ∧ h 0 = h 0 ^ 3 ∧
      h (half n) ^ 2 = 1 :=
  Xia.Proofs.thm_3_1_step4_proved n e hne he ω hω h hF3

/-- Row 14c — Section 4.1, homogeneous laws (s4_normfree.tex:39-48): if `ŷ, ŷ'` satisfy (F1), (F3), (F4), then
`λ := ŷ'/ŷ` satisfies (h1) `λ(ξ^3) = λ(ξ)^3`, (h3) `λ(ξ)λ(ξ^{-1}) = 1`, (h4) `λ(ξ)λ(-ξ) = λ(-1)λ(ξ^2)`; conversely
`λŷ` satisfies (F1), (F3), (F4) when `ŷ` does and `λ` satisfies (h1), (h3), (h4); so `NF(n)` is empty or has as many
elements as the group `K_n` of solutions of (h1), (h3), (h4); every `λ ∈ K_n` has `λ(ξ)^{3^{ord_n(3)}-1} = 1`, so `K_n`
is finite. -/
theorem sec_4_1_homog (n : ℕ) [NeZero n] (hn : Even n) (h3 : ¬ 3 ∣ n) {L : Type*} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) :
    let H : (ZMod n → L) → Prop := fun lam => (∀ k, lam (3 * k) = lam k ^ 3) ∧ (∀ k, lam k * lam (-k) = 1) ∧
      (∀ k, lam k * lam (k + half n) = lam (half n) * lam (2 * k))
    (∀ h h' : ZMod n → L, (F1 3 2 ω h ∧ F3 ω h ∧ F4 h) → (F1 3 2 ω h' ∧ F3 ω h' ∧ F4 h') →
      H (fun k => h' k / h k)) ∧
    (∀ h lam : ZMod n → L, (F1 3 2 ω h ∧ F3 ω h ∧ F4 h) → H lam →
      F1 3 2 ω (fun k => lam k * h k) ∧ F3 ω (fun k => lam k * h k) ∧ F4 (fun k => lam k * h k)) ∧
    ((NFSet n 2).Nonempty → Nat.card (NFSet n 2) = Nat.card {lam : ZMod n → L // H lam}) ∧
    (∀ lam : ZMod n → L, H lam → ∀ k, lam k ^ (3 ^ orderOf (3 : ZMod n) - 1) = 1) ∧
    {lam : ZMod n → L | H lam}.Finite :=
  Xia.Proofs.sec_4_1_homog_of_proved n hn h3 ω hω (prop_2_4_bij n hn h3 ω hω)

/-- Row 14d — proof of Theorem 4.1, Step 3, equation (eq:descent) (s4_normfree.tex:85-95): for a solution and `ξ ∈ μ_n`
of layer `j ≥ 1` (exponent model: `v_2(k) = a - j`), `ŷ(ξ) = S^{2^{a-j}-1} ∏_{ρ ∈ 𝓛_a, ρ^{2^{a-j}} = ξ} ŷ(ρ)`; and
`ŷ(-1) = S`. -/
theorem thm_4_1_descent (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2) :
    (∀ (j : ℕ) (k : ZMod n), 1 ≤ j → j ≤ a - 1 → k ≠ 0 → padicValNat 2 k.val = a - j →
      dftA ω y k = algebraMap _ L (S y) ^ (2 ^ (a - j) - 1) *
        ∏ ρ ∈ (topLayer n).filter (fun ρ => (2 ^ (a - j) : ZMod n) * ρ = k), dftA ω y ρ) ∧
    dftA ω y (half n) = algebraMap _ L (S y) :=
  Xia.Proofs.thm_4_1_descent_of n a nodd hn ha hodd h3 ω hω y hy
    (prop_2_4_F3 n (Xia.Proofs.H9_even_halves hn (by omega)).1 h3 ω hω y) (prop_2_4_F4 n (Xia.Proofs.H9_even_halves hn (by omega)).1 h3 ω hω y)

/-- Row 21b — proof of Theorem 6.2, Step 1 (s6_primes.tex:77-80): `v_2(5^{n/4} - 1) = e`, so `μ_n ⊂ F_{Q_5}`;
`ord(5) = m/2` in `(ℤ/2^e)^×`, every unit is `±5^k`, `-1 ∉ ⟨5⟩`; the odd residues (elements of order `n`) form two
disjoint orbits `{5^k}`, `{-5^k}`. -/
theorem thm_6_2_step1 (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) :
    padicValNat 2 (5 ^ (n / 4) - 1) = e ∧ (∀ ξ : GaloisField 5 n, ξ ^ n = 1 → ξ ^ (5 ^ (n / 4)) = ξ) ∧
      orderOf (5 : ZMod n) = n / 4 ∧ (∀ k : ℕ, (-1 : ZMod n) ≠ (5 : ZMod n) ^ k) ∧
      (∀ x : ZMod n, IsUnit x → ∃ k : ℕ, x = (5 : ZMod n) ^ k ∨ x = -(5 : ZMod n) ^ k) ∧
      (∀ x : ZMod n, Odd x.val → orbit 5 x = orbit 5 1 ∨ orbit 5 x = inv (orbit 5 1)) ∧
      Disjoint (orbit 5 (1 : ZMod n)) (inv (orbit 5 1)) :=
  Xia.Proofs.thm_6_2_step1_proved n e hne he heo

/-- Theorem B (P10s_main.tex:174-195), the parts not tied to `V`, `T`: the substitution is an involution of the
norm-free system; case B occurs only when `a = 3`, so `b = 0` when `16 ∣ n`; each fibre contains at most 4 solutions of
Xia's system; Xia's system has at most `16 ∏_𝒜 (q_O-1) ∏_ℬ (q_O+1) ∏_𝒞 (3^L-1) ≤ 16 (4/3)^b 3^{n/8}` solutions; for
`n = 2^e`, `e ≥ 5` odd, this bound is `16(3^{n/8}-1)`, compared with the `4(3^{n/4}-1)` norm-free solutions. (The `V`, `T`,
`V_±` statements: rows thm_B_V, thm_B_subst_fibre, thm_B_pow2_V.) -/
theorem thm_B_part (n : ℕ) [NeZero n] (hn : n % 24 = 8) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L]
    (ω : L) (hω : IsPrimitiveRoot ω n) :
    (∀ y ∈ NFSet n 2, ySubst y ∈ NFSet n 2 ∧ ySubst (ySubst y) = y) ∧
      (16 ∣ n → (blocksB n).card = 0) ∧
      (∀ y ∈ NFSet n 2, (fibre ω y ∩ XiaSet n 2).ncard ≤ 4) ∧
      Nat.card (XiaSet n 2) ≤ 16 * fibreProd n ∧
      (16 * fibreProd n : ℝ) ≤ 16 * (4 / 3 : ℝ) ^ (blocksB n).card * 3 ^ (n / 8) ∧
      ∀ e : ℕ, n = 2 ^ e → 5 ≤ e → 16 * fibreProd n = 16 * (3 ^ (n / 8) - 1) ∧
        Nat.card (NFSet n 2) = 4 * (3 ^ (n / 4) - 1) :=
  Xia.Proofs.thm_B_part_of n hn ω hω
    (fun ω' hω' hnL z => Xia.Paper.fourier_inversion n (Xia.Proofs.H19_even_of24 hn) ω' hω' hnL z)
    (fun a nodd hn' ha hodd h3 => Xia.Paper.thm_5_1_c_count n a nodd hn' ha hodd h3 ω hω)
    (fun a nodd hn' ha hodd h3 => Xia.Paper.thm_4_1_count n a nodd hn' ha hodd h3)

/-- Row 17 (partial) — Remark 4.4 (s4_normfree.tex:167-172), `n = 80`: the top orbits form 5 pairs, each of length 4
(one pair over `α = 1`, four over `α ≠ 1`), so `|𝒟| = 80^5`, and the total is `4 · 80^5`. (The statements about `G`,
`G^τ` and the extendable fraction are about objects inside the proof of Thm 4.1: PENDING with Steps 4-7.) -/
theorem rem_4_4 : (topPairs 80 3).card = 5 ∧ (∀ P ∈ topPairs 80 3, pairLen P = 4) ∧ pairProd 80 3 = 80 ^ 5 ∧
    Nat.card (NFSet 80 2) = 4 * 80 ^ 5 :=
  Xia.Proofs.rem_4_4_of Xia.Paper.thm_4_1_count

/-- Link L1 — after Corollary 3.5 (s3_pow2.tex:138-139): for `n = 32` the bound is `1280`, compared with `26240`
norm-free solutions; for `n = 128` it is `688 747 520`, compared with `7 412 080 755 407 360`. (Status follows
Theorem 3.1 and Corollary 3.5(ii).) -/
theorem link_L1 :
    (16 * (qq 32 - 1) = 1280 ∧ Nat.card (XiaSet 32 2) ≤ 1280 ∧ Nat.card (NFSet 32 2) = 26240) ∧
      (16 * (qq 128 - 1) = 688747520 ∧ Nat.card (XiaSet 128 2) ≤ 688747520 ∧
        Nat.card (NFSet 128 2) = 7412080755407360) :=
  Xia.Proofs.link_L1_of Xia.Paper.thm_3_1_card Xia.Paper.cor_3_5_ii

/-! ## WAVE 3 — the remaining named steps, Section 5 in y-form, numeric links -/

/-- Row 17b — Remark 4.4 (s4_normfree.tex:169-172), `n = 80`, `a = 4`, `n_odd = 5`: `|G| = 10`, `G^τ = {±1}` (2 elements),
`(τ-1)G = {g : g^5 = 1}` (5 elements) (algebraically closed `L` of characteristic 3). -/
theorem rem_4_4_G {L : Type*} [Field L] [CharP L 3] [IsAlgClosed L] :
    Nat.card (Ggrp 80 4 3 : Set (ZMod 80 → L)) = 10 ∧
      Nat.card {g : ZMod 80 → L // g ∈ (Ggrp 80 4 3 : Set (ZMod 80 → L)) ∧ tauG 80 4 g = g} = 2 ∧
      (fun g => tauG 80 4 g / g) '' (Ggrp 80 4 3 : Set (ZMod 80 → L)) =
        {g | g ∈ (Ggrp 80 4 3 : Set (ZMod 80 → L)) ∧ g ^ 5 = 1} ∧
      Nat.card {g : ZMod 80 → L // g ∈ (Ggrp 80 4 3 : Set (ZMod 80 → L)) ∧ g ^ 5 = 1} = 5 :=
  Xia.Proofs.rem_4_4_G_proved

/-- Row 18d — Section 5 set-up (s5_twonorms.tex:13-33), algebraically closed `L` of characteristic 3: for each top orbit `O`
(any `ρ ∈ O`, `L = |O|`, `c_O = ρ^{-2L}`), `V_O = {t : t^{3^L} = c_O t}` is closed under addition and has `3^L` elements; a
solution has `ŷ(ρ^{3^k}) = ρ^{2k3^k} t^{3^k}` with `t = ŷ(ρ) ∈ V_O ∖ {0}`; `ŷ(ξ^{-1}) = -1/ŷ(ξ)` on `𝓛_a`; `-ξ = ξ^u`, so
`ξ ↦ -ξ` permutes the orbits; in case A `-ρ = ρ^{q_O}`, in case B `-ρ = ρ^{-q_O}`; for `n = 2^e`, `e ≥ 4`, there is one block,
of case A, with `q_O = q`. -/
theorem sec_5_setup (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type*} [Field L] [CharP L 3] [IsAlgClosed L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L)
    (hω : IsPrimitiveRoot ω n) :
    (∀ O ∈ topOrbits n 3, ∀ ρ ∈ O,
      Nat.card {t : L // t ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * t} = 3 ^ O.card ∧
      (∀ t t' : L, t ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * t →
        t' ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * t' →
        (t + t') ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * (t + t')) ∧
      (∀ y ∈ NFSet n 2, (∀ k : ℕ,
          dftA ω y ((3 : ZMod n) ^ k * ρ) = (ω ^ ρ.val) ^ (2 * k * 3 ^ k) * dftA ω y ρ ^ (3 ^ k)) ∧
        dftA ω y ρ ≠ 0 ∧ dftA ω y ρ ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * dftA ω y ρ) ∧
      negO O ∈ topOrbits n 3 ∧ ρ + half n = (1 + half n) * ρ ∧
      (IsCaseA O → ρ + half n = (3 : ZMod n) ^ (O.card / 2) * ρ) ∧
      (IsCaseB O → ρ + half n = -((3 : ZMod n) ^ (O.card / 2) * ρ))) ∧
    (∀ y ∈ NFSet n 2, ∀ k : ZMod n, Odd k.val → dftA ω y (-k) = -1 / dftA ω y k) ∧
    ∀ e : ℕ, n = 2 ^ e → 4 ≤ e → (blocks n).card = 1 ∧ (blocksA n).card = 1 ∧ (∀ B ∈ blocks n, qO B = qq n) ∧
      (ω ^ (1 : ZMod n).val)⁻¹ ^ (2 * (n / 4)) = -1 ∧ ω ^ ((n / 4) * qq n) = ω ^ (n / 4) ∧
      {t : L | t ^ (3 ^ (n / 4)) = -t} = algebraMap (GaloisField 3 (n / 2)) L '' (Vsp n) :=
  Xia.Proofs.sec_5_setup_of n a nodd hn ha hodd h3 ω hω
    (Xia.Paper.prop_2_4_bij n (Xia.Proofs.H19_even_of hn ha) h3 ω hω)

/-- Row 18e — Theorem 5.1(c) in y-form (s5_twonorms.tex:59-63, :74-77): on solutions the substitution acts on the top data
by `ŷ(ρ) ↦ ŷ(-ρ)` and keeps the `ν`-data `ŷ(ρ)ŷ(-ρ)` (ρ ∈ 𝓛_a); `S`, `f = ŷ|_{μ_{n_odd}}` and the `ν`-data determine the
values of `ŷ` on `μ_m`, and conversely; a non-empty fibre is in bijection, through its top data, with ALL top data having its
`ν`-data. (The form "T is an `F_3`-linear involution of the block parameter space" is row thm_5_1_c_V with thm_5_1_c_V_blocks, (N6).) -/
theorem thm_5_1_c_yform (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) :
    (∀ y ∈ NFSet n 2, ∀ ρ : ZMod n, Odd ρ.val →
      dftA ω (ySubst y) ρ = dftA ω y (ρ + half n) ∧
      dftA ω (ySubst y) ρ * dftA ω (ySubst y) (ρ + half n) = dftA ω y ρ * dftA ω y (ρ + half n)) ∧
    (∀ y ∈ NFSet n 2, ∀ y' ∈ NFSet n 2,
      ((S y = S y' ∧ (∀ k : ZMod n, 2 ^ a ∣ k.val → dftA ω y k = dftA ω y' k) ∧
        ∀ ρ : ZMod n, Odd ρ.val → dftA ω y ρ * dftA ω y (ρ + half n) = dftA ω y' ρ * dftA ω y' (ρ + half n)) ↔
       ∀ k : ZMod n, Even k.val → dftA ω y k = dftA ω y' k)) ∧
    ∀ y ∈ NFSet n 2, ∀ h ∈ topData n 3 2 (1 : L) ω,
      (∀ ρ : ZMod n, Odd ρ.val → h ρ * h (ρ + half n) = dftA ω y ρ * dftA ω y (ρ + half n)) →
      ∃! y' : ZMod n → GaloisField 3 (n / 2), y' ∈ fibre ω y ∧ ∀ ρ : ZMod n, Odd ρ.val → dftA ω y' ρ = h ρ :=
  Xia.Proofs.thm_5_1_c_yform_of n a nodd hn ha hodd h3 ω hω
    (Xia.Paper.prop_2_4_bij n (Xia.Proofs.H19_even_of hn ha) h3 ω hω)

/-- Row 18f — Theorem 5.1(d) and the matching sentences of Theorem B, in y-form (s5_twonorms.tex:68-70;
P10s_main.tex:184-187): on a fibre, the `V_±`-components of a point are read through its top data,
`g_±(ρ) = ŷ(ρ) ± ŷ(-ρ)` (ρ ∈ 𝓛_a; `T` acts by `ŷ(ρ) ↦ ŷ(-ρ)`); then `y_0^-` depends only on `g_+` and `y_1^-` only on `g_-`,
each injectively. (The form with `F_3`-linear maps `𝒴_0, 𝒴_1` on the whole space `V` is row thm_5_1_d_V, (N6).) -/
theorem thm_5_1_d_yform (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2) :
    ∀ y1 ∈ fibre ω y, ∀ y2 ∈ fibre ω y,
      (yMinus n (y1 0) = yMinus n (y2 0) ↔
        ∀ ρ : ZMod n, Odd ρ.val → dftA ω y1 ρ + dftA ω y1 (ρ + half n) = dftA ω y2 ρ + dftA ω y2 (ρ + half n)) ∧
      (yMinus n (y1 1) = yMinus n (y2 1) ↔
        ∀ ρ : ZMod n, Odd ρ.val → dftA ω y1 ρ - dftA ω y1 (ρ + half n) = dftA ω y2 ρ - dftA ω y2 (ρ + half n)) :=
  Xia.Proofs.thm_5_1_d_yform_of n a nodd hn ha hodd h3 ω hω y hy
    (fun ω' hω' hnL z => Xia.Paper.fourier_inversion n (Xia.Proofs.H19_even_of hn ha) ω' hω' hnL z)

/-- Coverage — Figure 1 caption (P10s_main.tex:133-139), y-form, `n ≡ 8 (mod 24)`: in a fibre at most two `V_+`-components
occur at points with `N(y_0) = -1` and at most two `V_-`-components at points with `N(y_1) = -1`; `T` fixes `V_+` and negates
`V_-`; (the solutions in a fibre form one orbit of `⟨T, v ↦ -v⟩`: Cor 5.2). -/
theorem fig1_caption (n : ℕ) [NeZero n] (hn : n % 24 = 8) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L]
    (ω : L) (hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2) :
    let gp : (ZMod n → GaloisField 3 (n / 2)) → ZMod n → L :=
      fun y' ρ => if Odd ρ.val then dftA ω y' ρ + dftA ω y' (ρ + half n) else 0
    let gm : (ZMod n → GaloisField 3 (n / 2)) → ZMod n → L :=
      fun y' ρ => if Odd ρ.val then dftA ω y' ρ - dftA ω y' (ρ + half n) else 0
    (gp '' {y' | y' ∈ fibre ω y ∧ Nm n (y' 0) = -1}).encard ≤ 2 ∧
      (gm '' {y' | y' ∈ fibre ω y ∧ Nm n (y' 1) = -1}).encard ≤ 2 ∧
      ∀ y' ∈ fibre ω y, gp (ySubst y') = gp y' ∧ gm (ySubst y') = -gm y' :=
  Xia.Proofs.fig1_caption_of n hn ω hω y hy
    (fun ω' hω' hnL z => Xia.Paper.fourier_inversion n (Xia.Proofs.H19_even_of24 hn) ω' hω' hnL z)

/-- Row 21d — proof of Theorem 6.2, Step 2 (s6_primes.tex:82-86): for a solution `θ' := ŷ(ξ_0) ≠ 0` and `θ'^{Q_5-1} = -ι_5`;
conversely, for such `θ'`, `t_k := ξ_0^{k5^k} θ'^{5^k}` satisfies (F1_5) along `O` and closes at the wrap, and the values
`-κ/t_k` that (F3_5) puts on `O^{-1}` satisfy (F1_5) there (as `κ^4 = 1`). -/
theorem thm_6_2_step2 (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) (ξ0 : GaloisField 5 n)
    (hξ0 : IsPrimitiveRoot ξ0 n) :
    (∀ y ∈ NF5Set n, dft ξ0 y 1 ≠ 0 ∧ dft ξ0 y 1 ^ (5 ^ (n / 4) - 1) = -ξ0 ^ (n / 4)) ∧
    ∀ θ : GaloisField 5 n, θ ^ (5 ^ (n / 4) - 1) = -ξ0 ^ (n / 4) →
      (∀ k : ℕ, ξ0 ^ ((k + 1) * 5 ^ (k + 1)) * θ ^ (5 ^ (k + 1)) =
        (ξ0 ^ (5 ^ k)) ^ 5 * (ξ0 ^ (k * 5 ^ k) * θ ^ (5 ^ k)) ^ 5) ∧
      (∀ k : ℕ, ξ0 ^ ((k + n / 4) * 5 ^ (k + n / 4)) * θ ^ (5 ^ (k + n / 4)) = ξ0 ^ (k * 5 ^ k) * θ ^ (5 ^ k)) ∧
      (∀ k : ℕ, -kappa n (GaloisField 5 n) / (ξ0 ^ ((k + 1) * 5 ^ (k + 1)) * θ ^ (5 ^ (k + 1))) =
        ((ξ0 ^ (5 ^ k))⁻¹) ^ 5 * (-kappa n (GaloisField 5 n) / (ξ0 ^ (k * 5 ^ k) * θ ^ (5 ^ k))) ^ 5) :=
  Xia.Proofs.thm_6_2_step2_proved n e hne he heo ξ0 hξ0

/-- Row 21e — proof of Theorem 6.2, Step 3 (s6_primes.tex:88-92): if `κ^2 = -1`, `S^2 = κ`, and (F1_5), (F3_5) hold at `ξ`
and `-ξ` (exponent model `x`, `x + n/2`), then `ŷ(η) := ŷ(ξ)ŷ(-ξ)/S` at `η = ξ^2` satisfies (F1_5) (using `S^4 = -1`) and
(F3_5) (`4 ∣ n`, any field). -/
theorem thm_6_2_step3 (n : ℕ) [NeZero n] (h4 : 4 ∣ n) {L : Type*} [Field L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (κ : L) (hκ : κ ^ 2 = -1) (h : ZMod n → L) (s0 : L) (hs : s0 ^ 2 = κ) (x : ZMod n)
    (hF1 : ∀ z ∈ ({x, x + half n} : Set (ZMod n)), h (5 * z) = (ω ^ z.val) ^ 5 * h z ^ 5)
    (hF3 : ∀ z ∈ ({x, x + half n} : Set (ZMod n)), h z * h (-z) = κ * (ω ^ z.val) ^ (n / 2)) :
    h (5 * x) * h (5 * x + half n) / s0 = (ω ^ (2 * x).val) ^ 5 * (h x * h (x + half n) / s0) ^ 5 ∧
      (h x * h (x + half n) / s0) * (h (-x) * h (-x + half n) / s0) = κ * (ω ^ (2 * x).val) ^ (n / 2) :=
  Xia.Proofs.thm_6_2_step3_proved n h4 ω hω κ hκ h s0 hs x hF1 hF3

/-- Row 21f — proof of Theorem 6.2, Step 4 (s6_primes.tex:94-96): (F3_5) at `ι_5` gives `ŷ(ι_5)ŷ(-ι_5) = κ`, so with `S^2 = κ`
the step `j = 1` gives `ŷ(-1) = κ/S = S`; (F3_5) at `1` gives `ŷ(1) = ±n`; (F1_5) at `1` holds as `n^4 = 1` and at `-1` as
`S^4 = -1` (char 5). -/
theorem thm_6_2_step4 (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) {L : Type*} [Field L]
    [CharP L 5] (ω : L) (hω : IsPrimitiveRoot ω n) (h : ZMod n → L) (hF3 : F3r (kappa n L) ω h) (s0 : L)
    (hs : s0 ^ 2 = kappa n L) :
    h ((n / 4 : ℕ) : ZMod n) * h (((n / 4 : ℕ) : ZMod n) + half n) = kappa n L ∧ kappa n L / s0 = s0 ∧
      (h 0 = (n : L) ∨ h 0 = -(n : L)) ∧ h 0 = h 0 ^ 5 ∧ s0 = (ω ^ (half n).val) ^ 5 * s0 ^ 5 :=
  Xia.Proofs.thm_6_2_step4_proved n e hne he heo ω hω h hF3 s0 hs

/-- Link L2 — after Corollary 5.2 (s5_twonorms.tex:88-90): for `n ≡ 8 (mod 24)` with `16 ∣ n` there is no case-B block and the
bound is less than `16 · 3^{n/8}`, compared with `|NF(n)| < 4 · 3^{n/4}`; for `n = 8` (one case-B block, `L = 2`) the bound
`64` exceeds `|NF(8)| = 32`. (Status follows Theorem 4.1, Theorem 5.1(b) and Corollary 5.2.) -/
theorem link_L2 :
    (∀ (n : ℕ) [NeZero n], n % 24 = 8 → 16 ∣ n →
      (blocksB n).card = 0 ∧ 16 * fibreProd n < 16 * 3 ^ (n / 8) ∧ Nat.card (NFSet n 2) < 4 * 3 ^ (n / 4)) ∧
    ((blocksB 8).card = 1 ∧ (∀ B ∈ blocksB 8, blockLen B = 2) ∧ 16 * fibreProd 8 = 64 ∧ Nat.card (NFSet 8 2) = 32) :=
  Xia.Proofs.link_L2_of Xia.Paper.thm_3_1_card Xia.Paper.thm_4_1_count Xia.Paper.cor_5_2

/-- Link L3 — Table 4 (s5_twonorms.tex:93-109): blocks (case: orbit length), `|NF(n)|` and the bound of Corollary 5.2 for
`n = 8, 32, 56, 80, 104`. (Status follows Theorem 4.1, Theorem 5.1 and Corollary 5.2.) -/
theorem link_L3 :
    ((blocksA 8).card = 0 ∧ (blocksB 8).val.map blockLen = {2} ∧ (blocksC 8).card = 0 ∧
      Nat.card (NFSet 8 2) = 32 ∧ 16 * fibreProd 8 = 64) ∧
    ((blocksA 32).val.map blockLen = {8} ∧ (blocksB 32).card = 0 ∧ (blocksC 32).card = 0 ∧
      Nat.card (NFSet 32 2) = 26240 ∧ 16 * fibreProd 32 = 1280) ∧
    ((blocksA 56).card = 0 ∧ (blocksB 56).val.map blockLen = {2, 6, 6} ∧ (blocksC 56).card = 0 ∧
      Nat.card (NFSet 56 2) = 16959488 ∧ 16 * fibreProd 56 = 50176) ∧
    ((blocksA 80).val.map blockLen = {4} ∧ (blocksB 80).card = 0 ∧ (blocksC 80).val.map blockLen = {4, 4} ∧
      Nat.card (NFSet 80 2) = 13107200000 ∧ 16 * fibreProd 80 = 819200) ∧
    ((blocksA 104).card = 0 ∧ (blocksB 104).val.map blockLen = {2} ∧ (blocksC 104).val.map blockLen = {6, 6} ∧
      Nat.card (NFSet 104 2) = 8988257288192 ∧ 16 * fibreProd 104 = 33918976) :=
  Xia.Proofs.link_L3_of Xia.Paper.thm_3_1_card Xia.Paper.thm_4_1_count

/-- Coverage — P10s_main.tex:72-75: for `n = 2` (`p = 7`) and `n = 8` (`p = 73`) the subgroup `H` of
order `n+1` of `F_p^×` (the `h` with `h^{n+1} = 1`) is a planar difference set: every non-zero element of `F_p` is `h - h'`
with `h, h' ∈ H` in exactly one way. -/
theorem intro_planar_2_8 :
    (∀ d : ZMod 7, d ≠ 0 → ∃! hh : ZMod 7 × ZMod 7, hh.1 ^ 3 = 1 ∧ hh.2 ^ 3 = 1 ∧ hh.1 - hh.2 = d) ∧
      (∀ d : ZMod 73, d ≠ 0 → ∃! hh : ZMod 73 × ZMod 73, hh.1 ^ 9 = 1 ∧ hh.2 ^ 9 = 1 ∧ hh.1 - hh.2 = d) :=
  Xia.Proofs.intro_planar_2_8_proved

/-- SUPERSEDED by prop_6_1_X12 / prop_6_1_from_diffset (no such hypotheses: Xia's Lemma 3.5 `hX35`, Lemma 4.1 `hX41`, Thm 3.4(b) `hX34b` are proved in Lean as xia_lemma_3_5, xia_lemma_4_1, xia_thm_3_4b; only Xia's Prop 1.2 `hX12` stays). Row 20 — Proposition 6.1 (s6_primes.tex:17-42), PROVED GIVEN Xia's results (goal A4: projective planes, `r`-adic
characters, Gauss sums and the multiplier theorem are not in Lean's library; each enters as an EXPLICIT hypothesis, worded
as in Xia, arXiv 1707.05486 v7, never stronger):
* `Plane` stands for "there is a non-Desarguesian flag-transitive projective plane of order `n`" (no Lean theory);
* `hX12` = Xia Prop 1.2 (p. 2): a plane gives `v = n^2+n+1` prime, `n > 8` even, `H_{v,n}` a `(v, n+1, 1)`-difference set;
* `hX41` = Xia Lemma 4.1 (p. 13): such a difference set (v prime) has `n ≡ 2 (mod 3)` and `2 ∈ H_{v,n}`;
* `χ` = a multiplicative character of order `n` on `F_p` with values in a field `M` (Xia: an `r`-adic character, `M = ℂ_5`;
  the conclusions below depend only on the exponents, so any `M` with this `χ` is an instance of Xia's setting);
* `hX35` = Xia Lemma 3.5 (pp. 11-12) for `r = 5`, `m = n`, `q = p`: `χ(5) = μ^σ`, `μ` primitive ⇒ `(-1)^σ = ((-1)^{n/2}p / 5)`;
* `hX34b` = Xia Theorem 3.4(b) (pp. 10-11) for `r = 5`, `m = n`, `q = p`: if `H_{p,n}` is a cyclotomic difference set (here
  `λ = 1`), `χ(5) = μ^σ`, `χ(2) = μ^θ`, then some `y ∈ F_{5^{n/gcd(σ,n)}}^n` satisfies `y_{s+σ} = y_s^5` (all `s`),
  `y_s y_{n/2+s} = 1 + (n-1)p`, `∑_t y_t y_{s+t} = n(1-p)`, `∑_t (-1)^t y_t y_{2s-2θ-t} = (y_s + y_{n/2+s}) ∑_t (-1)^t y_t`
  (`s < n/2`).
The paper's deduction (σ_5 odd for every μ, so `χ(5)` is primitive and `σ_5 = 1`; `χ(2) = 1` as `2 ∈ H = ker χ`;
`1 + (n-1)p = n^3`) is what this row proves: for `n = 2^e`, `e ≥ 3` odd, a plane gives a solution of (eq:xia125). -/
theorem prop_6_1 (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) (Plane : Prop)
    (hX12 : Plane → (pp n).Prime ∧ 8 < n ∧ Even n ∧ IsDiffSet (pp n) (Hpow (pp n) n) (n + 1) 1)
    (hX41 : (pp n).Prime → IsDiffSet (pp n) (Hpow (pp n) n) (n + 1) 1 → n % 3 = 2 ∧ (2 : ZMod (pp n)) ∈ Hpow (pp n) n)
    {M : Type*} [Field M] (χ : MulChar (ZMod (pp n)) M) (g : (ZMod (pp n))ˣ)
    (hg : ∀ x : (ZMod (pp n))ˣ, x ∈ Subgroup.zpowers g) (hχg : IsPrimitiveRoot (χ (g : ZMod (pp n))) n)
    (hX35 : ∀ (μ : M) (σ : ℕ), IsPrimitiveRoot μ n → χ 5 = μ ^ σ →
      (-1 : ℤ) ^ σ = legendreSym 5 ((-1) ^ (n / 2) * (pp n : ℤ)))
    (hX34b : IsDiffSet (pp n) (Hpow (pp n) n) (n + 1) 1 → ∀ (μ : M) (σ θ : ℕ), IsPrimitiveRoot μ n →
      χ 5 = μ ^ σ → χ 2 = μ ^ θ →
      ∃ y : ZMod n → GaloisField 5 (n / Nat.gcd σ n),
        L1 5 (σ : ℤ) y ∧ L2 (((1 + (n - 1) * pp n : ℕ) : GaloisField 5 (n / Nat.gcd σ n))) y ∧
        L3 ((n : GaloisField 5 (n / Nat.gcd σ n)) * (1 - (pp n : GaloisField 5 (n / Nat.gcd σ n)))) y ∧
        ∀ s : ZMod n, s.val < n / 2 →
          ∑ t, sgn t * y t * y (2 * s - 2 * (θ : ZMod n) - t) = (y s + y (s + half n)) * S y) :
    Plane → (Xia5Set n).Nonempty :=
  Xia.Proofs.prop_6_1_proved n e hne he heo Plane hX12 hX41 χ g hg hχg hX35 hX34b

/-- Row 11e — equation (eq:top-all-V) (s3_pow2.tex:168-173), `n = 2^e`, `e ≥ 4`: for `ν` with `ν^{q-1} = -1` and every `x ∈ V`,
with `h_x(ξ_0^{3^k}) := ξ_0^{2k3^k} x^{3^k}` and `h_x(ξ_0^{-3^k}) := -ξ_0^{-2k3^k} ν^{-3^k} x^{q3^k}` on `O ∪ O^{-1}`
(`k < m/2`): `n^{-1} ∑ h_x(ξ) = n^{-1} Λ_ν(x + Tx)` and `n^{-1} ∑ h_x(ξ) ξ^{-1} = n^{-1} Λ'_ν(x - Tx)`; and for a parameter
`θ` with `θ^{1+q} = ν`, `h_θ = ŷ` on `O ∪ O^{-1}` (any solution `y` with `ŷ(ξ_0) = θ`). -/
theorem eq_top_all_V (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 4 ≤ e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) (ν : GaloisField 3 (n / 2)) (hν : ν ^ (qq n - 1) = -1) :
    (∀ x ∈ (Vsp n : Set (GaloisField 3 (n / 2))),
      (n : GaloisField 3 (n / 2))⁻¹ * ∑ k ∈ range (n / 4),
          (ξ0 ^ (2 * k * 3 ^ k) * x ^ (3 ^ k) - (ξ0⁻¹) ^ (2 * k * 3 ^ k) * (ν⁻¹) ^ (3 ^ k) * x ^ (qq n * 3 ^ k)) =
        (n : GaloisField 3 (n / 2))⁻¹ * Lam n ξ0 ν (x + Tmap n ξ0 x) ∧
      (n : GaloisField 3 (n / 2))⁻¹ * ∑ k ∈ range (n / 4),
          (ξ0 ^ (2 * k * 3 ^ k) * x ^ (3 ^ k) * (ξ0 ^ (3 ^ k))⁻¹ -
            (ξ0⁻¹) ^ (2 * k * 3 ^ k) * (ν⁻¹) ^ (3 ^ k) * x ^ (qq n * 3 ^ k) * ξ0 ^ (3 ^ k)) =
        (n : GaloisField 3 (n / 2))⁻¹ * Lam' n ξ0 ν (x - Tmap n ξ0 x)) ∧
    ∀ y ∈ NFSet n 2, dft ξ0 y 1 ^ (1 + qq n) = ν → ∀ k : ℕ,
      dft ξ0 y ((3 : ZMod n) ^ k) = ξ0 ^ (2 * k * 3 ^ k) * dft ξ0 y 1 ^ (3 ^ k) ∧
      dft ξ0 y (-(3 : ZMod n) ^ k) = -((ξ0⁻¹) ^ (2 * k * 3 ^ k) * (ν⁻¹) ^ (3 ^ k) * dft ξ0 y 1 ^ (qq n * 3 ^ k)) :=
  Xia.Proofs.eq_top_all_V_proved n e hne he ξ0 hξ0 ν hν

/-! ## Remark 4.4's other printed numbers (claim 17N), two printed facts, number facts added in v1.90 -/

/-- Row rem_4_4_N1 — Remark 4.4 (s4_normfree.tex:168-169): "Here `a = 4` and `n_odd = 5`; ... Over `α = 1` there are two
top orbits of length `4` (one pair), and over `α ≠ 1` eight (four pairs)". Exponent model: `ξ = ω^k` (`k` odd) lies over
`α = ω^{16k}`, so "over `α = 1`" is `16k = 0` in `ℤ/80`; a pair `{O, O^{-1}}` lies over `α = 1` iff all its elements do.
Every top orbit has length `4`. -/
theorem rem_4_4_N1 :
    ((topOrbits 80 3).filter (fun O => ∀ k ∈ O, (16 : ZMod 80) * k = 0)).card = 2 ∧
    ((topOrbits 80 3).filter (fun O => ∀ k ∈ O, (16 : ZMod 80) * k ≠ 0)).card = 8 ∧
    (∀ O ∈ topOrbits 80 3, O.card = 4) ∧
    ((topPairs 80 3).filter (fun P => ∀ k ∈ P.biUnion id, (16 : ZMod 80) * k = 0)).card = 1 ∧
    ((topPairs 80 3).filter (fun P => ∀ k ∈ P.biUnion id, (16 : ZMod 80) * k ≠ 0)).card = 4 :=
  Xia.Proofs.rem_4_4_N1_proved

/-- Row rem_4_4_N2 — Remark 4.4 (s4_normfree.tex:169): "On layer `0`, `μ_5 ∖ {1}` is one orbit of `⟨2⟩ = ⟨3⟩ = (ℤ/5)^×`":
every non-zero residue mod `5` is a power of `2` and a power of `3`; and on `μ_5 ∖ {1}` (exponent model
`layer0' 80 4`), the orbit of every `α` under squaring (`k ↦ 2k`) and under cubing (`k ↦ 3k`) is all of `μ_5 ∖ {1}`. -/
theorem rem_4_4_N2 :
    (∀ x : ZMod 5, x ≠ 0 → (∃ i : ℕ, (2 : ZMod 5) ^ i = x) ∧ ∃ i : ℕ, (3 : ZMod 5) ^ i = x) ∧
    ∀ k ∈ layer0' 80 4, orbit 2 k = layer0' 80 4 ∧ orbit 3 k = layer0' 80 4 :=
  Xia.Proofs.rem_4_4_N2_proved

/-- Row rem_4_4_N3 — Remark 4.4 (s4_normfree.tex:169-170): "`G` consists of the `g` with `g(β) ∈ μ_80`,
`g(β)^{-1} = g(β)^9`" (`G` of Step 5, `β ∈ μ_5 ∖ {1}`): for every `β`, `g ↦ g(β)` is a bijection from `G` onto
`{t : t^80 = 1, t^{-1} = t^9}` (algebraically closed `L` of characteristic 3, as in row rem_4_4_G). -/
theorem rem_4_4_N3 {L : Type*} [Field L] [CharP L 3] [IsAlgClosed L] :
    ∀ β ∈ layer0' 80 4, Set.BijOn (fun g : ZMod 80 → L => g β) (Ggrp 80 4 3 : Set (ZMod 80 → L))
      {t : L | t ^ 80 = 1 ∧ t⁻¹ = t ^ 9} :=
  Xia.Proofs.rem_4_4_N3_proved

/-- Row rem_4_4_N4 — Remark 4.4 (s4_normfree.tex:170-171): "(For `f_0 ∈ G'`, (E2) and (E3) give
`f_0(α)^{10} = α^{-1}` and `τf_0/f_0 = f_0^6`" (`G'` with `σ = 2`, `κ = 1` as in Step 5 of Theorem 4.1; `α = ω^k` runs
over `μ_5 ∖ {1}`; both sides of the second identity are `1` off `μ_5 ∖ {1}`). -/
theorem rem_4_4_N4 {L : Type*} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (hω : IsPrimitiveRoot ω 80) :
    ∀ f0 ∈ (Gprime 80 4 3 2 (1 : L) ω : Set (ZMod 80 → L)),
      (∀ k ∈ layer0' 80 4, f0 k ^ 10 = (ω ^ k.val)⁻¹) ∧ tauG 80 4 f0 / f0 = f0 ^ 6 :=
  Xia.Proofs.rem_4_4_N4_proved ω hω

/-- Row rem_4_4_N5 — Remark 4.4 (s4_normfree.tex:170): "The extendable top data satisfy `P(α)^5 = α^2`,
which holds for half of the `10` possible values of `P(α)`". Reading: a top datum `h ∈ 𝒟` (Step 2, `σ = 2`, `κ = 1`) is
extendable iff some `f ∈ G'` satisfies (E1) `f(α^2) = P(α) f(α)` on `μ_5 ∖ {1}`, `P = P_h` of Step 4 (`Pmap`); this
holds iff `P(α)^5 = α^2` on `μ_5 ∖ {1}`; and for each `α ∈ μ_5 ∖ {1}` the values of `P(α)` over all top data form a set
of `10` elements, exactly `5` of which satisfy `t^5 = α^2`. -/
theorem rem_4_4_N5 {L : Type*} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (hω : IsPrimitiveRoot ω 80) :
    (∀ h ∈ topData 80 3 2 (1 : L) ω,
      (∃ f ∈ (Gprime 80 4 3 2 (1 : L) ω : Set (ZMod 80 → L)), ∀ k ∈ layer0' 80 4, f (2 * k) = Pmap 80 4 h k * f k) ↔
        ∀ k ∈ layer0' 80 4, Pmap 80 4 h k ^ 5 = (ω ^ k.val) ^ 2) ∧
    ∀ k ∈ layer0' 80 4,
      ((fun h => Pmap 80 4 h k) '' (topData 80 3 2 (1 : L) ω)).ncard = 10 ∧
      ((fun h => Pmap 80 4 h k) '' (topData 80 3 2 (1 : L) ω) ∩ {t : L | t ^ 5 = (ω ^ k.val) ^ 2}).ncard = 5 :=
  Xia.Proofs.rem_4_4_N5_proved ω hω

/-- Row rem_4_4_N6 — Remark 4.4 (s4_normfree.tex:172): "Each such top datum extends in `2` ways at `α ≠ 1`, so the
count is `80^5 · 1/2 · 2 · 4 = 4 · 80^5`". Reading: for every top datum with `P(α)^5 = α^2` on `μ_5 ∖ {1}` there are exactly `2`
maps `f ∈ G'` with (E1); the factor `80^5 · 1/2` is the number of such top data (half of `|𝒟| = 80^5`); and the
arithmetic identity. -/
theorem rem_4_4_N6 {L : Type*} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (hω : IsPrimitiveRoot ω 80) :
    (∀ h ∈ topData 80 3 2 (1 : L) ω, (∀ k ∈ layer0' 80 4, Pmap 80 4 h k ^ 5 = (ω ^ k.val) ^ 2) →
      Nat.card {f : ZMod 80 → L // f ∈ (Gprime 80 4 3 2 (1 : L) ω : Set (ZMod 80 → L)) ∧
        ∀ k ∈ layer0' 80 4, f (2 * k) = Pmap 80 4 h k * f k} = 2) ∧
    2 * Nat.card {h : ZMod 80 → L // h ∈ topData 80 3 2 (1 : L) ω ∧
        ∀ k ∈ layer0' 80 4, Pmap 80 4 h k ^ 5 = (ω ^ k.val) ^ 2} = 80 ^ 5 ∧
    (80 : ℚ) ^ 5 * (1 / 2) * 2 * 4 = 4 * 80 ^ 5 :=
  Xia.Proofs.rem_4_4_N6_proved ω hω

/-- Row nit_s2_m — s2_xia.tex:48-49: "Then `m := n/2 ≡ 4 (mod 12)`, so `m/2` is even and
`m ≡ 1 (mod 3)`" (the subsection's standing hypothesis: `n ≡ 8 (mod 24)`). -/
theorem nit_s2_m (n : ℕ) (hn : n % 24 = 8) : (n / 2) % 12 = 4 ∧ Even (n / 2 / 2) ∧ (n / 2) % 3 = 1 :=
  Xia.Proofs.nit_s2_m_proved n hn

/-- Row nit_s4_layers — s4_normfree.tex:11-12, standing hypotheses of Section 4 (`n = 2^a n_odd`, `a ≥ 3`,
`n_odd` odd, `3 ∤ n`): "The top layer is `𝓛_a := {ξ : j(ξ) = a}`, of size `m`, ... Let `Ξ_a` be the set of the `2^{a-1}`
elements of order `2^a` of `μ_{2^a}`." Exponent model: `𝓛_a = topLayer n` (odd `k`); `Ξ_a` = the `k` with `2^a k = 0` and
`2^{a-1} k ≠ 0` (the filter of row thm_6_4_step3b). -/
theorem nit_s4_layers (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n) :
    (topLayer n).card = n / 2 ∧
      (univ.filter (fun k : ZMod n => (2 ^ a : ZMod n) * k = 0 ∧ (2 ^ (a - 1) : ZMod n) * k ≠ 0)).card =
        2 ^ (a - 1) :=
  Xia.Proofs.nit_s4_layers_proved n a nodd hn ha hodd h3

/-- Row rem_4_4_v190 — Remark 4.4 (s4_normfree.tex:168-169; added in v1.90): "`n = 80` is the smallest `n > 8` in Xia's
range with `p` prime (`p = 6481`)" and "`|𝒟| = (3^4-1)^5 = 80^5`" (Xia's range: `n ≡ 8 (mod 24)`, s2_xia.tex:46;
`|𝒟| = ∏_i (3^{L_i}-1) = pairProd 80 3`, as in row rem_4_4). The non-printed witnesses `pp 32 = 7·151`,
`pp 56 = 31·103` are the lemmas H25_pp32, H25_pp56. -/
theorem rem_4_4_v190 :
    (80 % 24 = 8 ∧ (pp 80).Prime ∧ pp 80 = 6481) ∧
    (∀ n : ℕ, 8 < n → n < 80 → n % 24 = 8 → ¬ (pp n).Prime) ∧
    pairProd 80 3 = (3 ^ 4 - 1) ^ 5 ∧ (3 ^ 4 - 1) ^ 5 = 80 ^ 5 :=
  Xia.Proofs.rem_4_4_v190_proved

/-- Row link_L3_v190 — Table 4 caption (s5_twonorms.tex:95; added in v1.90): "Of these five values, only `n = 8` and
`n = 80` make `p = n^2+n+1` prime" (the table's `n = 8, 32, 56, 80, 104`). "A counterexample needs `n ≥ 2·10^11`" (same
line) = CITED (Thas–Zagier), not formalized. The non-printed witnesses `pp 32 = 7·151`,
`pp 56 = 31·103`, `pp 104 = 67·163` are H25_pp32, H25_pp56, H25_pp104. -/
theorem link_L3_v190 :
    ∀ n ∈ ({8, 32, 56, 80, 104} : Finset ℕ), (pp n).Prime ↔ n = 8 ∨ n = 80 :=
  Xia.Proofs.link_L3_v190_proved

/-! ## Section 5's space V: Theorem 5.1(c),(d) and Theorem B in V-form (Defs: Xia/Defs/BlockSpace.lean) -/

/-- Row 18V(c) — Theorem 5.1(c), V-form (s5_twonorms.tex:59-60, :33, :170-186): for the fibre of a solution `y` (ν-data
`ν = ŷ(k)ŷ(k+m)`), `V = Vfib ω ν` is an `F_3`-space (closed under `0`, `+`, `-`; characteristic 3); `T` (shift by `m`) is additive,
an involution, maps `V` to `V` and keeps the ν-datum; on solutions of the fibre `T` is the action of `y ↦ y^{(u)}`; and the
fibre is in bijection, through its top data, with the points of `V` with the fibre's ν-data. -/
theorem thm_5_1_c_V (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2) :
    let ν := nuData (topOf ω y)
    ((0 : ZMod n → L) ∈ Vfib ω ν ∧ (∀ h ∈ Vfib ω ν, ∀ h' ∈ Vfib ω ν, h + h' ∈ Vfib ω ν) ∧
      ∀ h ∈ Vfib ω ν, -h ∈ Vfib ω ν) ∧
    (∀ h h' : ZMod n → L, Tsh (h + h') = Tsh h + Tsh h') ∧ (∀ h : ZMod n → L, Tsh (Tsh h) = h) ∧
    (∀ h ∈ Vfib ω ν, Tsh h ∈ Vfib ω ν ∧ nuData (Tsh h) = nuData h) ∧
    (∀ y' ∈ fibre ω y, topOf ω y' ∈ Vfib ω ν ∧ topOf ω (ySubst y') = Tsh (topOf ω y')) ∧
    Set.InjOn (topOf ω) (fibre ω y) ∧
    topOf ω '' fibre ω y = {h | h ∈ Vfib ω ν ∧ ∀ k : ZMod n, Odd k.val → nuData h k = ν k} :=
  Xia.Proofs.thm_5_1_c_V_proved n a nodd hn ha hodd h3 ω hω y hy

/-- Row 18V(c-blocks) — Theorem 5.1(c), the block parameter spaces (s5_twonorms.tex:24-33, Table 3): `V` is the direct sum of
its block subspaces, each kept by `T`; in the coordinates of the paper (any `ρ = ρ_O ∈ O`; case B with `t_0 = ŷ(ρ)` of the
fibre) the block space is `V_O` (case A), `V_O^2` (case C), `F_{q_O}^2` (case B), and `T` is `t ↦ ι_O t^{q_O}` with
`ι_O = ρ^{L q_O}` and ν-datum `ι_O t^{1+q_O}` (A), the swap `(t, t') ↦ (t', t)` (C), `(x, x') ↦ (δ_O x', x/δ_O)` with
`δ_O = -ρ^{-L q_O} t_0^{-1-q_O}`, keeping `x x'` (B). -/
theorem thm_5_1_c_V_blocks (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2) :
    let ν := nuData (topOf ω y)
    (∀ h ∈ Vfib ω ν, (∀ B ∈ blocks n, restrictBlock B h ∈ VfibBlock ω ν B) ∧ h = ∑ B ∈ blocks n, restrictBlock B h) ∧
    (∀ B ∈ blocks n, ∀ h ∈ VfibBlock ω ν B, Tsh h ∈ VfibBlock ω ν B) ∧
    (∀ B ∈ blocksA n, ∀ O ∈ B, ∀ ρ ∈ O,
      Set.BijOn (fun h : ZMod n → L => h ρ) (VfibBlock ω ν B)
        {t | t ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * t} ∧
      ∀ h ∈ VfibBlock ω ν B, Tsh h ρ = (ω ^ ρ.val) ^ (O.card * qO B) * h ρ ^ qO B ∧
        nuData h ρ = (ω ^ ρ.val) ^ (O.card * qO B) * h ρ ^ (1 + qO B)) ∧
    (∀ B ∈ blocksC n, ∀ O ∈ B, ∀ ρ ∈ O,
      Set.BijOn (fun h : ZMod n → L => (h ρ, h (ρ + half n))) (VfibBlock ω ν B)
        ({t | t ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * t} ×ˢ
          {t | t ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * t}) ∧
      ∀ h ∈ VfibBlock ω ν B, Tsh h ρ = h (ρ + half n) ∧ Tsh h (ρ + half n) = h ρ) ∧
    (∀ B ∈ blocksB n, ∀ O ∈ B, ∀ ρ ∈ O,
      Set.BijOn (fun h : ZMod n → L => (h ρ / topOf ω y ρ, -(topOf ω y ρ * h (-ρ)))) (VfibBlock ω ν B)
        ({x | x ^ qO B = x} ×ˢ {x | x ^ qO B = x}) ∧
      ∀ h ∈ VfibBlock ω ν B,
        Tsh h ρ / topOf ω y ρ = (-((ω ^ ρ.val)⁻¹ ^ (O.card * qO B)) * (topOf ω y ρ)⁻¹ ^ (1 + qO B)) *
            (-(topOf ω y ρ * h (-ρ))) ∧
        -(topOf ω y ρ * Tsh h (-ρ)) = (h ρ / topOf ω y ρ) /
            (-((ω ^ ρ.val)⁻¹ ^ (O.card * qO B)) * (topOf ω y ρ)⁻¹ ^ (1 + qO B)) ∧
        (Tsh h ρ / topOf ω y ρ) * (-(topOf ω y ρ * Tsh h (-ρ))) = (h ρ / topOf ω y ρ) * (-(topOf ω y ρ * h (-ρ)))) :=
  Xia.Proofs.thm_5_1_c_V_blocks_proved n a nodd hn ha hodd h3 ω hω y hy

/-- Coverage — s5_twonorms.tex:145-147: in case B, `δ_O = -ρ^{-L q_O} t_0^{-1-q_O}` lies in
`F_{q_O}` (i.e. `δ_O^{q_O} = δ_O`) for EVERY `t_0 ∈ V_O ∖ {0}` (any `ρ = ρ_O ∈ O`, `L = |O|`, `c_O = ρ^{-2L}`). -/
theorem caseB_delta (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) :
    ∀ B ∈ blocksB n, ∀ O ∈ B, ∀ ρ ∈ O, ∀ t0 : L, t0 ≠ 0 → t0 ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * t0 →
      (-((ω ^ ρ.val)⁻¹ ^ (O.card * qO B)) * t0⁻¹ ^ (1 + qO B)) ^ qO B =
        -((ω ^ ρ.val)⁻¹ ^ (O.card * qO B)) * t0⁻¹ ^ (1 + qO B) :=
  Xia.Proofs.caseB_delta_proved n a nodd hn ha hodd h3 ω hω

/-- Row 18V(d) — Theorem 5.1(d), V-form (s5_twonorms.tex:67-70, proof :170-214): `V = V_+ ⊕ V_-` (eigenspaces of `T`);
`𝒴_0`, `𝒴_1` are additive (`F_3`-linear) with values in `F` on all of `V`, `𝒴_0` is injective on `V_+` and zero on `V_-`, `𝒴_1`
injective on `V_-` and zero on `V_+`; every point of the fibre has `y_0^- = 𝒴_0(v_+)` and `y_1^- = 𝒴_1(v_-)`. -/
theorem thm_5_1_d_V (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2) :
    let ν := nuData (topOf ω y)
    (∀ h ∈ Vfib ω ν, (h + Tsh h) / 2 ∈ VfibPlus ω ν ∧ (h - Tsh h) / 2 ∈ VfibMinus ω ν ∧
      h = (h + Tsh h) / 2 + (h - Tsh h) / 2) ∧
    (∀ hp ∈ VfibPlus ω ν, ∀ hm ∈ VfibMinus ω ν, hp + hm = 0 → hp = 0 ∧ hm = 0) ∧
    (∀ (s : ℕ) (h h' : ZMod n → L), Ycoef ω s (h + h') = Ycoef ω s h + Ycoef ω s h') ∧
    (∀ h ∈ Vfib ω ν, (∃ x : GaloisField 3 (n / 2), algebraMap _ L x = Ycoef ω 0 h) ∧
      ∃ x : GaloisField 3 (n / 2), algebraMap _ L x = Ycoef ω 1 h) ∧
    Set.InjOn (Ycoef ω 0) (VfibPlus ω ν) ∧ Set.InjOn (Ycoef ω 1) (VfibMinus ω ν) ∧
    (∀ h ∈ VfibMinus ω ν, Ycoef ω 0 h = 0) ∧ (∀ h ∈ VfibPlus ω ν, Ycoef ω 1 h = 0) ∧
    ∀ y' ∈ fibre ω y,
      algebraMap _ L (yMinus n (y' 0)) = Ycoef ω 0 ((topOf ω y' + Tsh (topOf ω y')) / 2) ∧
      algebraMap _ L (yMinus n (y' 1)) = Ycoef ω 1 ((topOf ω y' - Tsh (topOf ω y')) / 2) :=
  Xia.Proofs.thm_5_1_d_V_proved n a nodd hn ha hodd h3 ω hω y hy

/-- Row BV — Theorem B, the V sentences (P10s_main.tex:184-187): for `n ≡ 8 (mod 24)` (`σ = 2`), the points of a fibre are
given by top data in the explicit `F_3`-space `V` attached to the fibre (the direct sum of the block parameter spaces); the
substitution acts on the points of the fibre as the `F_3`-linear involution `T` of `V` with eigenspaces `V_±` (fibre to
fibre: row thm_B_subst_fibre); `y_0` is an injective function of the `V_+`-component alone and `y_1` of the
`V_-`-component alone (= rows 18V(c), 18V(c-blocks), 18V(d) at `n ≡ 8 (mod 24)`). -/
theorem thm_B_V (n : ℕ) [NeZero n] (hn : n % 24 = 8) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L)
    (hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2) :
    let ν := nuData (topOf ω y)
(((0 : ZMod n → L) ∈ Vfib ω ν ∧ (∀ h ∈ Vfib ω ν, ∀ h' ∈ Vfib ω ν, h + h' ∈ Vfib ω ν) ∧
      ∀ h ∈ Vfib ω ν, -h ∈ Vfib ω ν) ∧
    (∀ h h' : ZMod n → L, Tsh (h + h') = Tsh h + Tsh h') ∧ (∀ h : ZMod n → L, Tsh (Tsh h) = h) ∧
    (∀ h ∈ Vfib ω ν, Tsh h ∈ Vfib ω ν ∧ nuData (Tsh h) = nuData h) ∧
    (∀ y' ∈ fibre ω y, topOf ω y' ∈ Vfib ω ν ∧ topOf ω (ySubst y') = Tsh (topOf ω y')) ∧
    Set.InjOn (topOf ω) (fibre ω y) ∧
    topOf ω '' fibre ω y = {h | h ∈ Vfib ω ν ∧ ∀ k : ZMod n, Odd k.val → nuData h k = ν k}) ∧
    ((∀ h ∈ Vfib ω ν, (∀ B ∈ blocks n, restrictBlock B h ∈ VfibBlock ω ν B) ∧ h = ∑ B ∈ blocks n, restrictBlock B h) ∧
    (∀ B ∈ blocks n, ∀ h ∈ VfibBlock ω ν B, Tsh h ∈ VfibBlock ω ν B) ∧
    (∀ B ∈ blocksA n, ∀ O ∈ B, ∀ ρ ∈ O,
      Set.BijOn (fun h : ZMod n → L => h ρ) (VfibBlock ω ν B)
        {t | t ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * t} ∧
      ∀ h ∈ VfibBlock ω ν B, Tsh h ρ = (ω ^ ρ.val) ^ (O.card * qO B) * h ρ ^ qO B ∧
        nuData h ρ = (ω ^ ρ.val) ^ (O.card * qO B) * h ρ ^ (1 + qO B)) ∧
    (∀ B ∈ blocksC n, ∀ O ∈ B, ∀ ρ ∈ O,
      Set.BijOn (fun h : ZMod n → L => (h ρ, h (ρ + half n))) (VfibBlock ω ν B)
        ({t | t ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * t} ×ˢ
          {t | t ^ (3 ^ O.card) = (ω ^ ρ.val)⁻¹ ^ (2 * O.card) * t}) ∧
      ∀ h ∈ VfibBlock ω ν B, Tsh h ρ = h (ρ + half n) ∧ Tsh h (ρ + half n) = h ρ) ∧
    (∀ B ∈ blocksB n, ∀ O ∈ B, ∀ ρ ∈ O,
      Set.BijOn (fun h : ZMod n → L => (h ρ / topOf ω y ρ, -(topOf ω y ρ * h (-ρ)))) (VfibBlock ω ν B)
        ({x | x ^ qO B = x} ×ˢ {x | x ^ qO B = x}) ∧
      ∀ h ∈ VfibBlock ω ν B,
        Tsh h ρ / topOf ω y ρ = (-((ω ^ ρ.val)⁻¹ ^ (O.card * qO B)) * (topOf ω y ρ)⁻¹ ^ (1 + qO B)) *
            (-(topOf ω y ρ * h (-ρ))) ∧
        -(topOf ω y ρ * Tsh h (-ρ)) = (h ρ / topOf ω y ρ) /
            (-((ω ^ ρ.val)⁻¹ ^ (O.card * qO B)) * (topOf ω y ρ)⁻¹ ^ (1 + qO B)) ∧
        (Tsh h ρ / topOf ω y ρ) * (-(topOf ω y ρ * Tsh h (-ρ))) = (h ρ / topOf ω y ρ) * (-(topOf ω y ρ * h (-ρ))))) ∧
    ((∀ h ∈ Vfib ω ν, (h + Tsh h) / 2 ∈ VfibPlus ω ν ∧ (h - Tsh h) / 2 ∈ VfibMinus ω ν ∧
      h = (h + Tsh h) / 2 + (h - Tsh h) / 2) ∧
    (∀ hp ∈ VfibPlus ω ν, ∀ hm ∈ VfibMinus ω ν, hp + hm = 0 → hp = 0 ∧ hm = 0) ∧
    (∀ (s : ℕ) (h h' : ZMod n → L), Ycoef ω s (h + h') = Ycoef ω s h + Ycoef ω s h') ∧
    (∀ h ∈ Vfib ω ν, (∃ x : GaloisField 3 (n / 2), algebraMap _ L x = Ycoef ω 0 h) ∧
      ∃ x : GaloisField 3 (n / 2), algebraMap _ L x = Ycoef ω 1 h) ∧
    Set.InjOn (Ycoef ω 0) (VfibPlus ω ν) ∧ Set.InjOn (Ycoef ω 1) (VfibMinus ω ν) ∧
    (∀ h ∈ VfibMinus ω ν, Ycoef ω 0 h = 0) ∧ (∀ h ∈ VfibPlus ω ν, Ycoef ω 1 h = 0) ∧
    ∀ y' ∈ fibre ω y,
      algebraMap _ L (yMinus n (y' 0)) = Ycoef ω 0 ((topOf ω y' + Tsh (topOf ω y')) / 2) ∧
      algebraMap _ L (yMinus n (y' 1)) = Ycoef ω 1 ((topOf ω y' - Tsh (topOf ω y')) / 2)) :=
  Xia.Proofs.thm_B_V_of n hn ω hω y hy
    (fun a nodd hn' ha hodd h3 => thm_5_1_c_V n a nodd hn' ha hodd h3 ω hω y hy)
    (fun a nodd hn' ha hodd h3 => thm_5_1_c_V_blocks n a nodd hn' ha hodd h3 ω hω y hy)
    (fun a nodd hn' ha hodd h3 => thm_5_1_d_V n a nodd hn' ha hodd h3 ω hω y hy)

/-! ## Xia's Lemma 3.5 proved in Lean: row 25 without the Xia hypothesis -/

/-- Xia, Lemma 3.5 (arXiv 1707.05486 v7, pp. 11-12) in the setting of row 25, PROVED in Lean (not a hypothesis): `n = 2^a n_odd`,
`a ≥ 3`, `p = n^2+n+1` prime, `r` prime with `r ∤ pn`, `χ` a character of order `n` on `F_p` (values in any field `M`); for every
primitive `n`-th root `μ'` and integer `σ'` with `χ(r) = μ'^{σ'}`: `(-1)^{σ'} = ((-1)^{n/2} p / r)`. (The binders `μ, hμ, σr, hχr`
are those of row 25 and are not used.) Route: `χ(r)^{n/2} = (r/p)` (Euler), quadratic reciprocity (`p ≡ 1 mod 4`). -/
theorem xia_lemma_3_5 (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a)
    (hodd : Odd nodd) (hp : (pp n).Prime) (hr : ¬ r ∣ pp n * n) {M : Type*} [Field M] (χ : MulChar (ZMod (pp n)) M) (g : (ZMod (pp n))ˣ)
    (hg : ∀ x : (ZMod (pp n))ˣ, x ∈ Subgroup.zpowers g) (hχg : IsPrimitiveRoot (χ (g : ZMod (pp n))) n)
    (μ : M) (hμ : IsPrimitiveRoot μ n) (σr : ℤ) (hχr : χ (r : ZMod (pp n)) = μ ^ σr) :
    ∀ (μ' : M) (σ' : ℤ), IsPrimitiveRoot μ' n → χ (r : ZMod (pp n)) = μ' ^ σ' →
      (-1 : ℤ) ^ σ'.natAbs = legendreSym r ((-1) ^ (n / 2) * (pp n : ℤ)) :=
  Xia.Proofs.xia_lemma_3_5 n a nodd r hn ha hodd hp hr χ g hg hχg μ hμ σr hχr

/-- Row 25a without Xia's Lemma 3.5 as a hypothesis — Corollary 6.5, sign part (s6_primes.tex:152-154): for every prime
`r ∤ pn`, Xia's shift `σ_r` (`χ(r) = μ^{σ_r}`) satisfies `(-1)^{σ_r} = (p/r)`. = `cor_6_5_sign` with `hX35r := xia_lemma_3_5`. -/
theorem cor_6_5_sign_uncond (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a)
    (hodd : Odd nodd) (hp : (pp n).Prime) (hr : ¬ r ∣ pp n * n) {M : Type*} [Field M] (χ : MulChar (ZMod (pp n)) M) (g : (ZMod (pp n))ˣ)
    (hg : ∀ x : (ZMod (pp n))ˣ, x ∈ Subgroup.zpowers g) (hχg : IsPrimitiveRoot (χ (g : ZMod (pp n))) n)
    (μ : M) (hμ : IsPrimitiveRoot μ n) (σr : ℤ) (hχr : χ (r : ZMod (pp n)) = μ ^ σr) :
    (-1 : ℤ) ^ σr.natAbs = legendreSym r (pp n : ℤ) :=
  cor_6_5_sign n a nodd r hn ha hodd hp hr χ g hg hχg μ hμ σr hχr (xia_lemma_3_5 n a nodd r hn ha hodd hp hr χ g hg hχg μ hμ σr hχr)

/-- Row 25b without Xia's Lemma 3.5 as a hypothesis — Corollary 6.5, "Hence" (s6_primes.tex:154-156): for every
`r ≢ -1 (mod 2^a)`, and for every `r` when `n = 2^a`, the norm-free system in characteristic `r` is solvable. = `cor_6_5_solvable` with
`hX35r := xia_lemma_3_5`. -/
theorem cor_6_5_solvable_uncond (n a nodd r : ℕ) [NeZero n] [Fact r.Prime] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a)
    (hodd : Odd nodd) (hp : (pp n).Prime) (hr : ¬ r ∣ pp n * n) {M : Type*} [Field M] (χ : MulChar (ZMod (pp n)) M) (g : (ZMod (pp n))ˣ)
    (hg : ∀ x : (ZMod (pp n))ˣ, x ∈ Subgroup.zpowers g) (hχg : IsPrimitiveRoot (χ (g : ZMod (pp n))) n)
    (μ : M) (hμ : IsPrimitiveRoot μ n) (σr : ℤ) (hχr : χ (r : ZMod (pp n)) = μ ^ σr) :
    r % 2 ^ a ≠ 2 ^ a - 1 ∨ nodd = 1 → (NFrSet n r σr).Nonempty :=
  cor_6_5_solvable n a nodd r hn ha hodd hp hr χ g hg hχg μ hμ σr hχr (xia_lemma_3_5 n a nodd r hn ha hodd hp hr χ g hg hχg μ hμ σr hχr)

/-- SUPERSEDED by prop_6_1_X12 / prop_6_1_from_diffset (no such hypotheses: Xia's Lemma 4.1 `hX41`, Thm 3.4(b) `hX34b` are proved in Lean as xia_lemma_4_1, xia_thm_3_4b). Row 20 without Xia's Lemma 3.5 as a hypothesis — Proposition 6.1 deduction (s6_primes.tex:1-41), PROVED GIVEN Xia's
Prop 1.2 (`hX12`), Lemma 4.1 (`hX41`) and Theorem 3.4(b) (`hX34b`) only: = `prop_6_1` with `hX35` supplied by the Lean proof of
Lemma 3.5 (`xia_lemma_3_5` at `a = e`, `n_odd = 1`, `r = 5`; `p` prime comes from `hX12`). -/
theorem prop_6_1_noX35 (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) (Plane : Prop)
    (hX12 : Plane → (pp n).Prime ∧ 8 < n ∧ Even n ∧ IsDiffSet (pp n) (Hpow (pp n) n) (n + 1) 1)
    (hX41 : (pp n).Prime → IsDiffSet (pp n) (Hpow (pp n) n) (n + 1) 1 → n % 3 = 2 ∧ (2 : ZMod (pp n)) ∈ Hpow (pp n) n)
    {M : Type*} [Field M] (χ : MulChar (ZMod (pp n)) M) (g : (ZMod (pp n))ˣ)
    (hg : ∀ x : (ZMod (pp n))ˣ, x ∈ Subgroup.zpowers g) (hχg : IsPrimitiveRoot (χ (g : ZMod (pp n))) n)
    (hX34b : IsDiffSet (pp n) (Hpow (pp n) n) (n + 1) 1 → ∀ (μ : M) (σ θ : ℕ), IsPrimitiveRoot μ n →
      χ 5 = μ ^ σ → χ 2 = μ ^ θ →
      ∃ y : ZMod n → GaloisField 5 (n / Nat.gcd σ n),
        L1 5 (σ : ℤ) y ∧ L2 (((1 + (n - 1) * pp n : ℕ) : GaloisField 5 (n / Nat.gcd σ n))) y ∧
        L3 ((n : GaloisField 5 (n / Nat.gcd σ n)) * (1 - (pp n : GaloisField 5 (n / Nat.gcd σ n)))) y ∧
        ∀ s : ZMod n, s.val < n / 2 →
          ∑ t, sgn t * y t * y (2 * s - 2 * (θ : ZMod n) - t) = (y s + y (s + half n)) * S y) :
    Plane → (Xia5Set n).Nonempty :=
  fun hP => prop_6_1 n e hne he heo Plane hX12 hX41 χ g hg hχg
    (Xia.Proofs.L10_hX35_of_lemma n e hne he heo (hX12 hP).1 χ g hg hχg) hX34b hP

/-! ## Xia's Lemma 4.1 proved in Lean: row 20 given only Xia's Prop 1.2 and Thm 3.4(b) -/

/-- Xia's Lemma 4.1 (arXiv 1707.05486 v7, p. 13) in our instance, PROVED in Lean: for `n = 2^e` (`e ≥ 3`
odd), if `p = n^2+n+1` is prime and `H_{p,n}` is a `(p, n+1, 1)`-difference set, then `n ≡ 2 (mod 3)` and `2 ∈ H_{p,n}`.
This is, token for token, the hypothesis `hX41` of rows 20 (`prop_6_1`, `prop_6_1_noX35`). The part `2 ∈ H_{p,n}` is
Hall's first multiplier theorem for the multiplier 2 and `λ = 1`, proved by counting (for every even `n ≥ 2`). -/
theorem xia_lemma_4_1 (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) :
    (pp n).Prime → IsDiffSet (pp n) (Hpow (pp n) n) (n + 1) 1 → n % 3 = 2 ∧ (2 : ZMod (pp n)) ∈ Hpow (pp n) n :=
  Xia.Proofs.L10_hX41_proved n e hne he heo

/-- SUPERSEDED by prop_6_1_X12 / prop_6_1_from_diffset (no such hypothesis: Xia's Thm 3.4(b) `hX34b` is proved in Lean as xia_thm_3_4b). Row 20 without Xia's Lemmas 3.5 and 4.1 as hypotheses — Proposition 6.1 deduction (s6_primes.tex:1-41), PROVED GIVEN
Xia's Prop 1.2 (`hX12`) and Theorem 3.4(b) (`hX34b`) only: = `prop_6_1_noX35` with `hX41 := xia_lemma_4_1`. -/
theorem prop_6_1_X12_X34b (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) (Plane : Prop)
    (hX12 : Plane → (pp n).Prime ∧ 8 < n ∧ Even n ∧ IsDiffSet (pp n) (Hpow (pp n) n) (n + 1) 1)
    {M : Type*} [Field M] (χ : MulChar (ZMod (pp n)) M) (g : (ZMod (pp n))ˣ)
    (hg : ∀ x : (ZMod (pp n))ˣ, x ∈ Subgroup.zpowers g) (hχg : IsPrimitiveRoot (χ (g : ZMod (pp n))) n)
    (hX34b : IsDiffSet (pp n) (Hpow (pp n) n) (n + 1) 1 → ∀ (μ : M) (σ θ : ℕ), IsPrimitiveRoot μ n →
      χ 5 = μ ^ σ → χ 2 = μ ^ θ →
      ∃ y : ZMod n → GaloisField 5 (n / Nat.gcd σ n),
        L1 5 (σ : ℤ) y ∧ L2 (((1 + (n - 1) * pp n : ℕ) : GaloisField 5 (n / Nat.gcd σ n))) y ∧
        L3 ((n : GaloisField 5 (n / Nat.gcd σ n)) * (1 - (pp n : GaloisField 5 (n / Nat.gcd σ n)))) y ∧
        ∀ s : ZMod n, s.val < n / 2 →
          ∑ t, sgn t * y t * y (2 * s - 2 * (θ : ZMod n) - t) = (y s + y (s + half n)) * S y) :
    Plane → (Xia5Set n).Nonempty :=
  prop_6_1_noX35 n e hne he heo Plane hX12 (xia_lemma_4_1 n e hne he heo) χ g hg hχg hX34b

/-! ## Xia's Theorem 3.4(b) proved in Lean: row 20 given only Xia's Prop 1.2 -/

/-- Xia's Theorem 3.4(b) (arXiv 1707.05486 v7, pp. 10-11) in our instance (`r = 5`, `m = n = 2^e`, `q = p = n^2+n+1`),
PROVED in Lean. After the colon this is, token for token, the hypothesis `hX34b` of rows 20; the extra binder
`hp : p prime` is supplied by `hX12` where the row is used. Route: `y_t = n·η_t`, `η_t` the Gauss periods over the cosets
of `ker χ` in a field of characteristic 5; the fourth equation is Salié's evaluation of a quadratic Kloosterman sum. -/
theorem xia_thm_3_4b (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) (hp : (pp n).Prime)
    {M : Type*} [Field M] (χ : MulChar (ZMod (pp n)) M) (g : (ZMod (pp n))ˣ)
    (hg : ∀ x : (ZMod (pp n))ˣ, x ∈ Subgroup.zpowers g) (hχg : IsPrimitiveRoot (χ (g : ZMod (pp n))) n) :
    IsDiffSet (pp n) (Hpow (pp n) n) (n + 1) 1 → ∀ (μ : M) (σ θ : ℕ), IsPrimitiveRoot μ n →
      χ 5 = μ ^ σ → χ 2 = μ ^ θ →
      ∃ y : ZMod n → GaloisField 5 (n / Nat.gcd σ n),
        L1 5 (σ : ℤ) y ∧ L2 (((1 + (n - 1) * pp n : ℕ) : GaloisField 5 (n / Nat.gcd σ n))) y ∧
        L3 ((n : GaloisField 5 (n / Nat.gcd σ n)) * (1 - (pp n : GaloisField 5 (n / Nat.gcd σ n)))) y ∧
        ∀ s : ZMod n, s.val < n / 2 →
          ∑ t, sgn t * y t * y (2 * s - 2 * (θ : ZMod n) - t) = (y s + y (s + half n)) * S y :=
  Xia.Proofs.L10_hX34b_proved n e hne he heo hp χ g hg hχg

/-- Support of claim 20 — Proposition 6.1 from the planar difference set onwards (s6_primes.tex:17-42
after Xia's Prop 1.2), PROVED with no Xia hypothesis and no `Plane`: for `n = 2^e` (`e ≥ 3` odd), if `p = n^2+n+1` is prime
and `H_{p,n}` is a `(p, n+1, 1)`-difference set, then Xia's system (eq:xia125) has a solution over `F_{5^n}` (`n = 8`
included). Xia's Lemma 3.5, Lemma 4.1 and Theorem 3.4(b) enter through their Lean proofs (rows xia_lemma_3_5,
xia_lemma_4_1, xia_thm_3_4b); the character data come from `L10_char_data_exists` (values in `ℂ`). -/
theorem prop_6_1_from_diffset (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) (hp : (pp n).Prime)
    (hD : IsDiffSet (pp n) (Hpow (pp n) n) (n + 1) 1) : (Xia5Set n).Nonempty :=
  Xia.Proofs.prop_6_1_from_diffset_proved n e hne he heo hp hD

/-- Row 20 — Proposition 6.1 (s6_primes.tex:17-42), PROVED GIVEN ONLY Xia's Prop 1.2 (`hX12`; the plane is the
uninterpreted `Plane : Prop`): if a finite non-Desarguesian flag-transitive projective plane of order `n = 2^e` (`e ≥ 3`
odd) exists, then Xia's system (eq:xia125) has a solution over `F_{5^n}`. No character binders. = `prop_6_1_from_diffset`
composed with `hX12`. -/
theorem prop_6_1_X12 (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) (Plane : Prop)
    (hX12 : Plane → (pp n).Prime ∧ 8 < n ∧ Even n ∧ IsDiffSet (pp n) (Hpow (pp n) n) (n + 1) 1) :
    Plane → (Xia5Set n).Nonempty :=
  fun hP => prop_6_1_from_diffset n e hne he heo (hX12 hP).1 (hX12 hP).2.2.2

/-! ## Claims added to the paper between v1.70 (first formalized) and v2.70 -/

/-- Row thm_B_subst_fibre — Theorem B (P10s_main.tex:185): "The substitution acts on the points of the fibre as an
`F_3`-linear involution `T` of `V`": `y ↦ y^{(u)}` maps the fibre to itself and is an involution there; the top-data map
`y' ↦ top(y')` is injective from the fibre into `V`, and through it the substitution is `T` (`T` additive, an involution, maps
`V` to `V`; `F_3`-linear as `V` has characteristic 3). Eigenspaces `V_±`: row thm_5_1_d_V. -/
theorem thm_B_subst_fibre (n : ℕ) [NeZero n] (hn : n % 24 = 8) {L : Type*} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2))
    (hy : y ∈ NFSet n 2) :
    let ν := nuData (topOf ω y)
    (∀ y' ∈ fibre ω y, ySubst y' ∈ fibre ω y ∧ ySubst (ySubst y') = y') ∧
    (∀ y' ∈ fibre ω y, topOf ω y' ∈ Vfib ω ν) ∧ Set.InjOn (topOf ω) (fibre ω y) ∧
    (∀ y' ∈ fibre ω y, topOf ω (ySubst y') = Tsh (topOf ω y')) ∧
    (∀ h h' : ZMod n → L, Tsh (h + h') = Tsh h + Tsh h') ∧ (∀ h ∈ Vfib ω ν, Tsh h ∈ Vfib ω ν ∧ Tsh (Tsh h) = h) :=
  Xia.Proofs.thm_B_subst_fibre_proved n hn ω hω y hy

/-- Row thm_B_pow2_V — Theorem B (P10s_main.tex:185): for `n = 2^e`, `e ≥ 5` odd (so `n ≡ 8 (mod 24)`), with
`L = F = F_{3^{n/2}}` and `ω = ξ_0` of order `n`. "The space `V` is `{x ∈ F_{3^{n/2}} : x^{3^{n/4}} = -x}`": `v ↦ v(ξ_0)` (exponent
`1`) is a bijection from `V` onto `Vsp n`; "a point of the fibre is given by `x = ŷ(ξ_0)`": the top data of a point `y'` take
the value `ŷ'(ξ_0)` at `ξ_0`, this value lies in `Vsp n`, and `y' ↦ ŷ'(ξ_0)` is injective on the fibre; "`T(x) = ξ_0^{n/4}
x^{3^{n/8}}`": `(Tv)(ξ_0) = Tmap n ξ_0 (v(ξ_0))` on `V`, and `ŷ^{(u)}(ξ_0) = Tmap n ξ_0 (ŷ(ξ_0))` at the points of the fibre. -/
theorem thm_B_pow2_V (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 5 ≤ e) (heo : Odd e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2) :
    let ν := nuData (topOf ξ0 y)
    Set.BijOn (fun v : ZMod n → GaloisField 3 (n / 2) => v 1) (Vfib ξ0 ν) (Vsp n) ∧
    (∀ y' ∈ fibre ξ0 y, topOf ξ0 y' 1 = dftA ξ0 y' 1 ∧ dftA ξ0 y' 1 ∈ Vsp n) ∧
    Set.InjOn (fun y' : ZMod n → GaloisField 3 (n / 2) => dftA ξ0 y' 1) (fibre ξ0 y) ∧
    (∀ v ∈ Vfib ξ0 ν, Tsh v 1 = Tmap n ξ0 (v 1)) ∧
    ∀ y' ∈ fibre ξ0 y, dftA ξ0 (ySubst y') 1 = Tmap n ξ0 (dftA ξ0 y' 1) :=
  Xia.Proofs.thm_B_pow2_V_full n e hne he heo ξ0 hξ0 y hy

/-- Row thm_B_components — after Theorem B (P10s_main.tex:202-203): "So the first vanishes on `V_-`, where
`T=-1`, and the second on `V_+`, where `T=1`" (the first = the top-layer part of `y_0`, the second = that of `y_1`) and "Hence
the top-layer part of `y_0` alone determines the `V_+`-component, and that of `y_1` the `V_-`-component": `𝒴_1` vanishes on
`V_+` and `𝒴_0` on `V_-`; for `v, v'` in `V`, equal `𝒴_0` gives equal `V_+`-components `(v + Tv)/2`, and equal `𝒴_1` gives
equal `V_-`-components `(v - Tv)/2`. -/
theorem thm_B_components (n : ℕ) [NeZero n] (hn : n % 24 = 8) {L : Type*} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2))
    (hy : y ∈ NFSet n 2) :
    let ν := nuData (topOf ω y)
    (∀ v ∈ VfibPlus ω ν, Ycoef ω 1 v = 0) ∧ (∀ v ∈ VfibMinus ω ν, Ycoef ω 0 v = 0) ∧
    (∀ v ∈ Vfib ω ν, ∀ v' ∈ Vfib ω ν, Ycoef ω 0 v = Ycoef ω 0 v' → (v + Tsh v) / 2 = (v' + Tsh v') / 2) ∧
    ∀ v ∈ Vfib ω ν, ∀ v' ∈ Vfib ω ν, Ycoef ω 1 v = Ycoef ω 1 v' → (v - Tsh v) / 2 = (v' - Tsh v') / 2 :=
  Xia.Proofs.thm_B_components_proved n hn ω hω y hy

/-- Row thm_B_xia_iff — after Theorem B (P10s_main.tex:206): "For every `n ≡ 8 (mod 24)` and `σ = 2`, Xia's system
has a solution if and only if, in some fibre, a `V_+`-component allowed by `Nm(y_0) = -1` and a `V_-`-component allowed by
`Nm(y_1) = -1` add up to a point of the fibre". Fibre of `y ∈ NF`; `v_+ ∈ V_+` is allowed by `N(y_0) = -1` when
`y_0^+ + 𝒴_0(v_+)` (`y_0^+` = the lower-layer part of `y_0`, constant on the fibre) is an `x ∈ F` with `N(x) = -1`; likewise
`v_-` with `y_1`, `𝒴_1`; "a point of the fibre" = the top data of a point. (Also the Figure 1 caption's "A solution of Xia's
system would be a crossing on the curve" (P10s_main.tex:137-138), with sec_2_2_xia_eq.) -/
theorem thm_B_xia_iff (n : ℕ) [NeZero n] (hn : n % 24 = 8) {L : Type*} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) :
    (XiaSet n 2).Nonempty ↔
      ∃ y ∈ NFSet n 2, ∃ vp ∈ VfibPlus ω (nuData (topOf ω y)), ∃ vm ∈ VfibMinus ω (nuData (topOf ω y)),
        (∃ x : GaloisField 3 (n / 2), algebraMap _ L x = algebraMap _ L (yPlus n (y 0)) + Ycoef ω 0 vp ∧ Nm n x = -1) ∧
        (∃ x : GaloisField 3 (n / 2), algebraMap _ L x = algebraMap _ L (yPlus n (y 1)) + Ycoef ω 1 vm ∧ Nm n x = -1) ∧
        vp + vm ∈ topOf ω '' fibre ω y :=
  Xia.Proofs.thm_B_xia_iff_proved n hn ω hω

/-- Row intro_e_pow3 — introduction (P10s_main.tex:84), `n = 2^e`, `p = n^2+n+1 = 2^{2e}+2^e+1`:
"if `e = 3^k m` with `m > 1` and `3 ∤ m`, then `2^{2·3^k}+2^{3^k}+1` is a proper divisor of `p`", so `p` prime gives `e` a power
of `3` (`e ≥ 1`); "for `e = 3^4, …, 3^7`, `p` has a prime factor below `3·10^5`" (`487`, `80191`, `39367`, `209953`, each prime);
"so `e ≥ 3^8` (as `n ≥ 2·10^11` …)": `p` prime and `n ≥ 2·10^11` give `e = 3^k` with `k ≥ 8`. (`n ≥ 2·10^11` is ONLY a
hypothesis here: the Thas–Zagier bound behind it is cited, not formalized.) -/
theorem intro_e_pow3 :
    (∀ e k m : ℕ, e = 3 ^ k * m → 1 < m → ¬ 3 ∣ m →
      (2 ^ (2 * 3 ^ k) + 2 ^ 3 ^ k + 1) ∣ pp (2 ^ e) ∧ 1 < 2 ^ (2 * 3 ^ k) + 2 ^ 3 ^ k + 1 ∧
        2 ^ (2 * 3 ^ k) + 2 ^ 3 ^ k + 1 < pp (2 ^ e)) ∧
    (∀ e : ℕ, 0 < e → (pp (2 ^ e)).Prime → ∃ k : ℕ, e = 3 ^ k) ∧
    (Nat.Prime 487 ∧ 487 ∣ pp (2 ^ 3 ^ 4) ∧ Nat.Prime 80191 ∧ 80191 ∣ pp (2 ^ 3 ^ 5) ∧
      Nat.Prime 39367 ∧ 39367 ∣ pp (2 ^ 3 ^ 6) ∧ Nat.Prime 209953 ∧ 209953 ∣ pp (2 ^ 3 ^ 7) ∧ 209953 < 3 * 10 ^ 5) ∧
    ∀ e : ℕ, (pp (2 ^ e)).Prime → 2 * 10 ^ 11 ≤ 2 ^ e → ∃ k : ℕ, 8 ≤ k ∧ e = 3 ^ k :=
  Xia.Proofs.intro_e_pow3_proved

/-- Row sigma_of_n — s2_xia.tex:17 (proof of Lemma 2.2, s2_xia.tex:35-38): "This `σ` is determined by `n`": for
`8 ∣ n` and `p` prime, any data `χ, g, ϖ, σ` as in row lem_2_2_sigma (any field `M`) give `σ = n / ord(3^{(p-1)/n})` (order in
`F_p`), a number that depends on `n` only, and `σ = gcd(c, n)` for every `c` with `g^c = 3` (the proof's formula). -/
theorem sigma_of_n (n : ℕ) (h8 : 8 ∣ n) (hp : (pp n).Prime) {M : Type*} [Field M] (χ : MulChar (ZMod (pp n)) M)
    (g : (ZMod (pp n))ˣ) (hg : ∀ x : (ZMod (pp n))ˣ, x ∈ Subgroup.zpowers g)
    (hχg : IsPrimitiveRoot (χ (g : ZMod (pp n))) n) (ϖ : M) (hϖ : IsPrimitiveRoot ϖ n) (σ : ℕ) (hσ : σ ∣ n)
    (hσ0 : 0 < σ) (h3 : χ 3 = ϖ ^ σ) :
    σ = n / orderOf ((3 : ZMod (pp n)) ^ ((pp n - 1) / n)) ∧ ∀ c : ℕ, (g : ZMod (pp n)) ^ c = 3 → σ = Nat.gcd c n :=
  Xia.Proofs.sigma_of_n_proved n h8 hp χ g hg hχg ϖ hϖ σ hσ hσ0 h3

/-- Row table4_sigma80 — Table 4 caption (s5_twonorms.tex:95-96; also s2_xia.tex:47 and P10s_main.tex:174):
"For `n = 80` the `σ` of `n` (Section 2) is `10`, not `2`" = row lem_2_2_sigma's setting at `n = 80` (`p = 6481` prime) with
conclusion `σ = 10`. ("so the bound does not apply to a plane of order 80" = AUDIT_NOTES: the bound's rows assume `σ = 2`.) -/
theorem table4_sigma80 {M : Type*} [Field M] (χ : MulChar (ZMod (pp 80)) M) (g : (ZMod (pp 80))ˣ)
    (hg : ∀ x : (ZMod (pp 80))ˣ, x ∈ Subgroup.zpowers g) (hχg : IsPrimitiveRoot (χ (g : ZMod (pp 80))) 80)
    (ϖ : M) (hϖ : IsPrimitiveRoot ϖ 80) (σ : ℕ) (hσ : σ ∣ 80) (hσ0 : 0 < σ) (h3 : χ 3 = ϖ ^ σ) : σ = 10 :=
  Xia.Proofs.table4_sigma80_proved χ g hg hχg ϖ hϖ σ hσ hσ0 h3

/-- Row cor_3_5_fibre — Corollary 3.5(ii) (s3_pow2.tex:133; added in v2.70): "Above each triple `(ν, S, ŷ(1))`, that is, in
each fibre of Theorem B": for `n = 2^e`, `e ≥ 5` odd, with `L = F` and `ω = ξ_0`, two solutions `y, y'` of the norm-free system
lie in the same fibre of Theorem B (equal `ŷ` on the lower layers, Defs `fibre`) if and only if they have the same triple
`(ν, S, ŷ(1)) = (ŷ(ξ_0)^{1+q}, S, ŷ(1))` of row cor_3_5_ii. -/
theorem cor_3_5_fibre (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 5 ≤ e) (heo : Odd e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) (y y' : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2) (hy' : y' ∈ NFSet n 2) :
    y' ∈ fibre ξ0 y ↔
      (dft ξ0 y' 1 ^ (1 + qq n) = dft ξ0 y 1 ^ (1 + qq n) ∧ S y' = S y ∧ dft ξ0 y' 0 = dft ξ0 y 0) :=
  Xia.Proofs.cor_3_5_fibre_proved n e hne he heo ξ0 hξ0 y y' hy hy'

/-- Row thm_6_4_r3 — remark after Theorem 6.4 (s6_primes.tex:148; added in v3.00):
"For `r = 3` and `σ_r` a divisor of `n`, this is Theorem 4.1 with Proposition 4.3": for `3 ∤ pn` and `σ ∣ n`, the norm-free
system in characteristic 3 with shift `σ` IS the norm-free system with shift `σ`: its field `F_{3^{n/gcd(σ,n)}}` is
`F_{3^{n/σ}}`, its equations are exactly those of Definition 2.3 (`n(1-p) = 0` and `n^4 = 1` in `F_3`), and so the two solution
sets are in bijection, with the same count. (Theorem 6.4's sign condition then reads "`σ` even", as `(p/3) = 1`: row
thm_6_4_remarks.) -/
theorem thm_6_4_r3 (n : ℕ) [NeZero n] (hr : ¬ 3 ∣ pp n * n) (σ : ℕ) (hσ : σ ∣ n) :
    n / Int.gcd (σ : ℤ) n = n / σ ∧
    (∀ y : ZMod n → GaloisField 3 (n / Int.gcd (σ : ℤ) n), y ∈ NFrSet n 3 (σ : ℤ) ↔ NormFreeEqs (σ : ℤ) y) ∧
    Nonempty (NFrSet n 3 (σ : ℤ) ≃ NFSet n σ) ∧ Nat.card (NFrSet n 3 (σ : ℤ)) = Nat.card (NFSet n σ) :=
  Xia.Proofs.thm_6_4_r3_proved n hr σ hσ

/-! ## Printed claims added in the last versions of the paper (Figure 2's caption, the introduction, after Theorem B) -/

/-- Row fig2_layers — Figure 2's caption (s4_normfree.tex:72; with rows rem_4_4 and rem_4_4_N1): "The layers of `μ_n` for
`n = 80` (Remark 4.4: `a = 4`, `n_odd = 5`). An element `ξ = ζα` lies in layer `j` when `ζ` has order `2^j`. The top layer has
`40` elements and splits into ten orbits of `ξ ↦ ξ^3`, each of length `4`, in five inverse pairs `{O, O^{-1}}`. The pair with
`α = 1` is a block of case A (`-O = O`), and the four pairs with `α ≠ 1` form two blocks `{O, O^{-1}, -O, -O^{-1}}` of case C
(Table 4). Squaring maps each layer above layer `0` onto the layer below." Exponent model `ξ = ω^k` (Defs `fig2Layer`):
`80 = 2^4·5`; layer sizes `5, 5, 10, 20, 40` (layers `0..4`, as drawn); layer 4 is the tree's `topLayer 80` (odd `k`); ten top
orbits, each of length 4, each with its inverse a top orbit and not its own inverse; five pairs; exactly one case-A block, of
2 orbits, whose elements are the top-layer `k` over `α = 1` (`16k = 0`); no case-B block; exactly two case-C blocks, of 4
orbits each, whose elements are the top-layer `k` over `α ≠ 1`; squaring `ξ ↦ ξ^2` is `k ↦ 2k`. (One pair over `α = 1` and
four over `α ≠ 1` = row rem_4_4_N1; "the right column gives the choices of Table 2, which multiply to `4·80^5`" = row
rem_4_4.) -/
theorem fig2_layers :
    (80 : ℕ) = 2 ^ 4 * 5 ∧
    (fig2Layer 0).card = 5 ∧ (fig2Layer 1).card = 5 ∧ (fig2Layer 2).card = 10 ∧ (fig2Layer 3).card = 20 ∧
      (fig2Layer 4).card = 40 ∧
    fig2Layer 4 = topLayer 80 ∧
    (topOrbits 80 3).card = 10 ∧ (∀ O ∈ topOrbits 80 3, O.card = 4 ∧ inv O ∈ topOrbits 80 3 ∧ inv O ≠ O) ∧
    (topPairs 80 3).card = 5 ∧
    (blocksA 80).val.map Finset.card = {2} ∧
    (blocksA 80).biUnion (fun B => B.biUnion id) = (topLayer 80).filter (fun k => (16 : ZMod 80) * k = 0) ∧
    (blocksB 80).card = 0 ∧
    (blocksC 80).val.map Finset.card = {4, 4} ∧
    (blocksC 80).biUnion (fun B => B.biUnion id) = (topLayer 80).filter (fun k => (16 : ZMod 80) * k ≠ 0) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ 4 → (fig2Layer j).image (fun k => 2 * k) = fig2Layer (j - 1)) :=
  Xia.Proofs.fig2_layers_proved

/-- Link intro_planar_H7 — introduction (P10s_main.tex:74; with row intro_planar_2_8): "For `n = 2` (`H = {1,2,4}` in `F_7`)
and `n = 8` it can": the subgroup `H` of order `n + 1 = 3` of `F_7^×` (the `h` with `h^3 = 1`, as in row intro_planar_2_8)
is `{1, 2, 4}`. -/
theorem intro_planar_H7 : univ.filter (fun h : ZMod 7 => h ^ 3 = 1) = {1, 2, 4} :=
  Xia.Proofs.intro_planar_H7_proved

/-- Row intro_sigma_order — introduction (P10s_main.tex:174; also the proof of Lemma 2.2, s2_xia.tex:37): "Xia's proof fixes
`σ` for each `n` (`n/σ` is the order of `3` in `F_p^×/H`), and we call it the `σ` of `n` (Section 2)". In row sigma_of_n's
setting (same binders: `8 ∣ n`, `p = n^2+n+1` prime, data `χ, g, ϖ, σ` with `χ(3) = ϖ^σ`), with `H` = the `x ∈ F_p^×` with
`x^{n+1} = 1` (the kernel of `x ↦ x^{n+1}`, the subgroup of order `n + 1`, as in row intro_planar_2_8; it is `ker χ`, as
s2_xia.tex:37 says): `3 ≠ 0` in `F_p`, and the class of `3` in `F_p^× ⧸ H` has order `n / σ`. -/
theorem intro_sigma_order (n : ℕ) (h8 : 8 ∣ n) (hp : (pp n).Prime) {M : Type*} [Field M] (χ : MulChar (ZMod (pp n)) M)
    (g : (ZMod (pp n))ˣ) (hg : ∀ x : (ZMod (pp n))ˣ, x ∈ Subgroup.zpowers g)
    (hχg : IsPrimitiveRoot (χ (g : ZMod (pp n))) n) (ϖ : M) (hϖ : IsPrimitiveRoot ϖ n) (σ : ℕ) (hσ : σ ∣ n)
    (hσ0 : 0 < σ) (h3 : χ 3 = ϖ ^ σ) :
    (3 : ZMod (pp n)) ≠ 0 ∧
      ∀ u : (ZMod (pp n))ˣ, (u : ZMod (pp n)) = 3 →
        orderOf (QuotientGroup.mk u :
          (ZMod (pp n))ˣ ⧸ (powMonoidHom (n + 1) : (ZMod (pp n))ˣ →* (ZMod (pp n))ˣ).ker) = n / σ :=
  Xia.Proofs.intro_sigma_order_proved n h8 hp χ g hg hχg ϖ hϖ σ hσ hσ0 h3

/-- Link intro_norm_layers — after Theorem B (P10s_main.tex:198; with row rem_2_6): "we call the sum over the
lower layers the lower-layer part of `y_t` and the sum over the top layer its top-layer part (Remark 2.6). On a fibre the
lower-layer parts of `y_0` and `y_1` are constant, and `Nm(y_j)` is the square of the lower-layer part of `y_j` minus the square
of its top-layer part". Theorem B's setting: `n ≡ 8 (mod 24)`, `σ = 2`, `y` a solution of the norm-free system, `ŷ` computed
in `L ⊇ F` with `ω` a primitive `n`-th root of unity (exponent model: lower layers `μ_{n/2}` = even `k`, top layer = odd
`k`). The lower-layer part of `y_t` is `n^{-1} ∑_{k even} ŷ(ω^k) ω^{-kt}`, and it is `y_t^+` of Remark 2.6; the top-layer part
is `𝒴_t` of the top data (`Ycoef`, as in rows thm_B_components, thm_B_xia_iff), and it is `y_t^-`; then
`Nm(y_t) = (lower-layer part)^2 - (top-layer part)^2` for every `t` (so for `t = 0, 1`); and every point `y'` of the fibre of
`y` has the same lower-layer parts as `y`. -/
theorem intro_norm_layers (n : ℕ) [NeZero n] (hn : n % 24 = 8) {L : Type*} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2))
    (hy : y ∈ NFSet n 2) :
    (∀ t : ZMod n, algebraMap _ L (yPlus n (y t)) =
        (n : L)⁻¹ * ∑ k ∈ univ.filter (fun k : ZMod n => Even k.val), dftA ω y k * ((ω ^ k.val)⁻¹) ^ t.val) ∧
    (∀ t : ZMod n, algebraMap _ L (yMinus n (y t)) = Ycoef ω t.val (topOf ω y)) ∧
    (∀ t : ZMod n, algebraMap _ L (Nm n (y t)) =
        ((n : L)⁻¹ * ∑ k ∈ univ.filter (fun k : ZMod n => Even k.val), dftA ω y k * ((ω ^ k.val)⁻¹) ^ t.val) ^ 2 -
          Ycoef ω t.val (topOf ω y) ^ 2) ∧
    (∀ y' ∈ fibre ω y, ∀ t : ZMod n, yPlus n (y' t) = yPlus n (y t)) :=
  Xia.Proofs.intro_norm_layers_proved n hn ω hω y hy

/-! ## NOT stated in Lean (with reasons) — wave 1
(N1) Thm 2.1 (s2_xia.tex:9) and the introduction's cited results (Kantor; Thas–Zagier; Jungnickel–Vedder; Feit; Ho–Pott;
     Gordon–Mills–Welch): cited, about projective planes - no projective-plane theory in Lean's library (goal A4).
     The paper says "By Theorem 2.1 and its proof in [10], to exclude the planes of order n it suffices to prove that (1) has no
     solution for this n and the σ of n" (s2_xia.tex:17-18): Thm 2.1 and its proof are NOT stated and no row
     assumes them; the σ of Xia's proof (`χ(3) = ϖ^σ`, s2_xia.tex:15-17) enters only as binders (lem_2_2_sigma, sigma_of_n,
     table4_sigma80). Scope/status sentences, not claims: "Our results do not exclude any of these orders" (P10s_main.tex:84);
     Figure 1's "Whether one exists for some `n > 8` is open" (P10s_main.tex:138).
(N2) Rem 2.5 (s2_xia.tex:109): a shape analogy with Gauss-sum laws; no mathematical claim.
(N3) Rem 3.6(c), the closing sentence of Rem 3.6(b) and s6_primes.tex:103-105: remarks on where hypotheses are used.
(N4) Prop 6.1 (s6_primes.tex:17-42): row 20 = prop_6_1 (PROVED GIVEN Xia's results); its arithmetic is row 20a.
(N5) Thm 3.1 Step 5 and Thm 6.2 Step 5 (the counts): covered by the theorems' own rows (thm_3_1_card, thm_6_2).
(N6) Section 5's space V IS stated (Xia/Defs/BlockSpace.lean) and its sentences are rows
     thm_5_1_c_V, thm_5_1_c_V_blocks, caseB_delta, thm_5_1_d_V, thm_B_V (section "Section 5's space V" above). The y-form
     rows thm_5_1_c_yform, thm_5_1_d_yform, fig1_caption stay. For n = 2^e the explicit V, T, Lambda of Section 3.2 are
     thm_3_4_a-d, cor_3_5_i/ii, intro_conic_not_product.
-/

end Xia.Paper
