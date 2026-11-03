# AUDIT_NOTES — the Lean proof of "Xia's equations for the Higman–McLaughlin (1961) conjecture"

Every row of `Xia/Paper/Statements.lean` is one of: a printed claim of the paper; one part of a claim with several parts
(plus a row for the printed conjunction); a named step of a printed proof; a coverage row for a number or a sentence of the
text; one of Xia's results proved in our setting (section E); or a weaker form kept and marked SUPERSEDED (section I). These notes record the choices a reader needs to judge that the Lean statements
say what the paper says. `AUDIT.md` lists every row and every printed claim with the status that Lean itself reports.

## 0. Status
- All 134 rows of `Xia/Paper/Statements.lean` are proved. Lean reports only the standard axioms `propext`,
  `Classical.choice`, `Quot.sound`; the sources contain no `axiom` and no `sorry`. Rows: 127 PROVED, 7 PROVED GIVEN
  (the given hypotheses are named results of Xia, section E), 0 OPEN.
- Printed claims (`CLAIM_MAP.tsv`; a claim counts once, with its strongest proved form): 53 = 48 PROVED + 1 PROVED GIVEN
  (Proposition 6.1, given only Xia's Proposition 1.2) + 4 lines that restate two cited results, which are quoted and not
  formalized (section F). Not counted, as they make no mathematical claim: Remark 2.5 (an analogy with Gauss sums), the
  remarks on where hypotheses are used (note N3 in Statements), the introduction's account of cited work (Kantor, Feit,
  Jungnickel and Vedder, Ho and Pott, K. Thas, Gordon, Mills and Welch, Thas and Zagier; P10s_main.tex:72-80), which reports
  results of other papers, and the scope sentences "Our results do not exclude any of
  these orders" and "Whether one exists for some n > 8 is open" (Figure 1).
- The built tree was re-checked by seven kernel checks (`scripts/kernel_replay.sh`): Lean's own checker `leanchecker`
  (olean replay of every module; on an export also in paranoid mode) and the independent checkers lean4lean, nanoda,
  con-leche and con-ron. The files in this folder differ from the checked ones in comments only.
- Pointers `file:line` are lines of the TeX sources (P10s_main.tex, s2_xia.tex, ..., s6_primes.tex) of version 2.70 of
  the paper.

## A. The exponent model of the n-th roots of unity
The paper works with functions on `μ_n` (the n-th roots of unity in an algebraically closed field of characteristic r).
Lean indexes them by exponents: for a primitive n-th root `ω` in ANY field `L` (with an algebra map from the coefficient
field), `h k` stands for `ŷ(ω^k)`, `k ∈ ℤ/n`. Dictionary: `ξ^3 ↔ 3k`, `ξ^{-1} ↔ -k`, `-ξ ↔ k + n/2`, `-1 ↔ n/2`, top layer
(elements of order divisible by 2^a) `↔` odd `k`, `μ_m ↔` even `k`, layer 0 (`μ_{n_odd}`) `↔` multiples of `2^a`.
Rows quantify over every such `(L, ω)` (13 rows whose proof needs it require `L` algebraically closed, and then hold for
every algebraically closed such `L`; some rows take `ω` in the coefficient field itself); this is at least as strong as the
paper's single algebraic closure. Characters may take values in any field (Xia uses ℂ_3).

## B. Route differences (the Lean proof differs from the paper's proof; the statement does not)
- (B1) `prop_4_3_odd`, `thm_6_4_i`, `prop_6_6_i` (no solution for the wrong sign): proved by the direct route
  `S^2 = Σ sgn(s) R(s)` and `S^r = (-1)^σ S` (Frobenius), the argument of Xia's Lemma 3.5, instead of the Fourier route.
- (B2) `thm_6_4_step1` (`-1 ∈ ⟨r⟩ mod 2^a` only if `r ≡ -1`): proved via Euler's criterion and the 2-adic order.
- (B3) Theorem 3.1 (`thm_3_1_bij`): the inverse map is the unique fixed point of one recursion on the transform, which
  packages the paper's step-by-step reconstruction.
- (B4) Section 5's space V: `thm_5_1_d_V` proves "values in F" from (F1) and k ↦ 3k permuting ℤ/n, with no case split over
  the cases A/B/C, and the injectivity from Fourier inversion; `thm_5_1_c_V` gets the image equality from Proposition 2.4
  and `thm_5_1_c_yform`.

## C. Claims summarized, not given rows
- (C1) Tables 2 and 3 summarize proved statements; they have no separate rows.
- (C2) Numeric instances in the text (Remark 4.4, the bounds after Corollaries 3.5 and 5.2, Table 4) are coverage rows
  (`rem_4_4`, `rem_4_4_N1` ... `rem_4_4_N6`, `link_L1`, `link_L2`, `link_L3`, `link_L3_v190`, `table4_sigma80`).

## D. Section 5: the y-form and the space V
- The y-form rows (explicit maps on solutions, counts, orbit statements) are `thm_5_1_*_yform`, `fig1_caption` and others
  of claim 18. Equations eq:8e-A / eq:8e-B are covered by `sec_5_setup`.
- V is stated as the image of the paper's V under its injective F_3-linear map v ↦ top_v (formal top functions,
  `Xia/Defs/BlockSpace.lean`), T = the shift by m. The paper's block coordinates (V_O, F_q^2, V_O^2) and its formulas for T
  are the row `thm_5_1_c_V_blocks`; these bijections also check the definition. "V_O has dimension L" is stated as
  |V_O| = 3^L (`sec_5_setup`), which is equivalent for a finite F_3-space.
- In this model "T preserves the ν-datum" holds by definition; the paper's content (case A: ι_O^{1+q} c_O = 1; case B:
  T preserves x x') is in the formulas of `thm_5_1_c_V_blocks`. "δ_O ∈ F_{q_O} for every t_0" (s5_twonorms.tex:145-147)
  is the row `caseB_delta`.
- Theorem B in V-form: `thm_B_V`, `thm_B_subst_fibre` (the substitution maps a fibre to itself and acts there as T),
  `thm_B_pow2_V` (the explicit V and T for n = 2^e), and after the theorem `thm_B_components`, `thm_B_xia_iff`.
  In `thm_B_xia_iff`, an eigencomponent v_+ ∈ V_+ is "allowed by N(y_0) = -1" when y_0^+ + 𝒴_0(v_+) is an x ∈ F with
  N(x) = -1, where y_0^+ (the lower-layer part of y_0) is constant on the fibre; likewise for v_- and y_1.

## E. Xia's results used as explicit hypotheses (never axioms)
- Row `prop_6_1`: hypotheses `hX12` (Xia, Proposition 1.2), `hX41` (Lemma 4.1), `hX35` (Lemma 3.5, r = 5), `hX34b`
  (Theorem 3.4(b), r = 5); the plane is an uninterpreted `Plane : Prop`. Rows `cor_6_5_sign`, `cor_6_5_solvable`,
  `cor_6_5`: hypothesis `hX35r` (Lemma 3.5 for r), tied to a character `χ` of order n. These rows are "PROVED GIVEN
  <hypothesis>", never plain PROVED, and they are superseded (section I).
- Xia's Lemma 3.5 in our setting (8 | n) is PROVED in Lean (`xia_lemma_3_5`), so `cor_6_5_sign_uncond` and
  `cor_6_5_solvable_uncond` carry no Xia hypothesis. Caveat: Xia's Lemma 3.5 as stated (only "m even"; Xia's m is the order of the
  character, our n) is false for m ≡ 2 (mod 4) (m = 2, q = 5, r = 3 gives χ(3) = (3/5) = -1, σ odd, but (-5/3) = +1); every use here has 8 | n.
- Xia's Lemma 4.1 in our instance (n = 2^e, e ≥ 3 odd) is PROVED (`xia_lemma_4_1`): n ≡ 2 (mod 3) is elementary, and
  "2 ∈ H_{p,n}" is Hall's first multiplier theorem for the multiplier 2 and λ = 1, proved by counting.
- Xia's Theorem 3.4(b) in our instance is PROVED (`xia_thm_3_4b`): y_t = n·(Gauss period over a coset of ker χ) in a field
  of characteristic 5; the fourth equation is Salié's evaluation of a quadratic Kloosterman sum. Hence
  `prop_6_1_from_diffset` (from the planar difference set onwards, no Xia hypothesis) and `prop_6_1_X12` (it composed
  with `hX12`).
- Xia's Proposition 1.2 stays a hypothesis: it rests on Kantor's classification of flag-transitive planes (which uses the
  classification of finite simple groups) and on Thas and Zagier; `Plane` is uninterpreted.
- Xia's σ (fixed in the proof of his Theorem 1.3, χ(3) = ϖ^σ) enters only as binders: `lem_2_2_sigma`, `sigma_of_n`
  ("this σ is determined by n"), `table4_sigma80` (σ = 10 for n = 80).

## F. Cited, not formalized
- Theorem 2.1 = Xia's Theorem 1.3(b) (a plane gives a solution of the system, with n in Xia's range): about projective
  planes, which are not in Lean's library. Census lines 1, P2b (s2_xia.tex:46, first part) and S2c (s2_xia.tex:17-18)
  restate it. No row assumes it.
- "A counterexample needs n ≥ 2·10^11" (Table 4 caption; Thas and Zagier): census line L3c. Where the paper uses this bound
  (e ≥ 3^8 in the introduction, row `intro_e_pow3`), `n ≥ 2·10^11` is a hypothesis of the row.

## G. Unused or stronger-than-needed hypotheses (statements kept as printed; never false)
`caseAB_even` (uses only 8 | n), `thm_6_2_sets` (`heo` unused), `thm_6_4_step3` (`hodd` unused), `intro_conic_not_product`
(`heo` unused), `thm_4_1_step2` (`hodd`), `sec_6_3_fourier` (the `r ∤ p` part of `hr`, `hodd`), `xia_lemma_3_5`.

## H. Claims added between the first formalized text (v1.70) and the final text
New rows: `thm_B_subst_fibre`, `thm_B_pow2_V`, `thm_B_components`, `thm_B_xia_iff`, `intro_e_pow3`, `sigma_of_n`,
`table4_sigma80`, `cor_3_5_fibre` (Corollary 3.5(ii): "above each triple (ν, S, ŷ(1)), that is, in each fibre of
Theorem B"), and earlier `rem_4_4_v190`, `link_L3_v190`, `link_L1` (n = 128). All other edits were wording; no earlier
row's statement changed. "So the bound does not apply to a plane of order 80" (Table 4): the bound's rows assume σ = 2,
and `table4_sigma80` shows σ = 10 for n = 80.

## I. Superseded rows (kept)
Each docstring starts "SUPERSEDED by ...": `prop_6_1`, `prop_6_1_noX35`, `prop_6_1_X12_X34b` (superseded by `prop_6_1_X12`
and `prop_6_1_from_diffset`), and `cor_6_5_sign`, `cor_6_5_solvable`, `cor_6_5` (superseded by `cor_6_5_sign_uncond`,
`cor_6_5_solvable_uncond`). They are kept so that every form the paper's argument passes through stays checked.

## J. Build hygiene
The build prints one warning: Lake's notice that `Xia/Defs/System.lean` imports Mathlib without the `module` keyword (kept:
the module system would make declarations private by default). Linter switches: `linter.unusedSectionVars false` in 22
files and `linter.unusedVariables false` in 2; no other `set_option` (no trust or debug option) anywhere.
