/- Xia/Proofs/Rem44.lean — proofs of the rows rem_4_4_N1, rem_4_4_N2, rem_4_4_N3, rem_4_4_N4, rem_4_4_N5, rem_4_4_N6 and 4 more of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry
import Xia.Defs.Layer0
import Xia.Proofs.Links
import Xia.Proofs.Thm41Steps57
import Xia.Proofs.Thm41Steps26
import Xia.Proofs.Thm41

namespace Xia.Proofs

open Xia Finset

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## 0. Constants of `n = 80` -/

theorem H25_hn : (80 : ℕ) = 2 ^ 4 * 5 := by norm_num

theorem H25_hodd : Odd (5 : ℕ) := by decide

theorem H25_h3 : ¬ 3 ∣ (80 : ℕ) := by decide

theorem H25_three80 : ((3 : ℕ) : ZMod 80) ^ 4 = 1 := by decide

theorem H25_layer_facts : ∀ k ∈ layer0' 80 4, 3 * k ∈ layer0' 80 4 ∧ 3 * (3 * k) = -k ∧
    3 * (3 * (3 * k)) = 2 * k ∧ (16 : ZMod 80) * k = k := by
  decide +kernel

/-! ## 1. Row rem_4_4_N1 — the top orbits over `α = 1` and over `α ≠ 1` -/

/-- Row rem_4_4_N1 — Remark 4.4 (s4_normfree.tex:161-162, v1.70): "Here `a = 4`, `n_odd = 5`. Over `α = 1` there are two
top orbits of length `4` (one pair), and over `α ≠ 1` eight (four pairs)". Exponent model: `ξ = ω^k` (`k` odd) lies over
`α = ω^{16k}`, so "over `α = 1`" is `16k = 0` in `ℤ/80`; a pair `{O, O^{-1}}` lies over `α = 1` iff all its elements do.
Every top orbit has length `4`. -/
theorem rem_4_4_N1_proved :
    ((topOrbits 80 3).filter (fun O => ∀ k ∈ O, (16 : ZMod 80) * k = 0)).card = 2 ∧
    ((topOrbits 80 3).filter (fun O => ∀ k ∈ O, (16 : ZMod 80) * k ≠ 0)).card = 8 ∧
    (∀ O ∈ topOrbits 80 3, O.card = 4) ∧
    ((topPairs 80 3).filter (fun P => ∀ k ∈ P.biUnion id, (16 : ZMod 80) * k = 0)).card = 1 ∧
    ((topPairs 80 3).filter (fun P => ∀ k ∈ P.biUnion id, (16 : ZMod 80) * k ≠ 0)).card = 4 := by
  rw [H18_topPairs_eq 4 (by norm_num) H25_three80, H18_topOrbits_eq 4 (by norm_num) H25_three80]
  have hlen : ∀ k ∈ topLayer 80, (H18_cOrb 80 4 k).card = 4 := by decide +kernel
  refine ⟨by decide +kernel, by decide +kernel, ?_, by decide +kernel, by decide +kernel⟩
  intro O hO
  obtain ⟨k, hk, rfl⟩ := mem_image.mp hO
  exact hlen k hk

/-! ## 2. Row rem_4_4_N2 — `⟨2⟩ = ⟨3⟩ = (ℤ/5)^×`, one orbit on layer 0 -/

theorem H25_orbit2_eq (k : ZMod 80) (hk : (16 : ZMod 80) * k = k) :
    orbit 2 k = (range 4).image (fun i => ((2 : ℕ) : ZMod 80) ^ i * k) := by
  have hper : ∀ j : ℕ, (16 : ZMod 80) ^ j * k = k := by
    intro j
    induction j with
    | zero => rw [pow_zero, one_mul]
    | succ j ih => rw [pow_succ, mul_assoc, hk, ih]
  ext x
  rw [H6_mem_orbit, mem_image]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨i % 4, mem_range.mpr (Nat.mod_lt _ (by norm_num)), ?_⟩
    conv_rhs => rw [← Nat.mod_add_div i 4, pow_add, pow_mul, mul_assoc,
      show ((2 : ℕ) : ZMod 80) ^ 4 = 16 by decide, hper]
  · rintro ⟨i, -, rfl⟩
    exact ⟨i, rfl⟩

/-- Row rem_4_4_N2 — Remark 4.4 (s4_normfree.tex:162, v1.70): "On layer `0`, `⟨2⟩ = ⟨3⟩ = (ℤ/5)^×` is one orbit":
every non-zero residue mod `5` is a power of `2` and a power of `3`; and on `μ_5 ∖ {1}` (exponent model
`layer0' 80 4`), the orbit of every `α` under squaring (`k ↦ 2k`) and under cubing (`k ↦ 3k`) is all of `μ_5 ∖ {1}`. -/
theorem rem_4_4_N2_proved :
    (∀ x : ZMod 5, x ≠ 0 → (∃ i : ℕ, (2 : ZMod 5) ^ i = x) ∧ ∃ i : ℕ, (3 : ZMod 5) ^ i = x) ∧
    ∀ k ∈ layer0' 80 4, orbit 2 k = layer0' 80 4 ∧ orbit 3 k = layer0' 80 4 := by
  refine ⟨?_, ?_⟩
  · have h : ∀ x : ZMod 5, x ≠ 0 →
        (∃ i ∈ range 4, (2 : ZMod 5) ^ i = x) ∧ ∃ i ∈ range 4, (3 : ZMod 5) ^ i = x := by decide
    intro x hx
    obtain ⟨⟨i, -, hi⟩, ⟨j, -, hj⟩⟩ := h x hx
    exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  · have hdec : ∀ k ∈ layer0' 80 4, (range 4).image (fun i => ((2 : ℕ) : ZMod 80) ^ i * k) = layer0' 80 4 ∧
        H18_cOrb 80 4 k = layer0' 80 4 := by decide +kernel
    intro k hk
    rw [H25_orbit2_eq k (H25_layer_facts k hk).2.2.2, H18_orbit_eq 4 (by norm_num) H25_three80 k]
    exact hdec k hk

/-! ## 3. Row rem_4_4_N3 — `G` is parametrized by `g(β) ∈ μ_80` with `g(β)^{-1} = g(β)^9` -/

section N80

variable {L : Type*} [Field L]

theorem H25_memS (t : L) : (t ^ 80 = 1 ∧ t⁻¹ = t ^ 9) ↔ t ^ 10 = 1 := by
  constructor
  · rintro ⟨h80, h9⟩
    have ht : t ≠ 0 := by rintro rfl; norm_num at h80
    rw [show t ^ 10 = t ^ 9 * t by ring, ← h9, inv_mul_cancel₀ ht]
  · intro h10
    refine ⟨by rw [show t ^ 80 = (t ^ 10) ^ 8 by ring, h10, one_pow], ?_⟩
    exact (eq_inv_of_mul_eq_one_left (by rw [show t ^ 9 * t = t ^ 10 by ring]; exact h10)).symm

theorem H25_B16 :
    Set.BijOn (fun g : ZMod 80 → L => g 16) (Ggrp 80 4 3 : Set (ZMod 80 → L)) {t : L | t ^ 10 = 1} :=
  ⟨fun g hg => (H12_G80_eq g hg).1, fun g hg g' hg' h => H12_G80_ext hg hg' h,
    fun t ht => ⟨H12_gen t, H12_gen_mem t ht, H12_gen16 t⟩⟩

theorem H25_cube : Set.BijOn (fun t : L => t ^ 3) {t : L | t ^ 10 = 1} {t : L | t ^ 10 = 1} := by
  refine ⟨fun t (ht : t ^ 10 = 1) => ?_, fun t (ht : t ^ 10 = 1) s (hs : s ^ 10 = 1) (h : t ^ 3 = s ^ 3) => ?_,
    fun s (hs : s ^ 10 = 1) => ⟨s ^ 7, ?_, ?_⟩⟩
  · show (t ^ 3) ^ 10 = 1
    rw [show (t ^ 3) ^ 10 = (t ^ 10) ^ 3 by ring, ht, one_pow]
  · calc t = (t ^ 10) ^ 2 * t := by rw [ht]; ring
      _ = (t ^ 3) ^ 7 := by ring
      _ = (s ^ 3) ^ 7 := by rw [h]
      _ = (s ^ 10) ^ 2 * s := by ring
      _ = s := by rw [hs]; ring
  · show (s ^ 7) ^ 10 = 1
    rw [show (s ^ 7) ^ 10 = (s ^ 10) ^ 7 by ring, hs, one_pow]
  · show (s ^ 7) ^ 3 = s
    calc (s ^ 7) ^ 3 = (s ^ 10) ^ 2 * s := by ring
      _ = s := by rw [hs]; ring

theorem H25_bij_at (β : ZMod 80) (hβ : β ∈ layer0' 80 4) :
    Set.BijOn (fun g : ZMod 80 → L => g β) (Ggrp 80 4 3 : Set (ZMod 80 → L)) {t : L | t ^ 10 = 1} := by
  have B := H25_B16 (L := L)
  have C := H25_cube (L := L)
  rw [H12_X80_iff] at hβ
  rcases hβ with rfl | rfl | rfl | rfl
  · exact B
  · refine (C.comp (C.comp (C.comp B))).congr fun g hg => ?_
    have e := congrFun (H12_G80_eq g hg).2 32
    rw [H12_gen32] at e
    show ((g 16 ^ 3) ^ 3) ^ 3 = g 32
    rw [e]; ring
  · refine (C.comp B).congr fun g hg => ?_
    have e := congrFun (H12_G80_eq g hg).2 48
    rw [H12_gen48] at e
    show g 16 ^ 3 = g 48
    rw [e]
  · refine (C.comp (C.comp B)).congr fun g hg => ?_
    have e := congrFun (H12_G80_eq g hg).2 64
    rw [H12_gen64] at e
    show (g 16 ^ 3) ^ 3 = g 64
    rw [e]; ring

end N80

/-- Row rem_4_4_N3 — Remark 4.4 (s4_normfree.tex:162-163, v1.70): "`G` consists of the `g` with `g(β) ∈ μ_80`,
`g(β)^{-1} = g(β)^9`" (`G` of Step 5, `β ∈ μ_5 ∖ {1}`): for every `β`, `g ↦ g(β)` is a bijection from `G` onto
`{t : t^80 = 1, t^{-1} = t^9}` (algebraically closed `L` of characteristic 3, as in row rem_4_4_G). -/
theorem rem_4_4_N3_proved {L : Type*} [Field L] [CharP L 3] [IsAlgClosed L] :
    ∀ β ∈ layer0' 80 4, Set.BijOn (fun g : ZMod 80 → L => g β) (Ggrp 80 4 3 : Set (ZMod 80 → L))
      {t : L | t ^ 80 = 1 ∧ t⁻¹ = t ^ 9} := by
  intro β hβ
  have hS : {t : L | t ^ 80 = 1 ∧ t⁻¹ = t ^ 9} = {t : L | t ^ 10 = 1} := Set.ext fun t => H25_memS t
  rw [hS]
  exact H25_bij_at β hβ

/-! ## 4. Row rem_4_4_N4 — `f_0(α)^{10} = α^{-1}` and `τf_0/f_0 = f_0^6` -/

section Gp

variable {L : Type*} [Field L]

theorem H25_pow_val_mul {M : Type*} [Monoid M] {x : M} (hx : x ^ 80 = 1) (c k : ZMod 80) :
    x ^ (c * k).val = (x ^ k.val) ^ c.val := by
  rw [ZMod.val_mul, ← pow_eq_pow_mod _ hx, mul_comm, pow_mul]

theorem H25_val3 : (3 : ZMod 80).val = 3 := rfl

theorem H25_w5 {ω : L} (hω1 : ω ^ 80 = 1) {k : ZMod 80} (hk : k ∈ layer0' 80 4) : (ω ^ k.val) ^ 5 = 1 := by
  obtain ⟨j, hj⟩ := (H12_mem_X.mp hk).1
  rw [← pow_mul, hj, show 2 ^ 4 * j * 5 = 80 * j by ring, pow_mul, hω1, one_pow]

/-- For `f ∈ G'` and `α = ω^k ∈ μ_5 ∖ {1}`: `f(α)^{10} α = 1` and `f(α^2) = f(α)^7` (from (E2), (E3)). -/
theorem H25_Gp_vals {ω : L} (hω1 : ω ^ 80 = 1) {f : ZMod 80 → L}
    (hf : f ∈ (Gprime 80 4 3 2 (1 : L) ω : Set (ZMod 80 → L))) {k : ZMod 80} (hk : k ∈ layer0' 80 4) :
    f k ^ 10 * ω ^ k.val = 1 ∧ f (2 * k) = f k ^ 7 := by
  obtain ⟨h1, -⟩ := (H12_memGp H25_hn (by norm_num) hω1).mp hf
  obtain ⟨hk3, hk9, hk27, -⟩ := H25_layer_facts k hk
  have hk9m : 3 * (3 * k) ∈ layer0' 80 4 := (H25_layer_facts _ hk3).1
  have h5 : (ω ^ k.val) ^ 5 = 1 := H25_w5 hω1 hk
  have hv3 : ω ^ (3 * k).val = (ω ^ k.val) ^ 3 := by rw [H25_pow_val_mul hω1, H25_val3]
  have hv9 : ω ^ (3 * (3 * k)).val = (ω ^ k.val) ^ 9 := by
    rw [H25_pow_val_mul hω1, H25_val3, hv3, ← pow_mul]
  have eB : f (3 * k) = (ω ^ k.val) ^ 6 * f k ^ 3 := (h1 k hk).1
  have eC : f (3 * (3 * k)) = ((ω ^ k.val) ^ 3) ^ 6 * f (3 * k) ^ 3 := by rw [(h1 _ hk3).1, hv3]
  have eD : f (3 * (3 * (3 * k))) = ((ω ^ k.val) ^ 9) ^ 6 * f (3 * (3 * k)) ^ 3 := by
    rw [(h1 _ hk9m).1, hv9]
  have hinv : f k * f (3 * (3 * k)) = 1 := by rw [hk9]; exact (h1 k hk).2
  rw [eC, eB] at hinv
  have h10 : f k ^ 10 * ω ^ k.val = 1 := by
    calc f k ^ 10 * ω ^ k.val = ((ω ^ k.val) ^ 5) ^ 7 * (f k ^ 10 * ω ^ k.val) := by rw [h5]; ring
      _ = f k * (((ω ^ k.val) ^ 3) ^ 6 * ((ω ^ k.val) ^ 6 * f k ^ 3) ^ 3) := by ring
      _ = 1 := hinv
  refine ⟨h10, ?_⟩
  rw [← hk27, eD, eC, eB]
  calc ((ω ^ k.val) ^ 9) ^ 6 * (((ω ^ k.val) ^ 3) ^ 6 * ((ω ^ k.val) ^ 6 * f k ^ 3) ^ 3) ^ 3
      = ((ω ^ k.val) ^ 5) ^ 32 * (f k ^ 10 * ω ^ k.val) ^ 2 * f k ^ 7 := by ring
    _ = f k ^ 7 := by rw [h5, h10]; ring

theorem H25_pow30 {ω : L} (hω1 : ω ^ 80 = 1) {f : ZMod 80 → L}
    (hf : f ∈ (Gprime 80 4 3 2 (1 : L) ω : Set (ZMod 80 → L))) {k : ZMod 80} (hk : k ∈ layer0' 80 4) :
    f k ^ 30 = (ω ^ k.val) ^ 2 := by
  have h10 := (H25_Gp_vals hω1 hf hk).1
  have h5 := H25_w5 hω1 hk
  calc f k ^ 30 = f k ^ 30 * (ω ^ k.val) ^ 5 := by rw [h5, mul_one]
    _ = (f k ^ 10 * ω ^ k.val) ^ 3 * (ω ^ k.val) ^ 2 := by ring
    _ = (ω ^ k.val) ^ 2 := by rw [h10, one_pow, one_mul]

end Gp

/-- Row rem_4_4_N4 — Remark 4.4 (s4_normfree.tex:163-164, v1.70): "for `f_0 ∈ G'`, (E2) and (E3) give
`f_0(α)^{10} = α^{-1}` and `τf_0/f_0 = f_0^6`" (`G'` with `σ = 2`, `κ = 1` as in Step 5 of Theorem 4.1; `α = ω^k` runs
over `μ_5 ∖ {1}`; both sides of the second identity are `1` off `μ_5 ∖ {1}`). -/
theorem rem_4_4_N4_proved {L : Type*} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (hω : IsPrimitiveRoot ω 80) :
    ∀ f0 ∈ (Gprime 80 4 3 2 (1 : L) ω : Set (ZMod 80 → L)),
      (∀ k ∈ layer0' 80 4, f0 k ^ 10 = (ω ^ k.val)⁻¹) ∧ tauG 80 4 f0 / f0 = f0 ^ 6 := by
  have hω1 : ω ^ 80 = 1 := hω.pow_eq_one
  intro f0 hf0
  refine ⟨fun k hk => eq_inv_of_mul_eq_one_left (H25_Gp_vals hω1 hf0 hk).1, ?_⟩
  funext x
  rw [Pi.div_apply, Pi.pow_apply]
  by_cases hx : x ∈ layer0' 80 4
  · have hne : f0 x ≠ 0 := H12_Gp_ne H25_hn (by norm_num) hω1 hf0 x
    rw [H12_tau_mem f0 hx, (H25_Gp_vals hω1 hf0 hx).2, div_eq_iff hne]
    ring
  · rw [H12_tau_nmem f0 hx, ((H12_memGp H25_hn (by norm_num) hω1).mp hf0).2 x hx]
    simp

/-! ## 5. Rows rem_4_4_N5, rem_4_4_N6 — the extendable top data -/

section Ext

variable {L : Type*} [Field L]

/-- `P/f_0^6 ∈ G` for `P, f_0 ∈ G'`. -/
theorem H25_quot_mem {ω : L} (hω1 : ω ^ 80 = 1) (hω0 : ω ≠ 0) {P f0 : ZMod 80 → L}
    (hP : P ∈ (Gprime 80 4 3 2 (1 : L) ω : Set (ZMod 80 → L)))
    (hf0 : f0 ∈ (Gprime 80 4 3 2 (1 : L) ω : Set (ZMod 80 → L))) :
    P / f0 ^ 6 ∈ (Ggrp 80 4 3 : Set (ZMod 80 → L)) := by
  obtain ⟨hP1, hP2⟩ := (H12_memGp H25_hn (by norm_num) hω1).mp hP
  obtain ⟨hf1, hf2⟩ := (H12_memGp H25_hn (by norm_num) hω1).mp hf0
  rw [H12_memG]
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · have hw0 : ω ^ k.val ≠ 0 := pow_ne_zero _ hω0
    have h5 := H25_w5 hω1 hk
    simp only [Pi.div_apply, Pi.pow_apply]
    refine ⟨?_, ?_⟩
    · rw [(hP1 k hk).1, (hf1 k hk).1]
      have e : ((ω ^ k.val) ^ 6 * f0 k ^ 3) ^ 6 = (ω ^ k.val) ^ 6 * (f0 k ^ 6) ^ 3 := by
        calc ((ω ^ k.val) ^ 6 * f0 k ^ 3) ^ 6 = ((ω ^ k.val) ^ 5) ^ 6 * ((ω ^ k.val) ^ 6 * (f0 k ^ 6) ^ 3) := by
              ring
          _ = (ω ^ k.val) ^ 6 * (f0 k ^ 6) ^ 3 := by rw [h5]; ring
      rw [e, mul_div_mul_left _ _ (pow_ne_zero 6 hw0), div_pow]
    · have e1 : P (-k) * P k = 1 := by rw [mul_comm]; exact (hP1 k hk).2
      have e2 : f0 (-k) * f0 k = 1 := by rw [mul_comm]; exact (hf1 k hk).2
      rw [div_mul_div_comm, ← mul_pow, e1, e2, one_pow, div_one]
  · simp [Pi.div_apply, hP2 k hk, hf2 k hk]

/-- Sufficiency: if `P ∈ G'` has `P(α)^5 = α^2` at `α = ω^16`, some `f ∈ G'` satisfies (E1). -/
theorem H25_ext [CharP L 3] [IsAlgClosed L] {ω : L} (hω : IsPrimitiveRoot ω 80) {P : ZMod 80 → L}
    (hP : P ∈ (Gprime 80 4 3 2 (1 : L) ω : Set (ZMod 80 → L)))
    (h16 : P 16 ^ 5 = (ω ^ (16 : ZMod 80).val) ^ 2) :
    ∃ f ∈ (Gprime 80 4 3 2 (1 : L) ω : Set (ZMod 80 → L)), ∀ k ∈ layer0' 80 4, f (2 * k) = P k * f k := by
  have hω1 : ω ^ 80 = 1 := hω.pow_eq_one
  have hω0 : ω ≠ 0 := hω.ne_zero (by norm_num)
  obtain ⟨f0, hf0⟩ := H12_Gp_nonempty H25_hn (by norm_num) H25_hodd H25_h3 hω
  rw [H12_E1_iff H25_hn (by norm_num) hω0 hω1 P f0 hP hf0]
  have hg1G := H25_quot_mem hω1 hω0 hP hf0
  have hg15 : (P / f0 ^ 6) ^ 5 = 1 := by
    rw [(H12_G80_eq _ hg1G).2]
    apply H12_gen_pow5
    simp only [Pi.div_apply, Pi.pow_apply]
    rw [div_pow, show (f0 16 ^ 6) ^ 5 = f0 16 ^ 30 by ring, h16, H25_pow30 hω1 hf0 H12_m16,
      div_self (pow_ne_zero 2 (pow_ne_zero _ hω0))]
  obtain ⟨g, hg, hgg⟩ : P / f0 ^ 6 ∈ (fun g => tauG 80 4 g / g) '' (Ggrp 80 4 3 : Set (ZMod 80 → L)) := by
    rw [(rem_4_4_G_proved (L := L)).2.2.1]; exact ⟨hg1G, hg15⟩
  have hgg' : tauG 80 4 g / g = P / f0 ^ 6 := hgg
  refine ⟨g, hg, ?_⟩
  rw [hgg', (rem_4_4_N4_proved ω hω f0 hf0).2]
  funext k
  have hne : f0 k ^ 6 ≠ 0 := pow_ne_zero 6 (H12_Gp_ne H25_hn (by norm_num) hω1 hf0 k)
  simp only [Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
  rw [mul_comm, div_mul_cancel₀ _ hne]

/-- Necessity: (E1) for some `f ∈ G'` forces `P(α) = f(α)^6`, hence `P(α)^5 = α^2` on `μ_5 ∖ {1}`. -/
theorem H25_nec {ω : L} (hω1 : ω ^ 80 = 1) {P : ZMod 80 → L}
    (hex : ∃ f ∈ (Gprime 80 4 3 2 (1 : L) ω : Set (ZMod 80 → L)), ∀ k ∈ layer0' 80 4, f (2 * k) = P k * f k) :
    ∀ k ∈ layer0' 80 4, P k ^ 5 = (ω ^ k.val) ^ 2 := by
  obtain ⟨f, hf, hE1⟩ := hex
  intro k hk
  have hne : f k ≠ 0 := H12_Gp_ne H25_hn (by norm_num) hω1 hf k
  have e : P k = f k ^ 6 := by
    have h1 := hE1 k hk
    rw [(H25_Gp_vals hω1 hf hk).2] at h1
    apply mul_right_cancel₀ hne
    rw [← h1]; ring
  rw [e, show (f k ^ 6) ^ 5 = f k ^ 30 by ring]
  exact H25_pow30 hω1 hf hk

/-- `#{t : t^d = c} = d` for `c ≠ 0` in an algebraically closed field with `d ≠ 0` in it. -/
theorem H25_card_roots_c [IsAlgClosed L] (d : ℕ) (hd : (d : L) ≠ 0) {c : L} (hc : c ≠ 0) :
    {t : L | t ^ d = c}.ncard = d := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero (fun h => hd (by rw [h, Nat.cast_zero]))
  obtain ⟨t0, ht0⟩ := IsAlgClosed.exists_pow_nat_eq c hd0
  have ht0' : t0 ≠ 0 := by
    rintro rfl
    rw [zero_pow hd0.ne'] at ht0
    exact hc ht0.symm
  rw [← Nat.card_coe_set_eq]
  refine (Nat.card_congr ?_).trans (H12_card_roots d hd)
  exact
    { toFun := fun t => ⟨t.1 / t0, by
        have h1 : t.1 ^ d = c := t.2
        rw [div_pow, h1, ht0, div_self hc]⟩
      invFun := fun u => ⟨u.1 * t0, by
        show (u.1 * t0) ^ d = c
        rw [mul_pow, u.2, one_mul, ht0]⟩
      left_inv := fun t => Subtype.ext (div_mul_cancel₀ _ ht0')
      right_inv := fun u => Subtype.ext (mul_div_cancel_right₀ _ ht0') }

theorem H25_D_nonempty [CharP L 3] [IsAlgClosed L] {ω : L} (hω : IsPrimitiveRoot ω 80) :
    (topData 80 3 2 (1 : L) ω).Nonempty := by
  have h := (thm_4_1_step2_proved 80 4 5 H25_hn (by norm_num) H25_hodd H25_h3 ω hω).1
  rw [H18_n80_pp] at h
  apply Set.nonempty_of_ncard_ne_zero
  rw [← Nat.card_coe_set_eq, h]
  norm_num

theorem H25_Pmap_mem {ω : L} (hω : IsPrimitiveRoot ω 80) {h : ZMod 80 → L}
    (hh : h ∈ topData 80 3 2 (1 : L) ω) : Pmap 80 4 h ∈ (Gprime 80 4 3 2 (1 : L) ω : Set (ZMod 80 → L)) :=
  H16_Pmap_mem H25_hn (by norm_num) H25_hodd H25_h3 hω even_two h hh

/-- As the top data vary, `P(α)` runs over the `10` roots of `t^{10} = α^{-1}` (Steps 6, 7). -/
theorem H25_image [CharP L 3] [IsAlgClosed L] {ω : L} (hω : IsPrimitiveRoot ω 80) {k : ZMod 80}
    (hk : k ∈ layer0' 80 4) :
    (fun h => Pmap 80 4 h k) '' (topData 80 3 2 (1 : L) ω) = {t : L | t ^ 10 = (ω ^ k.val)⁻¹} := by
  have hω1 : ω ^ 80 = 1 := hω.pow_eq_one
  have hω0 : ω ≠ 0 := hω.ne_zero (by norm_num)
  apply Set.Subset.antisymm
  · rintro _ ⟨h, hh, rfl⟩
    exact eq_inv_of_mul_eq_one_left (H25_Gp_vals hω1 (H25_Pmap_mem hω hh) hk).1
  · rintro t (ht : t ^ 10 = (ω ^ k.val)⁻¹)
    obtain ⟨h0, hh0⟩ := H25_D_nonempty hω
    have hP0 := H25_Pmap_mem hω hh0
    have ht0 : Pmap 80 4 h0 k ^ 10 = (ω ^ k.val)⁻¹ :=
      eq_inv_of_mul_eq_one_left (H25_Gp_vals hω1 hP0 hk).1
    have hne0 : Pmap 80 4 h0 k ≠ 0 := H12_Gp_ne H25_hn (by norm_num) hω1 hP0 k
    have hu : (t / Pmap 80 4 h0 k) ^ 10 = 1 := by
      rw [div_pow, ht, ht0, div_self (inv_ne_zero (pow_ne_zero _ hω0))]
    obtain ⟨g, hg, hgk⟩ := (H25_bij_at k hk).2.2 hu
    have hgk' : g k = t / Pmap 80 4 h0 k := hgk
    obtain ⟨lam, hlam, hlamP⟩ :=
      (thm_4_1_step6_proved 80 4 5 H25_hn (by norm_num) H25_hodd H25_h3 (L := L)).2.2 hg
    refine ⟨lam * h0, H16_topData_mul lam h0 hlam hh0, ?_⟩
    show Pmap 80 4 (lam * h0) k = t
    rw [H16_Pmap_mul, Pi.mul_apply, hlamP, hgk', div_mul_cancel₀ _ hne0]

end Ext

/-- Row rem_4_4_N5 — Remark 4.4 (s4_normfree.tex:163-165, v1.70): "The extendable top data satisfy `P(α)^5 = α^2` ...,
which holds for half of the `10` possible values of `P(α)`". Reading: a top datum `h ∈ 𝒟` (Step 2, `σ = 2`, `κ = 1`) is
extendable iff some `f ∈ G'` satisfies (E1) `f(α^2) = P(α) f(α)` on `μ_5 ∖ {1}`, `P = P_h` of Step 4 (`Pmap`); this
holds iff `P(α)^5 = α^2` on `μ_5 ∖ {1}`; and for each `α ∈ μ_5 ∖ {1}` the values of `P(α)` over all top data form a set
of `10` elements, exactly `5` of which satisfy `t^5 = α^2`. -/
theorem rem_4_4_N5_proved {L : Type*} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (hω : IsPrimitiveRoot ω 80) :
    (∀ h ∈ topData 80 3 2 (1 : L) ω,
      (∃ f ∈ (Gprime 80 4 3 2 (1 : L) ω : Set (ZMod 80 → L)), ∀ k ∈ layer0' 80 4, f (2 * k) = Pmap 80 4 h k * f k) ↔
        ∀ k ∈ layer0' 80 4, Pmap 80 4 h k ^ 5 = (ω ^ k.val) ^ 2) ∧
    ∀ k ∈ layer0' 80 4,
      ((fun h => Pmap 80 4 h k) '' (topData 80 3 2 (1 : L) ω)).ncard = 10 ∧
      ((fun h => Pmap 80 4 h k) '' (topData 80 3 2 (1 : L) ω) ∩ {t : L | t ^ 5 = (ω ^ k.val) ^ 2}).ncard = 5 := by
  have hω1 : ω ^ 80 = 1 := hω.pow_eq_one
  have hω0 : ω ≠ 0 := hω.ne_zero (by norm_num)
  refine ⟨fun h hh => ⟨fun hex => H25_nec hω1 hex,
    fun hall => H25_ext hω (H25_Pmap_mem hω hh) (hall 16 H12_m16)⟩, ?_⟩
  intro k hk
  rw [H25_image hω hk]
  have hw0 : ω ^ k.val ≠ 0 := pow_ne_zero _ hω0
  have h5 := H25_w5 hω1 hk
  have hsub : {t : L | t ^ 5 = (ω ^ k.val) ^ 2} ⊆ {t : L | t ^ 10 = (ω ^ k.val)⁻¹} := by
    rintro t (ht : t ^ 5 = (ω ^ k.val) ^ 2)
    show t ^ 10 = (ω ^ k.val)⁻¹
    apply eq_inv_of_mul_eq_one_left
    calc t ^ 10 * ω ^ k.val = (t ^ 5) ^ 2 * ω ^ k.val := by ring
      _ = (ω ^ k.val) ^ 5 := by rw [ht]; ring
      _ = 1 := h5
  rw [Set.inter_eq_right.mpr hsub]
  exact ⟨H25_card_roots_c 10 (H12_two_ne 10 (by decide)) (inv_ne_zero hw0),
    H25_card_roots_c 5 (H12_two_ne 5 (by decide)) (pow_ne_zero 2 hw0)⟩

section Count

variable {L : Type*} [Field L]

/-- Half of the top data are extendable: `2 · #{h ∈ 𝒟 : P_h(α)^5 = α^2 on μ_5 ∖ {1}} = |𝒟| = 80^5`. -/
theorem H25_count [CharP L 3] [IsAlgClosed L] {ω : L} (hω : IsPrimitiveRoot ω 80) :
    2 * Nat.card {h : ZMod 80 → L // h ∈ topData 80 3 2 (1 : L) ω ∧
        ∀ k ∈ layer0' 80 4, Pmap 80 4 h k ^ 5 = (ω ^ k.val) ^ 2} = 80 ^ 5 := by
  have hω1 : ω ^ 80 = 1 := hω.pow_eq_one
  have hω0 : ω ≠ 0 := hω.ne_zero (by norm_num)
  have hstep2 := thm_4_1_step2_proved 80 4 5 H25_hn (by norm_num) H25_hodd H25_h3 ω hω
  -- the criterion at the single point `α = ω^16`
  have hiff : ∀ h ∈ topData 80 3 2 (1 : L) ω,
      (∀ k ∈ layer0' 80 4, Pmap 80 4 h k ^ 5 = (ω ^ k.val) ^ 2) ↔
        Pmap 80 4 h 16 ^ 5 = (ω ^ (16 : ZMod 80).val) ^ 2 :=
    fun h hh => ⟨fun hall => hall 16 H12_m16, fun h16 => H25_nec hω1 (H25_ext hω (H25_Pmap_mem hω hh) h16)⟩
  -- `P_h(ω^16)^5 = ± (ω^16)^2`
  have hdich : ∀ h ∈ topData 80 3 2 (1 : L) ω, Pmap 80 4 h 16 ^ 5 = (ω ^ (16 : ZMod 80).val) ^ 2 ∨
      Pmap 80 4 h 16 ^ 5 = -(ω ^ (16 : ZMod 80).val) ^ 2 := by
    intro h hh
    have h10 := (H25_Gp_vals hω1 (H25_Pmap_mem hω hh) H12_m16).1
    have h5 := H25_w5 hω1 H12_m16
    rw [← sq_eq_sq_iff_eq_or_eq_neg]
    calc (Pmap 80 4 h 16 ^ 5) ^ 2 = Pmap 80 4 h 16 ^ 10 * (ω ^ (16 : ZMod 80).val) ^ 5 := by rw [h5]; ring
      _ = (Pmap 80 4 h 16 ^ 10 * ω ^ (16 : ZMod 80).val) * (ω ^ (16 : ZMod 80).val) ^ 4 := by ring
      _ = ((ω ^ (16 : ZMod 80).val) ^ 2) ^ 2 := by rw [h10]; ring
  -- `-x ≠ x` for `x ≠ 0` (characteristic 3)
  have h2 : (2 : L) ≠ 0 := by
    have := H12_two_ne (L := L) 2 (by decide)
    rwa [Nat.cast_ofNat] at this
  have hneg_ne : -(ω ^ (16 : ZMod 80).val) ^ 2 ≠ (ω ^ (16 : ZMod 80).val) ^ 2 := by
    intro h
    have hx : (2 : L) * (ω ^ (16 : ZMod 80).val) ^ 2 = 0 := by linear_combination -h
    rcases mul_eq_zero.mp hx with h' | h'
    · exact h2 h'
    · exact pow_ne_zero 2 (pow_ne_zero _ hω0) h'
  -- a homogeneous datum `l1` with `P_{l1} = -1` on `μ_5 ∖ {1}`
  have hg1 : H12_gen (-1 : L) ∈ (Ggrp 80 4 3 : Set (ZMod 80 → L)) := H12_gen_mem (-1) (by norm_num)
  obtain ⟨l1, hl1, hl1P⟩ :=
    (thm_4_1_step6_proved 80 4 5 H25_hn (by norm_num) H25_hodd H25_h3 (L := L)).2.2 hg1
  have hl1i : l1⁻¹ ∈ (topData0 80 3 : Set (ZMod 80 → L)) := (hstep2.2.2.2 l1 hl1 l1 hl1).2
  have hl1_16 : Pmap 80 4 l1 16 = -1 := by rw [hl1P, H12_gen16]
  have hl1i_16 : Pmap 80 4 l1⁻¹ 16 = -1 := by
    rw [H12_Pmap_inv, Pi.inv_apply, hl1P, H12_gen16]; norm_num
  have hflip : ∀ l : ZMod 80 → L, Pmap 80 4 l 16 = -1 → ∀ h : ZMod 80 → L,
      Pmap 80 4 (l * h) 16 ^ 5 = -(Pmap 80 4 h 16 ^ 5) := by
    intro l hl h
    rw [H16_Pmap_mul, Pi.mul_apply, hl]; ring
  -- the sets
  have hDcard : (topData 80 3 2 (1 : L) ω).ncard = 80 ^ 5 := by
    rw [← Nat.card_coe_set_eq, hstep2.1, H18_n80_pp]; norm_num
  have hDfin : (topData 80 3 2 (1 : L) ω).Finite := Set.finite_of_ncard_ne_zero (by rw [hDcard]; norm_num)
  have hED : {h | h ∈ topData 80 3 2 (1 : L) ω ∧ Pmap 80 4 h 16 ^ 5 = (ω ^ (16 : ZMod 80).val) ^ 2} ⊆
      topData 80 3 2 (1 : L) ω := fun h hh => hh.1
  have hsplit := Set.ncard_sdiff_add_ncard_of_subset hED hDfin
  have hEN : {h | h ∈ topData 80 3 2 (1 : L) ω ∧ Pmap 80 4 h 16 ^ 5 = (ω ^ (16 : ZMod 80).val) ^ 2}.ncard =
      (topData 80 3 2 (1 : L) ω \
        {h | h ∈ topData 80 3 2 (1 : L) ω ∧ Pmap 80 4 h 16 ^ 5 = (ω ^ (16 : ZMod 80).val) ^ 2}).ncard := by
    apply Set.ncard_congr (fun h _ => l1 * h)
    · rintro h ⟨hD, hQ⟩
      refine ⟨H16_topData_mul l1 h hl1 hD, fun hE => hneg_ne ?_⟩
      obtain ⟨-, hQ'⟩ := hE
      calc -(ω ^ (16 : ZMod 80).val) ^ 2 = -(Pmap 80 4 h 16 ^ 5) := by rw [hQ]
        _ = Pmap 80 4 (l1 * h) 16 ^ 5 := (hflip l1 hl1_16 h).symm
        _ = (ω ^ (16 : ZMod 80).val) ^ 2 := hQ'
    · intro a b _ _ hab
      funext k
      exact mul_left_cancel₀ (H12_D0_ne hl1 k) (congrFun hab k)
    · rintro b ⟨hbD, hbE⟩
      have hbQ : ¬ Pmap 80 4 b 16 ^ 5 = (ω ^ (16 : ZMod 80).val) ^ 2 := fun hQ => hbE ⟨hbD, hQ⟩
      have hbneg : Pmap 80 4 b 16 ^ 5 = -(ω ^ (16 : ZMod 80).val) ^ 2 := (hdich b hbD).resolve_left hbQ
      refine ⟨l1⁻¹ * b, ⟨H16_topData_mul _ b hl1i hbD, ?_⟩, ?_⟩
      · rw [hflip l1⁻¹ hl1i_16 b, hbneg, neg_neg]
      · funext k
        show l1 k * ((l1 k)⁻¹ * b k) = b k
        exact mul_inv_cancel_left₀ (H12_D0_ne hl1 k) (b k)
  have hcardE : Nat.card {h : ZMod 80 → L // h ∈ topData 80 3 2 (1 : L) ω ∧
      ∀ k ∈ layer0' 80 4, Pmap 80 4 h k ^ 5 = (ω ^ k.val) ^ 2} =
      {h | h ∈ topData 80 3 2 (1 : L) ω ∧ Pmap 80 4 h 16 ^ 5 = (ω ^ (16 : ZMod 80).val) ^ 2}.ncard := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun h =>
      ⟨fun hh => ⟨hh.1, (hiff h hh.1).mp hh.2⟩, fun hh => ⟨hh.1, (hiff h hh.1).mpr hh.2⟩⟩)
  rw [hcardE]
  omega

end Count

/-- Row rem_4_4_N6 — Remark 4.4 (s4_normfree.tex:165, v1.70): "each such top datum extends in `2` ways at `α ≠ 1`:
`80^5 · 1/2 · 2 · 4 = 4 · 80^5`". Reading: for every top datum with `P(α)^5 = α^2` on `μ_5 ∖ {1}` there are exactly `2`
maps `f ∈ G'` with (E1); the factor `80^5 · 1/2` is the number of such top data (half of `|𝒟| = 80^5`); and the
arithmetic identity. -/
theorem rem_4_4_N6_proved {L : Type*} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (hω : IsPrimitiveRoot ω 80) :
    (∀ h ∈ topData 80 3 2 (1 : L) ω, (∀ k ∈ layer0' 80 4, Pmap 80 4 h k ^ 5 = (ω ^ k.val) ^ 2) →
      Nat.card {f : ZMod 80 → L // f ∈ (Gprime 80 4 3 2 (1 : L) ω : Set (ZMod 80 → L)) ∧
        ∀ k ∈ layer0' 80 4, f (2 * k) = Pmap 80 4 h k * f k} = 2) ∧
    2 * Nat.card {h : ZMod 80 → L // h ∈ topData 80 3 2 (1 : L) ω ∧
        ∀ k ∈ layer0' 80 4, Pmap 80 4 h k ^ 5 = (ω ^ k.val) ^ 2} = 80 ^ 5 ∧
    (80 : ℚ) ^ 5 * (1 / 2) * 2 * 4 = 4 * 80 ^ 5 := by
  have hω1 : ω ^ 80 = 1 := hω.pow_eq_one
  have hω0 : ω ≠ 0 := hω.ne_zero (by norm_num)
  refine ⟨fun h hh hall => ?_, H25_count hω, by norm_num⟩
  have hP := H25_Pmap_mem hω hh
  have hex := H25_ext hω hP (hall 16 H12_m16)
  rw [H12_E1_card H25_hn (by norm_num) hω0 hω1 _ hP hex]
  exact (rem_4_4_G_proved (L := L)).2.1

/-! ## 6. Rows nit_s2_m, nit_s4_layers -/

/-- Row nit_s2_m — s2_xia.tex:46-47 (v1.70): "In that subsection `m := n/2 ≡ 4 (mod 12)`, so `m/2` is even and
`m ≡ 1 (mod 3)`" (the subsection's standing hypothesis: `n ≡ 8 (mod 24)`). -/
theorem nit_s2_m_proved (n : ℕ) (hn : n % 24 = 8) : (n / 2) % 12 = 4 ∧ Even (n / 2 / 2) ∧ (n / 2) % 3 = 1 :=
  ⟨by omega, Nat.even_iff.mpr (by omega), by omega⟩

/-- `|Ξ_a| = 2^{a-1}` (exponent model: `k` with `2^a k = 0 ≠ 2^{a-1} k`, i.e. `k = n_odd·(2j+1)`, `j < 2^{a-1}`). -/
theorem H25_Xi_card {n a nodd : ℕ} [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 1 ≤ a) (hodd : Odd nodd) :
    (univ.filter (fun k : ZMod n => (2 ^ a : ZMod n) * k = 0 ∧ (2 ^ (a - 1) : ZMod n) * k ≠ 0)).card =
      2 ^ (a - 1) := by
  have hnodd : 0 < nodd := hodd.pos
  obtain ⟨q, hq⟩ : ∃ q, q = 2 ^ (a - 1) := ⟨_, rfl⟩
  have hqpos : 0 < q := by rw [hq]; positivity
  have hpa : (2 : ℕ) ^ a = 2 * q := by
    rw [hq, ← pow_succ']
    congr 1
    omega
  have hn' : n = 2 * q * nodd := by rw [hn, hpa]
  have hn'' : n = q * (2 * nodd) := by rw [hn']; ring
  have e1 : (2 ^ a : ZMod n) = ((2 * q : ℕ) : ZMod n) := by rw [← hpa, Nat.cast_pow, Nat.cast_ofNat]
  have e2 : (2 ^ (a - 1) : ZMod n) = ((q : ℕ) : ZMod n) := by rw [hq, Nat.cast_pow, Nat.cast_ofNat]
  have hA : ∀ k : ZMod n, ((2 * q : ℕ) : ZMod n) * k = 0 ↔ nodd ∣ k.val := by
    intro k
    have h := Nat.mul_dvd_mul_iff_left (a := 2 * q) (b := nodd) (c := k.val) (by omega)
    rw [← hn'] at h
    rw [← ZMod.natCast_zmod_val k, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff, ZMod.val_natCast,
      Nat.mod_eq_of_lt (ZMod.val_lt k)]
    exact h
  have hB : ∀ k : ZMod n, ((q : ℕ) : ZMod n) * k = 0 ↔ 2 * nodd ∣ k.val := by
    intro k
    have h := Nat.mul_dvd_mul_iff_left (a := q) (b := 2 * nodd) (c := k.val) hqpos
    rw [← hn''] at h
    rw [← ZMod.natCast_zmod_val k, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff, ZMod.val_natCast,
      Nat.mod_eq_of_lt (ZMod.val_lt k)]
    exact h
  have hlt : ∀ j, j < q → nodd * (2 * j + 1) < n := by
    intro j hj
    rw [hn']
    nlinarith
  have key : univ.filter (fun k : ZMod n => (2 ^ a : ZMod n) * k = 0 ∧ (2 ^ (a - 1) : ZMod n) * k ≠ 0) =
      (range q).image (fun j => ((nodd * (2 * j + 1) : ℕ) : ZMod n)) := by
    ext k
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_range, e1, e2, ne_eq, hA, hB]
    constructor
    · rintro ⟨⟨c, hc⟩, h2⟩
      have hcodd : c % 2 = 1 := by
        by_contra hce
        obtain ⟨d, hd⟩ : ∃ d, c = 2 * d := ⟨c / 2, by omega⟩
        exact h2 ⟨d, by rw [hc, hd]; ring⟩
      obtain ⟨j, hj⟩ : ∃ j, c = 2 * j + 1 := ⟨c / 2, by omega⟩
      have hcn : nodd * c < nodd * (2 * q) := by
        rw [← hc]
        calc k.val < n := ZMod.val_lt k
          _ = nodd * (2 * q) := by rw [hn']; ring
      have hc2 : c < 2 * q := Nat.lt_of_mul_lt_mul_left hcn
      refine ⟨j, by omega, ?_⟩
      rw [← hj, ← hc, ZMod.natCast_zmod_val]
    · rintro ⟨j, hj, rfl⟩
      rw [ZMod.val_natCast_of_lt (hlt j hj)]
      refine ⟨Dvd.intro _ rfl, ?_⟩
      rintro ⟨d, hd⟩
      have h' : nodd * (2 * j + 1) = nodd * (2 * d) := by rw [hd]; ring
      have := Nat.eq_of_mul_eq_mul_left hnodd h'
      omega
  rw [key, card_image_of_injOn, card_range, hq]
  intro x hx y hy hxy
  have hx' : x < q := by simpa using hx
  have hy' : y < q := by simpa using hy
  have hxy' : ((nodd * (2 * x + 1) : ℕ) : ZMod n) = ((nodd * (2 * y + 1) : ℕ) : ZMod n) := hxy
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hlt x hx'), Nat.mod_eq_of_lt (hlt y hy')] at hxy'
  have := Nat.eq_of_mul_eq_mul_left hnodd hxy'
  omega

/-- Row nit_s4_layers — s4_normfree.tex:11-12 (v1.70), standing hypotheses of Section 4 (`n = 2^a n_odd`, `a ≥ 3`,
`n_odd` odd, `3 ∤ n`): "The top layer is `𝓛_a := {ξ : j(ξ) = a}`, of size `m`, ... Let `Ξ_a` be the set of the `2^{a-1}`
elements of order `2^a` of `μ_{2^a}`." Exponent model: `𝓛_a = topLayer n` (odd `k`); `Ξ_a` = the `k` with `2^a k = 0` and
`2^{a-1} k ≠ 0` (the filter of row thm_6_4_step3b). -/
theorem nit_s4_layers_proved (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n) :
    (topLayer n).card = n / 2 ∧
      (univ.filter (fun k : ZMod n => (2 ^ a : ZMod n) * k = 0 ∧ (2 ^ (a - 1) : ZMod n) * k ≠ 0)).card =
        2 ^ (a - 1) := by
  have h2 : 2 ∣ n := hn ▸ Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  exact ⟨H6_card_topLayer h2, H25_Xi_card hn (by omega) hodd⟩

/-! ## 7. Rows rem_4_4_v190, link_L3_v190 (paper v1.90) -/

theorem H25_pp32 : pp 32 = 7 * 151 := by norm_num [pp]

theorem H25_pp56 : pp 56 = 31 * 103 := by norm_num [pp]

theorem H25_pp104 : pp 104 = 67 * 163 := by norm_num [pp]

/-- Row rem_4_4_v190 — Remark 4.4 in v1.90 (v190 s4_normfree.tex:162-163): "`n = 80` is the smallest `n > 8` in Xia's
range with `p` prime (`p = 6481`)" and "`|𝒟| = (3^4-1)^5 = 80^5`" (Xia's range: `n ≡ 8 (mod 24)`, s2_xia.tex:45;
`|𝒟| = ∏_i (3^{L_i}-1) = pairProd 80 3`, as in row rem_4_4). The non-printed witnesses `pp 32 = 7·151`,
`pp 56 = 31·103` are the lemmas H25_pp32, H25_pp56. -/
theorem rem_4_4_v190_proved :
    (80 % 24 = 8 ∧ (pp 80).Prime ∧ pp 80 = 6481) ∧
    (∀ n : ℕ, 8 < n → n < 80 → n % 24 = 8 → ¬ (pp n).Prime) ∧
    pairProd 80 3 = (3 ^ 4 - 1) ^ 5 ∧ (3 ^ 4 - 1) ^ 5 = 80 ^ 5 := by
  refine ⟨⟨by norm_num, by norm_num [pp], by norm_num [pp]⟩, ?_, by rw [H18_n80_pp]; norm_num, by norm_num⟩
  intro n h1 h2 h3
  interval_cases n <;> try omega
  · rw [H25_pp32]; exact Nat.not_prime_mul (by norm_num) (by norm_num)
  · rw [H25_pp56]; exact Nat.not_prime_mul (by norm_num) (by norm_num)

/-- Row link_L3_v190 — Table 4 caption in v1.90 (v190 s5_twonorms.tex:94-95): "Only `n = 8` and `n = 80` make
`p = n^2+n+1` prime" (among the table's `n = 8, 32, 56, 80, 104`). The non-printed witnesses `pp 32 = 7·151`,
`pp 56 = 31·103`, `pp 104 = 67·163` are H25_pp32, H25_pp56, H25_pp104. -/
theorem link_L3_v190_proved :
    ∀ n ∈ ({8, 32, 56, 80, 104} : Finset ℕ), (pp n).Prime ↔ n = 8 ∨ n = 80 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · simp only [true_or, iff_true]; norm_num [pp]
  · rw [H25_pp32]
    exact ⟨fun h => absurd h (Nat.not_prime_mul (by norm_num) (by norm_num)), fun h => absurd h (by norm_num)⟩
  · rw [H25_pp56]
    exact ⟨fun h => absurd h (Nat.not_prime_mul (by norm_num) (by norm_num)), fun h => absurd h (by norm_num)⟩
  · simp only [or_true, iff_true]; norm_num [pp]
  · rw [H25_pp104]
    exact ⟨fun h => absurd h (Nat.not_prime_mul (by norm_num) (by norm_num)), fun h => absurd h (by norm_num)⟩

end Xia.Proofs

#print axioms Xia.Proofs.rem_4_4_N1_proved
#print axioms Xia.Proofs.rem_4_4_N2_proved
#print axioms Xia.Proofs.rem_4_4_N3_proved
#print axioms Xia.Proofs.rem_4_4_N4_proved
#print axioms Xia.Proofs.rem_4_4_N5_proved
#print axioms Xia.Proofs.rem_4_4_N6_proved
#print axioms Xia.Proofs.nit_s2_m_proved
#print axioms Xia.Proofs.nit_s4_layers_proved
#print axioms Xia.Proofs.rem_4_4_v190_proved
#print axioms Xia.Proofs.link_L3_v190_proved
