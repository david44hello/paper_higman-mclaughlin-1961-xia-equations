/- Xia/Proofs/Links.lean — proofs of the rows rem_4_4, link_L1, link_L2, link_L3 of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry
import Xia.Proofs.Combinatorics
import Xia.Proofs.Pow2Arith

namespace Xia.Proofs

open Xia Finset

set_option linter.unusedSectionVars false

/-! ## Part 1 — a computable form of the orbits, pairs and blocks (any `n`) -/

section Comp

variable {n : ℕ} [NeZero n]

/-- The orbit of `k` under `k ↦ 3k`, listed as `{3^i k : i < m}`. -/
def H18_cOrb (n m : ℕ) (k : ZMod n) : Finset (ZMod n) :=
  (range m).image (fun i => ((3 : ℕ) : ZMod n) ^ i * k)

theorem H18_orbit_eq (m : ℕ) (hm : 0 < m) (h3m : ((3 : ℕ) : ZMod n) ^ m = 1) (k : ZMod n) :
    orbit 3 k = H18_cOrb n m k := by
  ext x
  rw [H6_mem_orbit, H18_cOrb, mem_image]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i % m, mem_range.mpr (Nat.mod_lt _ hm), by rw [← pow_eq_pow_mod i h3m]⟩
  · rintro ⟨i, -, rfl⟩
    exact ⟨i, rfl⟩

theorem H18_topOrbits_eq (m : ℕ) (hm : 0 < m) (h3m : ((3 : ℕ) : ZMod n) ^ m = 1) :
    topOrbits n 3 = (topLayer n).image (H18_cOrb n m) := by
  unfold topOrbits
  exact image_congr (fun k _ => H18_orbit_eq m hm h3m k)

theorem H18_topPairs_eq (m : ℕ) (hm : 0 < m) (h3m : ((3 : ℕ) : ZMod n) ^ m = 1) :
    topPairs n 3 = ((topLayer n).image (H18_cOrb n m)).image (fun O => {O, inv O}) := by
  unfold topPairs
  rw [H18_topOrbits_eq m hm h3m]

theorem H18_pairProd_eq (m : ℕ) (hm : 0 < m) (h3m : ((3 : ℕ) : ZMod n) ^ m = 1) :
    pairProd n 3 = ∏ P ∈ ((topLayer n).image (H18_cOrb n m)).image (fun O => {O, inv O}), (3 ^ pairLen P - 1) := by
  unfold pairProd
  rw [H18_topPairs_eq m hm h3m]

theorem H18_blocks_eq (m : ℕ) (hm : 0 < m) (h3m : ((3 : ℕ) : ZMod n) ^ m = 1) :
    blocks n = ((topLayer n).image (H18_cOrb n m)).image blockOf := by
  unfold blocks
  rw [H18_topOrbits_eq m hm h3m]

theorem H18_blocksA_eq (m : ℕ) (hm : 0 < m) (h3m : ((3 : ℕ) : ZMod n) ^ m = 1) :
    blocksA n = (((topLayer n).image (H18_cOrb n m)).image blockOf).filter (fun B => ∃ O ∈ B, negO O = O) := by
  rw [← H18_blocks_eq m hm h3m]
  unfold blocksA IsCaseA
  exact filter_congr_decidable _ _ _

theorem H18_blocksB_eq (m : ℕ) (hm : 0 < m) (h3m : ((3 : ℕ) : ZMod n) ^ m = 1) :
    blocksB n = (((topLayer n).image (H18_cOrb n m)).image blockOf).filter
      (fun B => ∃ O ∈ B, negO O = inv O) := by
  rw [← H18_blocks_eq m hm h3m]
  unfold blocksB IsCaseB
  exact filter_congr_decidable _ _ _

theorem H18_blocksC_eq (m : ℕ) (hm : 0 < m) (h3m : ((3 : ℕ) : ZMod n) ^ m = 1) :
    blocksC n = (((topLayer n).image (H18_cOrb n m)).image blockOf).filter
      (fun B => ¬ (∃ O ∈ B, negO O = O) ∧ ¬ (∃ O ∈ B, negO O = inv O)) := by
  rw [← H18_blocks_eq m hm h3m]
  unfold blocksC IsCaseA IsCaseB
  refine (filter_congr_decidable _ _ _).trans (filter_congr (fun B _ =>
    ⟨fun h => ⟨fun ⟨O, hO, hA⟩ => (h O hO).1 hA, fun ⟨O, hO, hB⟩ => (h O hO).2 hB⟩,
      fun h O hO => ⟨fun hA => h.1 ⟨O, hO, hA⟩, fun hB => h.2 ⟨O, hO, hB⟩⟩⟩))

theorem H18_fibreProd_eq (m : ℕ) (hm : 0 < m) (h3m : ((3 : ℕ) : ZMod n) ^ m = 1) :
    fibreProd n =
      (∏ B ∈ (((topLayer n).image (H18_cOrb n m)).image blockOf).filter (fun B => ∃ O ∈ B, negO O = O),
          (qO B - 1)) *
        (∏ B ∈ (((topLayer n).image (H18_cOrb n m)).image blockOf).filter (fun B => ∃ O ∈ B, negO O = inv O),
          (qO B + 1)) *
        (∏ B ∈ (((topLayer n).image (H18_cOrb n m)).image blockOf).filter
          (fun B => ¬ (∃ O ∈ B, negO O = O) ∧ ¬ (∃ O ∈ B, negO O = inv O)), (3 ^ blockLen B - 1)) := by
  unfold fibreProd
  rw [H18_blocksA_eq m hm h3m, H18_blocksB_eq m hm h3m, H18_blocksC_eq m hm h3m]

end Comp

/-! ## Part 2 — the finite facts, one kernel `decide` each -/

/-! ### n = 8 (`3^2 = 1`) -/

theorem H18_n8_Acard : (blocksA 8).card = 0 := by
  rw [H18_blocksA_eq 2 (by norm_num) (by decide)]; decide +kernel

theorem H18_n8_Bmap : (blocksB 8).val.map blockLen = {2} := by
  rw [H18_blocksB_eq 2 (by norm_num) (by decide)]; decide +kernel

theorem H18_n8_Bcard : (blocksB 8).card = 1 := by
  rw [H18_blocksB_eq 2 (by norm_num) (by decide)]; decide +kernel

theorem H18_n8_Ccard : (blocksC 8).card = 0 := by
  rw [H18_blocksC_eq 2 (by norm_num) (by decide)]; decide +kernel

theorem H18_n8_fp : fibreProd 8 = 4 := by
  rw [H18_fibreProd_eq 2 (by norm_num) (by decide)]; decide +kernel

/-! ### n = 32 (`3^8 = 1`) -/

theorem H18_n32_Amap : (blocksA 32).val.map blockLen = {8} := by
  rw [H18_blocksA_eq 8 (by norm_num) (by decide)]; decide +kernel

theorem H18_n32_Bcard : (blocksB 32).card = 0 := by
  rw [H18_blocksB_eq 8 (by norm_num) (by decide)]; decide +kernel

theorem H18_n32_Ccard : (blocksC 32).card = 0 := by
  rw [H18_blocksC_eq 8 (by norm_num) (by decide)]; decide +kernel

theorem H18_n32_fp : fibreProd 32 = 80 := by
  rw [H18_fibreProd_eq 8 (by norm_num) (by decide)]; decide +kernel

/-! ### n = 56 (`3^6 = 1`) -/

theorem H18_n56_Acard : (blocksA 56).card = 0 := by
  rw [H18_blocksA_eq 6 (by norm_num) (by decide)]; decide +kernel

theorem H18_n56_Bmap : (blocksB 56).val.map blockLen = {2, 6, 6} := by
  rw [H18_blocksB_eq 6 (by norm_num) (by decide)]; decide +kernel

theorem H18_n56_Ccard : (blocksC 56).card = 0 := by
  rw [H18_blocksC_eq 6 (by norm_num) (by decide)]; decide +kernel

theorem H18_n56_fp : fibreProd 56 = 3136 := by
  rw [H18_fibreProd_eq 6 (by norm_num) (by decide)]; decide +kernel

theorem H18_n56_pp : pairProd 56 3 = 4239872 := by
  rw [H18_pairProd_eq 6 (by norm_num) (by decide)]; decide +kernel

/-! ### n = 80 (`3^4 = 1`) -/

theorem H18_n80_pcard : (topPairs 80 3).card = 5 := by
  rw [H18_topPairs_eq 4 (by norm_num) (by decide)]; decide +kernel

theorem H18_n80_plens : (topPairs 80 3).val.map pairLen = {4, 4, 4, 4, 4} := by
  rw [H18_topPairs_eq 4 (by norm_num) (by decide)]; decide +kernel

theorem H18_n80_pp : pairProd 80 3 = 3276800000 := by
  rw [H18_pairProd_eq 4 (by norm_num) (by decide)]; decide +kernel

theorem H18_n80_Amap : (blocksA 80).val.map blockLen = {4} := by
  rw [H18_blocksA_eq 4 (by norm_num) (by decide)]; decide +kernel

theorem H18_n80_Bcard : (blocksB 80).card = 0 := by
  rw [H18_blocksB_eq 4 (by norm_num) (by decide)]; decide +kernel

theorem H18_n80_Cmap : (blocksC 80).val.map blockLen = {4, 4} := by
  rw [H18_blocksC_eq 4 (by norm_num) (by decide)]; decide +kernel

theorem H18_n80_fp : fibreProd 80 = 51200 := by
  rw [H18_fibreProd_eq 4 (by norm_num) (by decide)]; decide +kernel

/-! ### n = 104 (`3^6 = 1`) -/

theorem H18_n104_Acard : (blocksA 104).card = 0 := by
  rw [H18_blocksA_eq 6 (by norm_num) (by decide)]; decide +kernel

theorem H18_n104_Bmap : (blocksB 104).val.map blockLen = {2} := by
  rw [H18_blocksB_eq 6 (by norm_num) (by decide)]; decide +kernel

theorem H18_n104_Cmap : (blocksC 104).val.map blockLen = {6, 6} := by
  rw [H18_blocksC_eq 6 (by norm_num) (by decide)]; decide +kernel

theorem H18_n104_fp : fibreProd 104 = 2119936 := by
  rw [H18_fibreProd_eq 6 (by norm_num) (by decide)]; decide +kernel

theorem H18_n104_pp : pairProd 104 3 = 2247064322048 := by
  rw [H18_pairProd_eq 6 (by norm_num) (by decide)]; decide +kernel

/-! ## Part 3 — general facts for link L2 (`n ≡ 8 mod 24`, `16 ∣ n`) -/

section General

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem H18_inv_inv (O : Finset (ZMod n)) : inv (inv O) = O := by
  unfold inv
  rw [image_image]
  conv_rhs => rw [← image_id (s := O)]
  exact image_congr (fun z _ => by simp)

omit [NeZero n] in
theorem H18_negO_negO (h2 : half n + half n = (0 : ZMod n)) (O : Finset (ZMod n)) : negO (negO O) = O := by
  unfold negO
  rw [image_image]
  conv_rhs => rw [← image_id (s := O)]
  exact image_congr (fun z _ => by simp [add_assoc, h2])

omit [NeZero n] in
theorem H18_inv_negO (h2 : half n + half n = (0 : ZMod n)) (O : Finset (ZMod n)) :
    inv (negO O) = negO (inv O) := by
  have hneg : -half n = half n := neg_eq_of_add_eq_zero_right h2
  unfold inv negO
  rw [image_image, image_image]
  exact image_congr (fun z _ => by simp only [Function.comp_apply]; rw [neg_add, hneg])

/-- Case B is a property of the whole block: if one orbit of `blockOf O0` is of case B, so is `O0`. -/
theorem H18_caseB_of_mem_block (h2 : half n + half n = (0 : ZMod n)) {O0 O : Finset (ZMod n)}
    (hO : O ∈ blockOf O0) (hB : IsCaseB O) : IsCaseB O0 := by
  unfold IsCaseB at hB ⊢
  simp only [blockOf, mem_insert, mem_singleton] at hO
  rcases hO with rfl | rfl | rfl | rfl
  · exact hB
  · rw [H18_inv_inv] at hB
    have h := congrArg inv hB
    rwa [H18_inv_negO h2, H18_inv_inv] at h
  · rw [H18_negO_negO h2, H18_inv_negO h2] at hB
    have h := congrArg negO hB
    rwa [H18_negO_negO h2] at h
  · rw [H18_negO_negO h2, H18_inv_negO h2, H18_inv_inv] at hB
    exact hB.symm

theorem H18_blocksB_card_zero (h2 : half n + half n = (0 : ZMod n))
    (hnoB : ∀ O ∈ topOrbits n 3, ¬ IsCaseB O) : (blocksB n).card = 0 := by
  rw [card_eq_zero, eq_empty_iff_forall_notMem]
  intro B hB
  simp only [blocksB, mem_filter] at hB
  obtain ⟨hB, O, hO, hOB⟩ := hB
  obtain ⟨O0, hO0, rfl⟩ := mem_image.mp hB
  exact hnoB O0 hO0 (H18_caseB_of_mem_block h2 hO hOB)

theorem H18_two_dvd_three_pow_sub_one (k : ℕ) : 2 ∣ 3 ^ k - 1 :=
  (Nat.Odd.sub_odd (Odd.pow ⟨1, rfl⟩) odd_one).two_dvd

theorem H18_not_two_dvd_three_pow (k : ℕ) : ¬ 2 ∣ 3 ^ k :=
  Odd.not_two_dvd_nat (Odd.pow ⟨1, rfl⟩)

theorem H18_lt_of_le_of_two_dvd {x y : ℕ} (hle : x ≤ y) (hx : 2 ∣ x) (hy : ¬ 2 ∣ y) : x < y :=
  lt_of_le_of_ne hle (fun h => hy (h ▸ hx))

theorem H18_topLayer_nonempty (h1 : 1 < n) : (topLayer n).Nonempty :=
  ⟨1, mem_filter.mpr ⟨mem_univ _, by rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt h1]; exact odd_one⟩⟩

theorem H18_topOrbits_nonempty (h1 : 1 < n) : (topOrbits n 3).Nonempty :=
  (H18_topLayer_nonempty h1).image _

/-- With no case-B block and at least one block, `fibreProd n` has a factor `3^x - 1`, so it is even. -/
theorem H18_fibreProd_even (hne : (blocks n).Nonempty) (hB0 : (blocksB n).card = 0) : 2 ∣ fibreProd n := by
  obtain ⟨B, hB⟩ := hne
  unfold fibreProd
  by_cases hA : ∃ O ∈ B, IsCaseA O
  · have hmem : B ∈ blocksA n := by simp only [blocksA, mem_filter]; exact ⟨hB, hA⟩
    have h1 : 2 ∣ qO B - 1 := H18_two_dvd_three_pow_sub_one _
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_trans h1 (dvd_prod_of_mem (fun B => qO B - 1) hmem)) _) _
  · by_cases hBB : ∃ O ∈ B, IsCaseB O
    · have hmem : B ∈ blocksB n := by simp only [blocksB, mem_filter]; exact ⟨hB, hBB⟩
      rw [card_eq_zero] at hB0
      rw [hB0] at hmem
      exact absurd hmem (notMem_empty B)
    · have hC : ∀ O ∈ B, ¬ IsCaseA O ∧ ¬ IsCaseB O := fun O hO => ⟨fun h => hA ⟨O, hO, h⟩, fun h => hBB ⟨O, hO, h⟩⟩
      have hmem : B ∈ blocksC n := by simp only [blocksC, mem_filter]; exact ⟨hB, hC⟩
      exact Dvd.dvd.mul_left (dvd_trans (H18_two_dvd_three_pow_sub_one _) (dvd_prod_of_mem (fun B => 3 ^ blockLen B - 1) hmem)) _

/-- `∏_i (3^{L_i} - 1) < 3^{∑ L_i} = 3^{n/4}` (the product is even and non-empty, the power odd). -/
theorem H18_pairProd_lt (hsum : ∑ P ∈ topPairs n 3, pairLen P = n / 4) (hne : (topPairs n 3).Nonempty) :
    pairProd n 3 < 3 ^ (n / 4) := by
  have hle : pairProd n 3 ≤ 3 ^ (n / 4) := by
    unfold pairProd
    rw [← hsum, ← prod_pow_eq_pow_sum]
    exact prod_le_prod (fun P _ => Nat.sub_le _ _)
  have hev : 2 ∣ pairProd n 3 := by
    obtain ⟨P, hP⟩ := hne
    exact dvd_trans (H18_two_dvd_three_pow_sub_one (pairLen P)) (dvd_prod_of_mem (fun P => 3 ^ pairLen P - 1) hP)
  exact H18_lt_of_le_of_two_dvd hle hev (H18_not_two_dvd_three_pow _)

omit [NeZero n] in
theorem H18_four_le_a {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (hodd : Odd nodd) (h16 : 16 ∣ n) : 4 ≤ a := by
  have hcop : Nat.Coprime (2 ^ 4) nodd := Nat.Coprime.pow_left 4 (Nat.coprime_two_left.mpr hodd)
  have h : 2 ^ 4 ∣ 2 ^ a * nodd := by rw [← hn]; norm_num; exact h16
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right h)

end General

/-! ## Part 4 — the four rows, parametrized by the count rows they use -/

/-- Remark 4.4 (s4_normfree.tex:167-172), `n = 80`; the count from Theorem 4.1 (row `thm_4_1_count`). -/
theorem rem_4_4_of
    (hcount : ∀ (n a nodd : ℕ) [NeZero n] (_hn : n = 2 ^ a * nodd) (_ha : 3 ≤ a) (_hodd : Odd nodd)
      (_h3 : ¬ 3 ∣ n),
      Nat.card (NFSet n 2) = 4 * pairProd n 3 ∧ (NFSet n 2).Nonempty ∧
        (Nat.card (NFSet n 2) : ℚ) = 4 * 3 ^ (n / 4) * ∏ P ∈ topPairs n 3, (1 - (3 : ℚ) ^ (-(pairLen P : ℤ)))) :
    (topPairs 80 3).card = 5 ∧ (∀ P ∈ topPairs 80 3, pairLen P = 4) ∧ pairProd 80 3 = 80 ^ 5 ∧
      Nat.card (NFSet 80 2) = 4 * 80 ^ 5 := by
  have hpp : pairProd 80 3 = 80 ^ 5 := by rw [H18_n80_pp]; norm_num
  refine ⟨H18_n80_pcard, fun P hP => ?_, hpp, ?_⟩
  · have h := Multiset.mem_map_of_mem pairLen (mem_val.mpr hP)
    rw [H18_n80_plens] at h
    simpa using h
  · rw [(hcount 80 4 5 (by norm_num) (by norm_num) ⟨2, rfl⟩ (by norm_num)).1, hpp]

/-- Link L1 (s3_pow2.tex:138-139); counts from Theorem 3.1 (row `thm_3_1_card`) and Corollary 3.5(ii) (row
`cor_3_5_ii`). -/
theorem link_L1_of
    (hcard : ∀ (n e : ℕ) [NeZero n] (_hne : n = 2 ^ e) (_he : 3 ≤ e), Nat.card (NFSet n 2) = 4 * (QQ n - 1))
    (hcor : ∀ (n e : ℕ) [NeZero n] (_hne : n = 2 ^ e) (_he : 5 ≤ e) (_heo : Odd e) (ξ0 : GaloisField 3 (n / 2))
      (_hξ0 : IsPrimitiveRoot ξ0 n),
      let above : GaloisField 3 (n / 2) → GaloisField 3 (n / 2) → GaloisField 3 (n / 2) →
          Set (ZMod n → GaloisField 3 (n / 2)) := fun ν s1 h1 =>
        {y | y ∈ XiaSet n 2 ∧ dft ξ0 y 1 ^ (1 + qq n) = ν ∧ S y = s1 ∧ dft ξ0 y 0 = h1}
      (∀ ν s1 h1, (above ν s1 h1).ncard ≤ 4 ∧ (above ν s1 h1).ncard ∈ ({0, 2, 4} : Set ℕ) ∧
        ∀ y ∈ above ν s1 h1, ∀ y' ∈ NFSet n 2,
          (y' ∈ above ν s1 h1 ↔ paramMap n ξ0 y' ∈ ({dft ξ0 y 1, -dft ξ0 y 1, Tmap n ξ0 (dft ξ0 y 1),
            -Tmap n ξ0 (dft ξ0 y 1)} : Set _) ×ˢ ({s1} ×ˢ {h1}))) ∧
        Nat.card (XiaSet n 2) ≤ 16 * (qq n - 1)) :
    (16 * (qq 32 - 1) = 1280 ∧ Nat.card (XiaSet 32 2) ≤ 1280 ∧ Nat.card (NFSet 32 2) = 26240) ∧
      (16 * (qq 128 - 1) = 688747520 ∧ Nat.card (XiaSet 128 2) ≤ 688747520 ∧
        Nat.card (NFSet 128 2) = 7412080755407360) := by
  have hq32 : 16 * (qq 32 - 1) = 1280 := by norm_num [qq]
  have hq128 : 16 * (qq 128 - 1) = 688747520 := by norm_num [qq]
  obtain ⟨ξ32, hξ32⟩ := (thm_3_1_xi0_proved 32 5 (by norm_num) (by norm_num)).1
  obtain ⟨ξ128, hξ128⟩ := (thm_3_1_xi0_proved 128 7 (by norm_num) (by norm_num)).1
  have hX32 := (hcor 32 5 (by norm_num) (by norm_num) ⟨2, rfl⟩ ξ32 hξ32).2
  have hX128 := (hcor 128 7 (by norm_num) (by norm_num) ⟨3, rfl⟩ ξ128 hξ128).2
  refine ⟨⟨hq32, hq32 ▸ hX32, ?_⟩, ⟨hq128, hq128 ▸ hX128, ?_⟩⟩
  · rw [hcard 32 5 (by norm_num) (by norm_num)]; norm_num [QQ]
  · rw [hcard 128 7 (by norm_num) (by norm_num)]; norm_num [QQ]

/-- The general half of link L2: `n ≡ 8 (mod 24)`, `16 ∣ n`. Uses Theorem 5.1(b) and Theorem 4.1 (pairs part), both
installed, and the rows `thm_4_1_count`, `cor_5_2` (hypotheses). -/
theorem H18_L2_general
    (hcount : ∀ (n a nodd : ℕ) [NeZero n] (_hn : n = 2 ^ a * nodd) (_ha : 3 ≤ a) (_hodd : Odd nodd)
      (_h3 : ¬ 3 ∣ n),
      Nat.card (NFSet n 2) = 4 * pairProd n 3 ∧ (NFSet n 2).Nonempty ∧
        (Nat.card (NFSet n 2) : ℚ) = 4 * 3 ^ (n / 4) * ∏ P ∈ topPairs n 3, (1 - (3 : ℚ) ^ (-(pairLen P : ℤ))))
    (hcor : ∀ (n : ℕ) [NeZero n] (_hn : n % 24 = 8) {L : Type} [Field L] [Algebra (GaloisField 3 (n / 2)) L]
      (ω : L) (_hω : IsPrimitiveRoot ω n),
      (∀ y ∈ NFSet n 2, (fibre ω y ∩ XiaSet n 2).ncard ∈ ({0, 2, 4} : Set ℕ) ∧
        ∀ y' ∈ fibre ω y ∩ XiaSet n 2,
          fibre ω y ∩ XiaSet n 2 = ({y', ySubst y', yTrans (half n) y', ySubst (yTrans (half n) y')} : Set _)) ∧
        Nat.card (XiaSet n 2) ≤ 16 * fibreProd n ∧
        (16 * fibreProd n : ℝ) ≤ 16 * (4 / 3 : ℝ) ^ (blocksB n).card * 3 ^ (n / 8))
    (n : ℕ) [NeZero n] (hn24 : n % 24 = 8) (h16 : 16 ∣ n) :
    (blocksB n).card = 0 ∧ 16 * fibreProd n < 16 * 3 ^ (n / 8) ∧ Nat.card (NFSet n 2) < 4 * 3 ^ (n / 4) := by
  obtain ⟨a, nodd, hodd, hn⟩ := Nat.exists_eq_two_pow_mul_odd (NeZero.ne n)
  have ha4 : 4 ≤ a := H18_four_le_a hn hodd h16
  have h3 : ¬ 3 ∣ n := by omega
  have h1 : 1 < n := by omega
  have h2 : half n + half n = (0 : ZMod n) := H6_half_add_half (by omega)
  have hB0 : (blocksB n).card = 0 :=
    H18_blocksB_card_zero h2 (fun O hO => (thm_5_1_b_proved n a nodd hn (by omega) hodd h3 O hO).1 ha4)
  -- the bound of Cor 5.2, in a field containing a primitive n-th root of unity
  have : NeZero ((n : ℕ) : GaloisField 3 (n / 2)) :=
    ⟨fun h => h3 ((CharP.cast_eq_zero_iff (GaloisField 3 (n / 2)) 3 n).mp h)⟩
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure (GaloisField 3 (n / 2))) n
  have hreal := (hcor n hn24 ω hω).2.2
  rw [hB0, pow_zero, mul_one] at hreal
  have hle : fibreProd n ≤ 3 ^ (n / 8) := by
    have h' : ((16 * fibreProd n : ℕ) : ℝ) ≤ ((16 * 3 ^ (n / 8) : ℕ) : ℝ) := by push_cast; exact hreal
    have h'' := Nat.cast_le.mp h'
    omega
  have hev := H18_fibreProd_even ((H18_topOrbits_nonempty h1).image _) hB0
  have hlt := H18_lt_of_le_of_two_dvd hle hev (H18_not_two_dvd_three_pow _)
  -- the count of Theorem 4.1
  have hsum := (thm_4_1_pairs_proved n a nodd hn (by omega) hodd h3).2
  have hpp := H18_pairProd_lt hsum ((H18_topOrbits_nonempty h1).image _)
  have hNF := (hcount n a nodd hn (by omega) hodd h3).1
  refine ⟨hB0, by omega, by omega⟩

/-- Link L2 (s5_twonorms.tex:88-90). -/
theorem link_L2_of
    (hcard : ∀ (n e : ℕ) [NeZero n] (_hne : n = 2 ^ e) (_he : 3 ≤ e), Nat.card (NFSet n 2) = 4 * (QQ n - 1))
    (hcount : ∀ (n a nodd : ℕ) [NeZero n] (_hn : n = 2 ^ a * nodd) (_ha : 3 ≤ a) (_hodd : Odd nodd)
      (_h3 : ¬ 3 ∣ n),
      Nat.card (NFSet n 2) = 4 * pairProd n 3 ∧ (NFSet n 2).Nonempty ∧
        (Nat.card (NFSet n 2) : ℚ) = 4 * 3 ^ (n / 4) * ∏ P ∈ topPairs n 3, (1 - (3 : ℚ) ^ (-(pairLen P : ℤ))))
    (hcor : ∀ (n : ℕ) [NeZero n] (_hn : n % 24 = 8) {L : Type} [Field L] [Algebra (GaloisField 3 (n / 2)) L]
      (ω : L) (_hω : IsPrimitiveRoot ω n),
      (∀ y ∈ NFSet n 2, (fibre ω y ∩ XiaSet n 2).ncard ∈ ({0, 2, 4} : Set ℕ) ∧
        ∀ y' ∈ fibre ω y ∩ XiaSet n 2,
          fibre ω y ∩ XiaSet n 2 = ({y', ySubst y', yTrans (half n) y', ySubst (yTrans (half n) y')} : Set _)) ∧
        Nat.card (XiaSet n 2) ≤ 16 * fibreProd n ∧
        (16 * fibreProd n : ℝ) ≤ 16 * (4 / 3 : ℝ) ^ (blocksB n).card * 3 ^ (n / 8)) :
    (∀ (n : ℕ) [NeZero n], n % 24 = 8 → 16 ∣ n →
      (blocksB n).card = 0 ∧ 16 * fibreProd n < 16 * 3 ^ (n / 8) ∧ Nat.card (NFSet n 2) < 4 * 3 ^ (n / 4)) ∧
    ((blocksB 8).card = 1 ∧ (∀ B ∈ blocksB 8, blockLen B = 2) ∧ 16 * fibreProd 8 = 64 ∧ Nat.card (NFSet 8 2) = 32) := by
  refine ⟨fun n _ hn24 h16 => H18_L2_general hcount hcor n hn24 h16, H18_n8_Bcard, fun B hB => ?_, ?_, ?_⟩
  · have h := Multiset.mem_map_of_mem blockLen (mem_val.mpr hB)
    rw [H18_n8_Bmap] at h
    simpa using h
  · rw [H18_n8_fp]
  · rw [hcard 8 3 (by norm_num) le_rfl]; norm_num [QQ]

/-- Link L3 — Table 4 (s5_twonorms.tex:93-109); counts from Theorem 3.1 (`n = 8, 32`) and Theorem 4.1 (`n = 56, 80, 104`). -/
theorem link_L3_of
    (hcard : ∀ (n e : ℕ) [NeZero n] (_hne : n = 2 ^ e) (_he : 3 ≤ e), Nat.card (NFSet n 2) = 4 * (QQ n - 1))
    (hcount : ∀ (n a nodd : ℕ) [NeZero n] (_hn : n = 2 ^ a * nodd) (_ha : 3 ≤ a) (_hodd : Odd nodd)
      (_h3 : ¬ 3 ∣ n),
      Nat.card (NFSet n 2) = 4 * pairProd n 3 ∧ (NFSet n 2).Nonempty ∧
        (Nat.card (NFSet n 2) : ℚ) = 4 * 3 ^ (n / 4) * ∏ P ∈ topPairs n 3, (1 - (3 : ℚ) ^ (-(pairLen P : ℤ)))) :
    ((blocksA 8).card = 0 ∧ (blocksB 8).val.map blockLen = {2} ∧ (blocksC 8).card = 0 ∧
      Nat.card (NFSet 8 2) = 32 ∧ 16 * fibreProd 8 = 64) ∧
    ((blocksA 32).val.map blockLen = {8} ∧ (blocksB 32).card = 0 ∧ (blocksC 32).card = 0 ∧
      Nat.card (NFSet 32 2) = 26240 ∧ 16 * fibreProd 32 = 1280) ∧
    ((blocksA 56).card = 0 ∧ (blocksB 56).val.map blockLen = {2, 6, 6} ∧ (blocksC 56).card = 0 ∧
      Nat.card (NFSet 56 2) = 16959488 ∧ 16 * fibreProd 56 = 50176) ∧
    ((blocksA 80).val.map blockLen = {4} ∧ (blocksB 80).card = 0 ∧ (blocksC 80).val.map blockLen = {4, 4} ∧
      Nat.card (NFSet 80 2) = 13107200000 ∧ 16 * fibreProd 80 = 819200) ∧
    ((blocksA 104).card = 0 ∧ (blocksB 104).val.map blockLen = {2} ∧ (blocksC 104).val.map blockLen = {6, 6} ∧
      Nat.card (NFSet 104 2) = 8988257288192 ∧ 16 * fibreProd 104 = 33918976) := by
  refine ⟨⟨H18_n8_Acard, H18_n8_Bmap, H18_n8_Ccard, ?_, by rw [H18_n8_fp]⟩,
    ⟨H18_n32_Amap, H18_n32_Bcard, H18_n32_Ccard, ?_, by rw [H18_n32_fp]⟩,
    ⟨H18_n56_Acard, H18_n56_Bmap, H18_n56_Ccard, ?_, by rw [H18_n56_fp]⟩,
    ⟨H18_n80_Amap, H18_n80_Bcard, H18_n80_Cmap, ?_, by rw [H18_n80_fp]⟩,
    ⟨H18_n104_Acard, H18_n104_Bmap, H18_n104_Cmap, ?_, by rw [H18_n104_fp]⟩⟩
  · rw [hcard 8 3 (by norm_num) le_rfl]; norm_num [QQ]
  · rw [hcard 32 5 (by norm_num) (by norm_num)]; norm_num [QQ]
  · rw [(hcount 56 3 7 (by norm_num) le_rfl ⟨3, rfl⟩ (by norm_num)).1, H18_n56_pp]
  · rw [(hcount 80 4 5 (by norm_num) (by norm_num) ⟨2, rfl⟩ (by norm_num)).1, H18_n80_pp]
  · rw [(hcount 104 3 13 (by norm_num) le_rfl ⟨6, rfl⟩ (by norm_num)).1, H18_n104_pp]

end Xia.Proofs

#print axioms Xia.Proofs.rem_4_4_of
#print axioms Xia.Proofs.link_L1_of
#print axioms Xia.Proofs.link_L2_of
#print axioms Xia.Proofs.link_L3_of
