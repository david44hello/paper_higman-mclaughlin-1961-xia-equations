/- Xia/Proofs/Fig2.lean — proofs of the rows fig2_layers, intro_planar_H7, intro_sigma_order of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Fig2
import Xia.Proofs.Rem44
import Xia.Proofs.Links
import Xia.Proofs.SigmaOfN

namespace Xia.Proofs

open Xia Finset

/-- A computable form of layer `j`: `ζ = ω^{65k}` (`65 ≡ 1 mod 16`, `65 ≡ 0 mod 5`) has order exactly `2^j`. -/
def fig2LayerC (j : ℕ) : Finset (ZMod 80) :=
  univ.filter (fun k => (2 ^ j : ZMod 80) * (65 * k) = 0 ∧ ∀ i < j, (2 ^ i : ZMod 80) * (65 * k) ≠ 0)

/-- The 2-part of `z + w` (`16z = 0`, `5w = 0`) is `z`: `65(z + w) = z + 4·(16z) + 13·(5w)`. -/
theorem fig2_twoPart (z w : ZMod 80) (hz : (16 : ZMod 80) * z = 0) (hw : (5 : ZMod 80) * w = 0) :
    65 * (z + w) = z := by
  have h : 65 * (z + w) = z + 4 * (16 * z) + 13 * (5 * w) := by ring
  rw [h, hz, hw]
  ring

/-- `addOrderOf z = 2^j` iff `2^j z = 0` and `2^i z ≠ 0` for every `i < j`. -/
theorem fig2_order_iff (z : ZMod 80) (j : ℕ) :
    addOrderOf z = 2 ^ j ↔ (2 ^ j : ZMod 80) * z = 0 ∧ ∀ i < j, (2 ^ i : ZMod 80) * z ≠ 0 := by
  have hsmul : ∀ m : ℕ, (m • z = 0 ↔ (m : ZMod 80) * z = 0) := fun m => by rw [nsmul_eq_mul]
  constructor
  · intro h
    refine ⟨?_, fun i hi hzero => ?_⟩
    · have := addOrderOf_nsmul_eq_zero z
      rw [h, hsmul] at this
      exact_mod_cast this
    · have hdvd : addOrderOf z ∣ 2 ^ i := addOrderOf_dvd_of_nsmul_eq_zero ((hsmul _).2 (by exact_mod_cast hzero))
      rw [h] at hdvd
      have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).1 hdvd
      omega
  · rintro ⟨hj, hlt⟩
    have hdvd : addOrderOf z ∣ 2 ^ j := addOrderOf_dvd_of_nsmul_eq_zero ((hsmul _).2 (by exact_mod_cast hj))
    obtain ⟨i, hij, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    rcases lt_or_eq_of_le hij with hlt' | rfl
    · exfalso
      have h0 := addOrderOf_nsmul_eq_zero z
      rw [hi, hsmul] at h0
      exact hlt i hlt' (by exact_mod_cast h0)
    · exact hi

/-- `O^{-1}` of the orbit of `k` is the orbit of `-k`. -/
theorem fig2_inv_cOrb (k : ZMod 80) : inv (H18_cOrb 80 4 k) = H18_cOrb 80 4 (-k) := by
  unfold inv H18_cOrb
  rw [image_image]
  congr 1
  funext i
  simp [Function.comp, mul_neg]

/-- Every top orbit has length 4 and is not its own inverse; its inverse is a top orbit. -/
theorem fig2_topOrbits_facts :
    ∀ O ∈ topOrbits 80 3, O.card = 4 ∧ inv O ∈ topOrbits 80 3 ∧ inv O ≠ O := by
  rw [H18_topOrbits_eq 4 (by norm_num) H25_three80]
  have hk : ∀ k ∈ topLayer 80, (H18_cOrb 80 4 k).card = 4 ∧ -k ∈ topLayer 80 ∧ -k ∉ H18_cOrb 80 4 k := by
    decide +kernel
  intro O hO
  obtain ⟨k, hkT, rfl⟩ := mem_image.mp hO
  obtain ⟨h1, h2, h3⟩ := hk k hkT
  have hself : k ∈ H18_cOrb 80 4 k := mem_image.mpr ⟨0, by simp, by simp⟩
  refine ⟨h1, ?_, fun heq => h3 ?_⟩
  · rw [fig2_inv_cOrb]
    exact mem_image_of_mem _ h2
  · rw [← heq]
    exact mem_image_of_mem Neg.neg hself

theorem fig2Layer_eq (j : ℕ) : fig2Layer j = fig2LayerC j := by
  classical
  ext k
  simp only [fig2Layer, fig2LayerC, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨z, w, rfl, hz, hw, ho⟩
    rw [fig2_twoPart z w hz hw]
    exact (fig2_order_iff z j).1 ho
  · intro h
    refine ⟨65 * k, 16 * k, ?_, ?_, ?_, (fig2_order_iff _ j).2 h⟩
    · have : (65 : ZMod 80) + 16 = 1 := by decide
      rw [← add_mul, this, one_mul]
    · rw [← mul_assoc, show (16 : ZMod 80) * 65 = 0 by decide, zero_mul]
    · rw [← mul_assoc, show (5 : ZMod 80) * 16 = 0 by decide, zero_mul]

/-- Row fig2_layers (Figure 2's caption, s4_normfree.tex:72). -/
theorem fig2_layers_proved :
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
    (∀ j : ℕ, 1 ≤ j → j ≤ 4 → (fig2Layer j).image (fun k => 2 * k) = fig2Layer (j - 1)) := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fig2_topOrbits_facts, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [fig2Layer_eq]
  all_goals try rw [H18_blocksA_eq 4 (by norm_num) H25_three80]
  all_goals try rw [H18_blocksB_eq 4 (by norm_num) H25_three80]
  all_goals try rw [H18_blocksC_eq 4 (by norm_num) H25_three80]
  all_goals try rw [H18_topPairs_eq 4 (by norm_num) H25_three80]
  all_goals try rw [H18_topOrbits_eq 4 (by norm_num) H25_three80]
  all_goals decide +kernel

/-- Row intro_planar_H7 (P10s_main.tex:74): `H = {1, 2, 4}` in `F_7`. -/
theorem intro_planar_H7_proved : univ.filter (fun h : ZMod 7 => h ^ 3 = 1) = {1, 2, 4} := by
  decide

/-- Row intro_sigma_order (P10s_main.tex:174): `n/σ` is the order of `3` in `F_p^× ⧸ H`. -/
theorem intro_sigma_order_proved (n : ℕ) (h8 : 8 ∣ n) (hp : (pp n).Prime) {M : Type*} [Field M]
    (χ : MulChar (ZMod (pp n)) M)
    (g : (ZMod (pp n))ˣ) (hg : ∀ x : (ZMod (pp n))ˣ, x ∈ Subgroup.zpowers g)
    (hχg : IsPrimitiveRoot (χ (g : ZMod (pp n))) n) (ϖ : M) (hϖ : IsPrimitiveRoot ϖ n) (σ : ℕ) (hσ : σ ∣ n)
    (hσ0 : 0 < σ) (h3 : χ 3 = ϖ ^ σ) :
    (3 : ZMod (pp n)) ≠ 0 ∧
      ∀ u : (ZMod (pp n))ˣ, (u : ZMod (pp n)) = 3 →
        orderOf (QuotientGroup.mk u :
          (ZMod (pp n))ˣ ⧸ (powMonoidHom (n + 1) : (ZMod (pp n))ˣ →* (ZMod (pp n))ˣ).ker) = n / σ := by
  have := Fact.mk hp
  have hn8 : 8 ≤ n := H1_n_ge n h8 hp
  have hn0 : n ≠ 0 := by omega
  have hpn : pp n - 1 = n * (n + 1) := by
    unfold pp
    rw [Nat.add_sub_cancel]
    ring
  have hq : (pp n - 1) / n = n + 1 := by rw [hpn, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn0)]
  have h30 : (3 : ZMod (pp n)) ≠ 0 := by
    intro h
    have hdvd : pp n ∣ 3 := (CharP.cast_eq_zero_iff (ZMod (pp n)) (pp n) 3).1 (by exact_mod_cast h)
    have hle : pp n ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 73 ≤ pp n := by unfold pp; nlinarith
    omega
  refine ⟨h30, fun u hu => ?_⟩
  have hσeq := (sigma_of_n_proved n h8 hp χ g hg hχg ϖ hϖ σ hσ hσ0 h3).1
  rw [hq] at hσeq
  have hord : orderOf (QuotientGroup.mk u :
      (ZMod (pp n))ˣ ⧸ (powMonoidHom (n + 1) : (ZMod (pp n))ˣ →* (ZMod (pp n))ˣ).ker) =
      orderOf ((3 : ZMod (pp n)) ^ (n + 1)) := by
    rw [← hu, ← Units.val_pow_eq_pow_val, orderOf_units]
    apply orderOf_eq_orderOf_iff.mpr
    intro m
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, MonoidHom.mem_ker, powMonoidHom_apply, ← pow_mul, ← pow_mul,
      Nat.mul_comm]
  have hdvd : orderOf ((3 : ZMod (pp n)) ^ (n + 1)) ∣ n := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, Nat.mul_comm, ← hpn]
    exact ZMod.pow_card_sub_one_eq_one h30
  rw [hord, hσeq, Nat.div_div_self hdvd hn0]

end Xia.Proofs

#print axioms Xia.Proofs.fig2_layers_proved
#print axioms Xia.Proofs.intro_planar_H7_proved
#print axioms Xia.Proofs.intro_sigma_order_proved
