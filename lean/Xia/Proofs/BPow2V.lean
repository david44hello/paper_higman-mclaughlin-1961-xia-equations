/- Xia/Proofs/BPow2V.lean — proofs of the rows thm_B_pow2_V of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry
import Xia.Proofs.VcV
import Xia.Proofs.VBlocks

namespace Xia.Proofs

open Xia Finset

set_option linter.unusedSectionVars false

/-- `q = 3^{n/8} ≡ 1 (mod 4)` for `n = 2^{j+3}`, `j ≥ 1` (`n/8 = 2^j` is even). -/
theorem H37_qq_mod4 (j : ℕ) (hj : 1 ≤ j) : qq (2 ^ (j + 3)) % 4 = 1 := by
  unfold qq
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have h8 : 2 ^ (i + 1 + 3) / 8 = 2 * 2 ^ i := by
    rw [show 2 ^ (i + 1 + 3) = (2 * 2 ^ i) * 8 by ring, Nat.mul_div_cancel _ (by norm_num)]
  rw [h8, pow_mul, Nat.pow_mod]
  norm_num

/-- `ξ0^{(n/4) q} = ξ0^{n/4}` for `ξ0^n = 1`, `n = 2^{j+3}`, `j ≥ 1` (the paper's `q ≡ 1 + n/2 (mod n)` only through
`q ≡ 1 (mod 4)`). -/
theorem H37_pow_quarter (j : ℕ) (hj : 1 ≤ j) {F : Type*} [Field F] {ξ0 : F} (hξ : ξ0 ^ (2 ^ (j + 3)) = 1) :
    ξ0 ^ (2 ^ (j + 3) / 4 * qq (2 ^ (j + 3))) = ξ0 ^ (2 ^ (j + 3) / 4) := by
  have hq := H37_qq_mod4 j hj
  have hdec : qq (2 ^ (j + 3)) = 4 * (qq (2 ^ (j + 3)) / 4) + 1 := by omega
  have h4 : 2 ^ (j + 3) / 4 * 4 = 2 ^ (j + 3) := by
    rw [show 2 ^ (j + 3) = 2 ^ (j + 1) * 4 by ring, Nat.mul_div_cancel _ (by norm_num)]
  rw [hdec, mul_add, mul_one, ← mul_assoc, h4, pow_add, pow_mul, hξ, one_pow, one_mul]

/-- `|O| = n/4` for `O = orbit 3 1`, `n = 2^{j+3}`. -/
theorem H37_card (j : ℕ) : (orbit 3 (1 : ZMod (2 ^ (j + 3)))).card = 2 ^ (j + 3) / 4 := by
  rw [H3_orbit_one_card j, show 2 ^ (j + 3) = 2 ^ (j + 1) * 4 by ring, Nat.mul_div_cancel _ (by norm_num)]

/-- `2 (n/4) = n/2` for `n = 2^{j+3}`. -/
theorem H37_two_quarter (j : ℕ) : 2 * (2 ^ (j + 3) / 4) = 2 ^ (j + 3) / 2 := by
  obtain ⟨M, hM⟩ : ∃ M, 2 ^ (j + 3) = 8 * M := ⟨2 ^ j, by ring⟩
  rw [hM]
  omega

theorem H37_val_one (j : ℕ) : (1 : ZMod (2 ^ (j + 3))).val = 1 := by
  apply ZMod.val_one''
  have : 2 ^ 3 ≤ 2 ^ (j + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- Row thm_B_pow2_V — Theorem B (P10s_main.tex:193), the sentence for `n = 2^e`, `e ≥ 5` odd. -/
theorem thm_B_pow2_V_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 5 ≤ e) (heo : Odd e) (ξ0 : GaloisField 3 (n / 2))
    (hξ0 : IsPrimitiveRoot ξ0 n) (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2) :
    let ν := nuData (topOf ξ0 y)
    Set.BijOn (fun v : ZMod n → GaloisField 3 (n / 2) => v 1) (Vfib ξ0 ν) (Vsp n) ∧
    (∀ y' ∈ fibre ξ0 y, topOf ξ0 y' 1 = dftA ξ0 y' 1) ∧
    Set.InjOn (fun y' : ZMod n → GaloisField 3 (n / 2) => dftA ξ0 y' 1) (fibre ξ0 y) ∧
    (∀ v ∈ Vfib ξ0 ν, Tsh v 1 = Tmap n ξ0 (v 1)) ∧
    ∀ y' ∈ fibre ξ0 y, dftA ξ0 (ySubst y') 1 = Tmap n ξ0 (dftA ξ0 y' 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, e = j + 3 := ⟨e - 3, by omega⟩
  subst hne
  intro ν
  have hN : (2 : ℕ) ^ (j + 3) = 2 ^ (j + 3) * 1 := (mul_one _).symm
  have h3 : ¬ 3 ∣ 2 ^ (j + 3) := H4_not3_of_pow2 rfl
  have h4 : 4 ∣ 2 ^ (j + 3) := ⟨2 ^ (j + 1), by ring⟩
  have hev : Even (2 ^ (j + 3)) := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h4)
  obtain ⟨-, -, -, -, hfib, hinj, -⟩ :=
    thm_5_1_c_V_proved (2 ^ (j + 3)) (j + 3) 1 hN (by omega) odd_one h3 ξ0 hξ0 y hy
  obtain ⟨hpart1, -, hA, -, -⟩ :=
    thm_5_1_c_V_blocks_proved (2 ^ (j + 3)) (j + 3) 1 hN (by omega) odd_one h3 ξ0 hξ0 y hy
  obtain ⟨hbl, hblA, -, -, hqO⟩ := H19_pow2_blocks j (by omega)
  have hval1 := H37_val_one j
  have hodd1 : Odd (1 : ZMod (2 ^ (j + 3))).val := by rw [hval1]; exact odd_one
  have hB0A : ({orbit 3 1, inv (orbit 3 1)} : Finset (Finset (ZMod (2 ^ (j + 3))))) ∈ blocksA (2 ^ (j + 3)) := by
    rw [hblA]; exact mem_singleton_self _
  obtain ⟨hbij, hT⟩ := hA _ hB0A (orbit 3 1) (mem_insert_self _ _) 1 (H6_self_mem 3 1)
  -- the single block carries all of V
  have hVeq : VfibBlock ξ0 ν ({orbit 3 1, inv (orbit 3 1)} : Finset (Finset (ZMod (2 ^ (j + 3))))) = Vfib ξ0 ν := by
    ext h
    refine ⟨fun hh => hh.1, fun hh => ⟨hh, fun k hk => ?_⟩⟩
    have hsum := (hpart1 h hh).2
    rw [hbl, sum_singleton] at hsum
    calc h k = restrictBlock ({orbit 3 1, inv (orbit 3 1)} : Finset (Finset (ZMod (2 ^ (j + 3))))) h k :=
          congrFun hsum k
      _ = 0 := by unfold restrictBlock; exact ite_eq_right hk
  -- the case-A target set is `V = {x | x^Q = -x}`
  have hset : {t : GaloisField 3 (2 ^ (j + 3) / 2) | t ^ (3 ^ (orbit 3 (1 : ZMod (2 ^ (j + 3)))).card) =
      (ξ0 ^ (1 : ZMod (2 ^ (j + 3))).val)⁻¹ ^ (2 * (orbit 3 (1 : ZMod (2 ^ (j + 3)))).card) * t} =
      Vsp (2 ^ (j + 3)) := by
    ext t
    simp only [Set.mem_ofPred_eq, Vsp, QQ]
    rw [H37_card j, hval1, pow_one, inv_pow, H37_two_quarter j, H7_pow_half_eq_neg_one hev hξ0, inv_neg, inv_one,
      neg_one_mul]
  have hbij1 : Set.BijOn (fun v : ZMod (2 ^ (j + 3)) → GaloisField 3 (2 ^ (j + 3) / 2) => v 1) (Vfib ξ0 ν)
      (Vsp (2 ^ (j + 3))) := by
    rw [← hVeq, ← hset]; exact hbij
  -- `T` in the coordinate `v(ξ0)`
  have hT4 : ∀ v ∈ Vfib ξ0 ν, Tsh v 1 = Tmap (2 ^ (j + 3)) ξ0 (v 1) := by
    intro v hv
    have hv' : v ∈ VfibBlock ξ0 ν ({orbit 3 1, inv (orbit 3 1)} : Finset (Finset (ZMod (2 ^ (j + 3))))) := by
      rw [hVeq]; exact hv
    unfold Tmap iota
    rw [(hT v hv').1, H37_card j, hval1, pow_one, hqO, H37_pow_quarter j (by omega) hξ0.pow_eq_one]
  refine ⟨hbij1, fun y' _ => H26_topOf_odd ξ0 y' hodd1, ?_, hT4, ?_⟩
  · intro y1 hy1 y2 hy2 heq
    apply hinj hy1 hy2
    apply hbij1.injOn (hfib y1 hy1).1 (hfib y2 hy2).1
    show topOf ξ0 y1 1 = topOf ξ0 y2 1
    rw [H26_topOf_odd ξ0 y1 hodd1, H26_topOf_odd ξ0 y2 hodd1]
    exact heq
  · intro y' hy'
    rw [← H26_topOf_odd ξ0 (ySubst y') hodd1, (hfib y' hy').2, hT4 _ (hfib y' hy').1, H26_topOf_odd ξ0 y' hodd1]

end Xia.Proofs

#print axioms Xia.Proofs.thm_B_pow2_V_proved
