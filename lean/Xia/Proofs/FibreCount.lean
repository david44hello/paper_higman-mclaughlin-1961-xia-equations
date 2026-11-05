/- Xia/Proofs/FibreCount.lean — proofs of the rows thm_5_1_c_count of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import Xia.Defs.Symmetry
import Xia.Defs.Layer0
import Xia.Proofs.Sec5
import Xia.Proofs.Thm41Steps26
import Xia.Proofs.Prop24

namespace Xia.Proofs

open Xia Finset

set_option linter.unusedSectionVars false

/-! ## Part 1 — the groups `K'` and `D0^inv`; a fibre is in bijection with `K'` -/

section KSet

/-- `K'`: homogeneous top data with `λ(k + m) = λ(k)⁻¹` on odd `k` (the top data of a fibre, divided by `ŷ`). -/
def H22_K (n : ℕ) [NeZero n] (L : Type*) [Field L] : Set (ZMod n → L) :=
  {lam | lam ∈ (topData0 n 3 : Set (ZMod n → L)) ∧ ∀ k : ZMod n, Odd k.val → lam (k + half n) = (lam k)⁻¹}

/-- `D0^inv`: homogeneous top data with `λ(k + m) = λ(k)` on odd `k`. -/
def H22_D (n : ℕ) [NeZero n] (L : Type*) [Field L] : Set (ZMod n → L) :=
  {lam | lam ∈ (topData0 n 3 : Set (ZMod n → L)) ∧ ∀ k : ZMod n, Odd k.val → lam (k + half n) = lam k}

variable {n : ℕ} [NeZero n]

theorem H22_T0_ne {L : Type*} [Field L] {lam : ZMod n → L} (hl : lam ∈ (topData0 n 3 : Set (ZMod n → L)))
    {k : ZMod n} (hk : Odd k.val) : lam k ≠ 0 :=
  left_ne_zero_of_mul_eq_one (hl.1 k hk).2

/-- The map `y' ↦ ŷ'/ŷ` on the top layer (value 1 on the lower layers). -/
noncomputable def H22_Phi {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L)
    (y : ZMod n → GaloisField 3 (n / 2)) (y' : ZMod n → GaloisField 3 (n / 2)) : ZMod n → L :=
  fun k => if Odd k.val then dftA ω y' k / dftA ω y k else 1

theorem H22_fibre_bij (hev : Even n) (h4 : 4 ∣ n) (h3 : ¬ 3 ∣ n) {L : Type*} [Field L]
    [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n) (y : ZMod n → GaloisField 3 (n / 2))
    (hy : y ∈ NFSet n 2) : Set.BijOn (H22_Phi ω y) (fibre ω y) (H22_K n L) := by
  have h2 : 2 ∣ n := even_iff_two_dvd.mp hev
  have hP := prop_2_4_bij_proved n hev h3 ω hω
  have hω0 : ω ≠ 0 := hω.ne_zero (NeZero.ne n)
  obtain ⟨hF1, hF3, hF4⟩ := hP.mapsTo hy
  have hne : ∀ k, dftA ω y k ≠ 0 := H5_F3_ne hω0 _ hF3
  have hpw : ∀ (k : ZMod n) (z : ℤ), (ω ^ k.val) ^ z ≠ 0 := fun k z => zpow_ne_zero _ (pow_ne_zero _ hω0)
  have hpn : ∀ (k : ZMod n) (z : ℕ), (ω ^ k.val) ^ z ≠ 0 := fun k z => pow_ne_zero _ (pow_ne_zero _ hω0)
  have hhe : Even (half n).val := H19_even_half h4
  have hPhiO : ∀ y' k, Odd k.val → H22_Phi ω y y' k = dftA ω y' k / dftA ω y k := fun y' k hk => by
    simp only [H22_Phi, hk, ite_true]
  have hPhiE : ∀ y' k, Even k.val → H22_Phi ω y y' k = 1 := fun y' k hk => by
    simp only [H22_Phi, Nat.not_odd_iff_even.mpr hk, ite_false]
  refine ⟨fun y' hy' => ?_, fun y1 hy1 y2 hy2 heq => ?_, fun lam hlam => ?_⟩
  · obtain ⟨hyN, hfib⟩ := hy'
    obtain ⟨hF1', hF3', hF4'⟩ := hP.mapsTo hyN
    refine ⟨⟨fun k hk => ⟨?_, ?_⟩, fun k hk => hPhiE y' k hk⟩, fun k hk => ?_⟩
    · rw [hPhiO _ _ (H19_odd_three_mul h2 hk), hPhiO _ _ hk, hF1' k, hF1 k, div_pow,
        mul_div_mul_left _ _ (hpw k _)]
    · rw [hPhiO _ _ hk, hPhiO _ _ (H6_odd_neg h2 hk), div_mul_div_comm, hF3' k, hF3 k, div_self (hpn k _)]
    · apply eq_inv_of_mul_eq_one_right
      rw [hPhiO _ _ hk, hPhiO _ _ (H19_odd_add_half h2 h4 hk), div_mul_div_comm, hF4' k, hF4 k,
        hfib _ hhe, hfib _ (H19_even_two_mul h2 k)]
      exact div_self (mul_ne_zero (hne _) (hne _))
  · apply hP.injOn hy1.1 hy2.1
    funext k
    rcases Nat.even_or_odd k.val with hk | hk
    · rw [hy1.2 k hk, hy2.2 k hk]
    · have e := congrFun heq k
      rw [hPhiO _ _ hk, hPhiO _ _ hk] at e
      exact (div_left_inj' (hne k)).mp e
  · obtain ⟨⟨htop, hone⟩, hK⟩ := hlam
    set H : ZMod n → L := fun k => if Odd k.val then lam k * dftA ω y k else dftA ω y k with hH
    have hHO : ∀ k : ZMod n, Odd k.val → H k = lam k * dftA ω y k := fun k hk => by
      rw [hH]; simp only [hk, ite_true]
    have hHE : ∀ k : ZMod n, Even k.val → H k = dftA ω y k := fun k hk => by
      rw [hH]; simp only [Nat.not_odd_iff_even.mpr hk, ite_false]
    have hHF : H ∈ {h | F1 3 2 ω h ∧ F3 ω h ∧ F4 h} := by
      refine ⟨fun k => ?_, fun k => ?_, fun k => ?_⟩
      · rcases Nat.even_or_odd k.val with hk | hk
        · rw [hHE _ hk, hHE _ (H19_even_three_mul h2 hk)]; exact hF1 k
        · rw [hHO _ hk, hHO _ (H19_odd_three_mul h2 hk), (htop k hk).1, hF1 k]; ring
      · rcases Nat.even_or_odd k.val with hk | hk
        · rw [hHE _ hk, hHE _ (H19_even_neg h2 hk)]; exact hF3 k
        · rw [hHO _ hk, hHO _ (H6_odd_neg h2 hk)]
          calc lam k * dftA ω y k * (lam (-k) * dftA ω y (-k))
              = (lam k * lam (-k)) * (dftA ω y k * dftA ω y (-k)) := by ring
            _ = (ω ^ k.val) ^ (n / 2) := by rw [(htop k hk).2, hF3 k, one_mul]
      · rw [hHE _ hhe, hHE _ (H19_even_two_mul h2 k)]
        rcases Nat.even_or_odd k.val with hk | hk
        · rw [hHE _ hk, hHE _ (H19_even_add_half h2 h4 hk)]; exact hF4 k
        · rw [hHO _ hk, hHO _ (H19_odd_add_half h2 h4 hk), hK k hk, ← hF4 k]
          have hl0 : lam k ≠ 0 := left_ne_zero_of_mul_eq_one (htop k hk).2
          field_simp
    obtain ⟨y', hy', hy'H⟩ := hP.surjOn hHF
    refine ⟨y', ⟨hy', fun k hk => ?_⟩, ?_⟩
    · rw [hy'H, hHE _ hk]
    · funext k
      rcases Nat.even_or_odd k.val with hk | hk
      · rw [hPhiE _ _ hk, hone k hk]
      · rw [hPhiO _ _ hk, hy'H, hHO _ hk, mul_div_assoc, div_self (hne k), mul_one]

/-- `ŷ` computed in an extension `L'` of `L` is the image of `ŷ` computed in `L`. -/
theorem H22_dftA_map {L L' : Type*} [Field L] [Field L'] [Algebra (GaloisField 3 (n / 2)) L]
    [Algebra (GaloisField 3 (n / 2)) L'] [Algebra L L'] [IsScalarTower (GaloisField 3 (n / 2)) L L'] (ω : L)
    (y : ZMod n → GaloisField 3 (n / 2)) (k : ZMod n) :
    dftA (algebraMap L L' ω) y k = algebraMap L L' (dftA ω y k) := by
  unfold dftA dft
  rw [map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, map_pow, map_pow, ← IsScalarTower.algebraMap_apply]

/-- Fibres do not change when `L` is enlarged. -/
theorem H22_fibre_map {L L' : Type*} [Field L] [Field L'] [Algebra (GaloisField 3 (n / 2)) L]
    [Algebra (GaloisField 3 (n / 2)) L'] [Algebra L L'] [IsScalarTower (GaloisField 3 (n / 2)) L L'] (ω : L)
    (y : ZMod n → GaloisField 3 (n / 2)) : fibre (algebraMap L L' ω) y = fibre ω y := by
  ext y'
  simp only [fibre, Set.mem_ofPred_eq, H22_dftA_map, (algebraMap L L').injective.eq_iff]

end KSet

/-! ## Part 2 — blocks: representatives, the cases are block invariants, `blockLen = |O|` -/

section Blocks

variable {n : ℕ} [NeZero n]

/-- A representative `ρ_B` (odd) of a block `B`: `B = blockOf (orbit 3 ρ_B)`. -/
noncomputable def H22_rep (B : Finset (Finset (ZMod n))) : ZMod n :=
  if h : ∃ k : ZMod n, Odd k.val ∧ B = blockOf (orbit 3 k) then Classical.choose h else 0

theorem H22_rep_spec {B : Finset (Finset (ZMod n))} (hB : B ∈ blocks n) :
    Odd (H22_rep B).val ∧ B = blockOf (orbit 3 (H22_rep B)) := by
  have h := H19_mem_blocks hB
  rw [H22_rep, dite_eq_left h]
  exact Classical.choose_spec h

theorem H22_self_mem_blockOf (O : Finset (ZMod n)) : O ∈ blockOf O := by
  unfold blockOf; simp

theorem H22_blockOf_mem_blocks {k : ZMod n} (hk : Odd k.val) : blockOf (orbit 3 k) ∈ blocks n :=
  mem_image.mpr ⟨orbit 3 k, mem_image.mpr ⟨k, mem_filter.mpr ⟨mem_univ _, hk⟩, rfl⟩, rfl⟩

theorem H22_orbit_mem_topOrbits {k : ZMod n} (hk : Odd k.val) : orbit 3 k ∈ topOrbits n 3 :=
  mem_image.mpr ⟨k, mem_filter.mpr ⟨mem_univ _, hk⟩, rfl⟩

theorem H22_inv_inj {O O' : Finset (ZMod n)} (h : inv O = inv O') : O = O' := by
  have := congrArg inv h
  rwa [H3_inv_inv, H3_inv_inv] at this

theorem H22_caseA_iff (hev : Even n) (O : Finset (ZMod n)) : (∃ O' ∈ blockOf O, IsCaseA O') ↔ IsCaseA O := by
  refine ⟨fun ⟨O', hO', hA⟩ => ?_, fun h => ⟨O, H22_self_mem_blockOf O, h⟩⟩
  unfold IsCaseA at hA ⊢
  unfold blockOf at hO'
  simp only [mem_insert, mem_singleton] at hO'
  rcases hO' with rfl | rfl | rfl | rfl
  · exact hA
  · rw [H19_negO_inv hev] at hA
    exact H22_inv_inj hA
  · rw [H19_negO_negO hev] at hA
    exact hA.symm
  · rw [H19_negO_negO hev, H19_negO_inv hev] at hA
    exact (H22_inv_inj hA).symm

theorem H22_caseB_iff (hev : Even n) (O : Finset (ZMod n)) : (∃ O' ∈ blockOf O, IsCaseB O') ↔ IsCaseB O := by
  refine ⟨fun ⟨O', hO', hB⟩ => ?_, fun h => ⟨O, H22_self_mem_blockOf O, h⟩⟩
  unfold IsCaseB at hB ⊢
  unfold blockOf at hO'
  simp only [mem_insert, mem_singleton] at hO'
  rcases hO' with rfl | rfl | rfl | rfl
  · exact hB
  · rw [H19_negO_inv hev, H3_inv_inv] at hB
    apply H22_inv_inj
    rw [hB, H3_inv_inv]
  · rw [H19_negO_negO hev] at hB
    conv_rhs => rw [hB]
    rw [H3_inv_inv]
  · rw [H19_negO_negO hev, H19_negO_inv hev, H3_inv_inv] at hB
    exact hB.symm

theorem H22_card_negO (O : Finset (ZMod n)) : (negO O).card = O.card :=
  card_image_of_injective O (add_left_injective _)

/-- The members of `blockOf (orbit 3 ρ)` are orbits of the same size as `orbit 3 ρ`. -/
theorem H22_blockOf_orbits (hev : Even n) (ρ : ZMod n) :
    ∀ O' ∈ blockOf (orbit 3 ρ), (∃ z : ZMod n, O' = orbit 3 z) ∧ O'.card = (orbit 3 ρ).card := by
  intro O' hO'
  unfold blockOf at hO'
  simp only [mem_insert, mem_singleton] at hO'
  rcases hO' with rfl | rfl | rfl | rfl
  · exact ⟨⟨ρ, rfl⟩, rfl⟩
  · exact ⟨⟨-ρ, H6_inv_orbit 3 ρ⟩, H6_card_inv _⟩
  · exact ⟨⟨ρ + half n, H19_negO_orbit hev ρ⟩, H22_card_negO _⟩
  · refine ⟨⟨-ρ + half n, by rw [H6_inv_orbit, H19_negO_orbit hev]⟩, ?_⟩
    rw [H22_card_negO, H6_card_inv]

theorem H22_orbits_disj (h3 : ¬ 3 ∣ n) {z1 z2 : ZMod n} (hne : orbit 3 z1 ≠ orbit 3 z2) :
    Disjoint (orbit 3 z1) (orbit 3 z2) := by
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  exact hne ((H6_orbit_eq hcop hx1).symm.trans (H6_orbit_eq hcop hx2))

theorem H22_blockLen (hev : Even n) (h3 : ¬ 3 ∣ n) (ρ : ZMod n) :
    blockLen (blockOf (orbit 3 ρ)) = (orbit 3 ρ).card := by
  classical
  have horb := H22_blockOf_orbits hev ρ
  have hdisj : ((blockOf (orbit 3 ρ) : Finset (Finset (ZMod n))) : Set (Finset (ZMod n))).PairwiseDisjoint id := by
    intro O1 h1 O2 h2 hne
    obtain ⟨⟨z1, rfl⟩, -⟩ := horb O1 h1
    obtain ⟨⟨z2, rfl⟩, -⟩ := horb O2 h2
    exact H22_orbits_disj h3 hne
  have hpos : 0 < (blockOf (orbit 3 ρ)).card := card_pos.mpr ⟨_, H22_self_mem_blockOf _⟩
  unfold blockLen
  rw [card_biUnion hdisj, sum_congr rfl (fun O' hO' => show (id O').card = _ from (horb O' hO').2), sum_const,
    smul_eq_mul,
    Nat.mul_div_cancel_left _ hpos]

theorem H22_orbit_card_pos (ρ : ZMod n) : 0 < (orbit 3 ρ).card := card_pos.mpr ⟨ρ, H6_self_mem 3 ρ⟩

end Blocks

/-! ## Part 3 — upper bounds: `|G| ≤ ∏_B M_B` by `λ ↦ (λ(ρ_B))_B` -/

section Upper

variable {n : ℕ} [NeZero n]

/-- On a block, a homogeneous top datum with `λ(x+m) = f(λ(x))` is a function of its value at the representative. -/
theorem H22_determined (hev : Even n) {L : Type*} [Field L] (f : L → L) {ρ k : ZMod n}
    (hρ : Odd ρ.val) (hk : orbit 3 k ∈ blockOf (orbit 3 ρ)) :
    ∃ g : L → L, ∀ lam ∈ (topData0 n 3 : Set (ZMod n → L)),
      (∀ x : ZMod n, Odd x.val → lam (x + half n) = f (lam x)) → lam k = g (lam ρ) := by
  have h2 : 2 ∣ n := even_iff_two_dvd.mp hev
  have hkk : k ∈ orbit 3 k := H6_self_mem 3 k
  unfold blockOf at hk
  simp only [mem_insert, mem_singleton] at hk
  rcases hk with h | h | h | h <;> rw [h] at hkk
  · obtain ⟨i, rfl⟩ := (H11_mem_orbit _ _).mp hkk
    exact ⟨fun t => t ^ (3 ^ i), fun lam hl _ => H11_T0_pow h2 hl hρ i⟩
  · obtain ⟨i, hi⟩ := (H11_mem_orbit _ _).mp ((H11_mem_inv _ _).mp hkk)
    refine ⟨fun t => (t ^ (3 ^ i))⁻¹, fun lam hl _ => ?_⟩
    have hodd : Odd (-k).val := by rw [hi]; exact H11_pow_odd h2 i hρ
    have e := H11_T0_neg hl hodd
    rw [neg_neg, hi, H11_T0_pow h2 hl hρ i] at e
    exact e
  · obtain ⟨z, hz, rfl⟩ := mem_image.mp hkk
    obtain ⟨i, rfl⟩ := (H11_mem_orbit _ _).mp hz
    exact ⟨fun t => f (t ^ (3 ^ i)), fun lam hl hf => by
      rw [hf _ (H11_pow_odd h2 i hρ), H11_T0_pow h2 hl hρ i]⟩
  · obtain ⟨z, hz, rfl⟩ := mem_image.mp hkk
    obtain ⟨i, hi⟩ := (H11_mem_orbit _ _).mp ((H11_mem_inv _ _).mp hz)
    have hodd : Odd (-z).val := by rw [hi]; exact H11_pow_odd h2 i hρ
    have hzodd : Odd z.val := by have := H6_odd_neg h2 hodd; rwa [neg_neg] at this
    refine ⟨fun t => f (t ^ (3 ^ i))⁻¹, fun lam hl hf => ?_⟩
    have e := H11_T0_neg hl hodd
    rw [neg_neg, hi, H11_T0_pow h2 hl hρ i] at e
    rw [hf _ hzodd, e]

theorem H22_nthRoots_card {L : Type*} [Field L] (M : ℕ) : (Polynomial.nthRootsFinset M (1 : L)).card ≤ M := by
  classical
  rw [Polynomial.nthRootsFinset_def]
  exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)

/-- The generic upper bound. -/
theorem H22_upper (hev : Even n) (_h4 : 4 ∣ n) {L : Type*} [Field L] (G : Set (ZMod n → L))
    (hG : G ⊆ (topData0 n 3 : Set (ZMod n → L))) (f : L → L)
    (hf : ∀ lam ∈ G, ∀ x : ZMod n, Odd x.val → lam (x + half n) = f (lam x))
    (M : Finset (Finset (ZMod n)) → ℕ) (hM : ∀ B ∈ blocks n, 0 < M B)
    (hroot : ∀ lam ∈ G, ∀ B ∈ blocks n, lam (H22_rep B) ^ M B = 1) :
    G.Finite ∧ Nat.card G ≤ ∏ B ∈ blocks n, M B := by
  classical
  let T : Finset ((blocks n) → L) :=
    Fintype.piFinset (fun B : blocks n => Polynomial.nthRootsFinset (M B.1) (1 : L))
  let Φ : (ZMod n → L) → (blocks n → L) := fun lam B => lam (H22_rep B.1)
  have hmaps : Set.MapsTo Φ G (T : Set ((blocks n) → L)) := by
    intro lam hl
    rw [mem_coe, Fintype.mem_piFinset]
    intro B
    rw [Polynomial.mem_nthRootsFinset (hM B.1 B.2)]
    exact hroot lam hl B.1 B.2
  have hinj : Set.InjOn Φ G := by
    intro l1 h1 l2 h2 heq
    funext k
    rcases Nat.even_or_odd k.val with hk | hk
    · rw [(hG h1).2 k hk, (hG h2).2 k hk]
    · have hB := H22_blockOf_mem_blocks hk
      obtain ⟨hρ, hBeq⟩ := H22_rep_spec hB
      have hkmem : orbit 3 k ∈ blockOf (orbit 3 (H22_rep (blockOf (orbit 3 k)))) := by
        rw [← hBeq]; exact H22_self_mem_blockOf _
      obtain ⟨g, hg⟩ := H22_determined hev f hρ hkmem
      rw [hg l1 (hG h1) (hf l1 h1), hg l2 (hG h2) (hf l2 h2)]
      exact congrArg g (congrFun heq ⟨_, hB⟩)
  have hfin : G.Finite := Set.Finite.of_injOn hmaps hinj T.finite_toSet
  refine ⟨hfin, ?_⟩
  rw [Nat.card_coe_set_eq]
  calc G.ncard ≤ (T : Set ((blocks n) → L)).ncard := Set.ncard_le_ncard_of_injOn Φ hmaps hinj
    _ = T.card := Set.ncard_coe_finset T
    _ = ∏ B : blocks n, (Polynomial.nthRootsFinset (M B.1) (1 : L)).card := Fintype.card_piFinset _
    _ ≤ ∏ B : blocks n, M B.1 := prod_le_prod (fun B _ => H22_nthRoots_card _)
    _ = ∏ B ∈ blocks n, M B := prod_coe_sort (blocks n) M

end Upper

/-! ## Part 4 — the per-block orders: case A `q±1`, case B `q∓1`, case C `3^L-1` -/

section Orders

variable {n : ℕ} [NeZero n]

open Classical in
/-- The factor of a block in `Φ = fibreSize` (Table: "In Φ"). -/
noncomputable def H22_mK (B : Finset (Finset (ZMod n))) : ℕ :=
  if ∃ O ∈ B, IsCaseA O then qO B + 1 else if ∃ O ∈ B, IsCaseB O then qO B - 1 else 3 ^ blockLen B - 1

open Classical in
/-- The factor of a block in `fibreProd` (Table: "In fibres"). -/
noncomputable def H22_mD (B : Finset (Finset (ZMod n))) : ℕ :=
  if ∃ O ∈ B, IsCaseA O then qO B - 1 else if ∃ O ∈ B, IsCaseB O then qO B + 1 else 3 ^ blockLen B - 1

theorem H22_pow_sub_one {L : Type*} [Field L] {t : L} (ht : t ≠ 0) {N : ℕ} (h : t ^ N = t) : t ^ (N - 1) = 1 := by
  rcases N with _ | N
  · simp
  · rw [pow_succ] at h
    simp only [Nat.add_sub_cancel]
    exact mul_right_cancel₀ ht (by rw [one_mul]; exact h)

/-- The facts about a block used below, all in terms of its representative `ρ`. -/
theorem H22_block_facts {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {B : Finset (Finset (ZMod n))} (hB : B ∈ blocks n) :
    Odd (H22_rep B).val ∧ blockLen B = (orbit 3 (H22_rep B)).card ∧
      qO B = 3 ^ ((orbit 3 (H22_rep B)).card / 2) ∧
      (3 : ZMod n) ^ (orbit 3 (H22_rep B)).card * H22_rep B = H22_rep B ∧
      ((∃ O ∈ B, IsCaseA O) → H22_rep B + half n = 3 ^ ((orbit 3 (H22_rep B)).card / 2) * H22_rep B ∧
        1 ≤ (orbit 3 (H22_rep B)).card / 2) ∧
      ((∃ O ∈ B, IsCaseB O) → H22_rep B + half n = -(3 ^ ((orbit 3 (H22_rep B)).card / 2) * H22_rep B) ∧
        1 ≤ (orbit 3 (H22_rep B)).card / 2) := by
  have h8 := H19_eight_dvd hn ha
  have h4 := H19_four_dvd hn ha
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hev : Even n := even_iff_two_dvd.mpr h2
  have hn2 : 2 ≤ n := Nat.le_of_dvd (NeZero.pos n) h2
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  obtain ⟨hρ, hBeq⟩ := H22_rep_spec hB
  generalize H22_rep B = ρ at hρ hBeq ⊢
  subst hBeq
  have hlen := H22_blockLen hev h3 ρ
  have hpos := H22_orbit_card_pos ρ
  have hmemT := H22_orbit_mem_topOrbits hρ
  have hρm : ρ + half n ∈ negO (orbit 3 ρ) := mem_image_of_mem _ (H6_self_mem 3 ρ)
  refine ⟨hρ, hlen, by unfold qO; rw [hlen], (H19_pow_eq_self_iff' hcop (H6_self_mem 3 ρ) _).mpr dvd_rfl,
    fun hA => ?_, fun hB' => ?_⟩
  · rw [H22_caseA_iff hev] at hA
    have hev' := caseAB_even_proved n a nodd hn ha hodd h3 _ hmemT (Or.inl hA)
    refine ⟨H19_caseA_pow hcop hev hn2 (by rw [← hA]; exact hρm), ?_⟩
    obtain ⟨c, hc⟩ := hev'
    omega
  · rw [H22_caseB_iff hev] at hB'
    have hev' := caseAB_even_proved n a nodd hn ha hodd h3 _ hmemT (Or.inr hB')
    have hinv : ρ + half n ∈ inv (orbit 3 ρ) := by rw [← hB']; exact hρm
    refine ⟨H19_caseB_pow hcop h8 hρ ((H11_mem_inv _ _).mp hinv), ?_⟩
    obtain ⟨c, hc⟩ := hev'
    omega

theorem H22_three_le {c : ℕ} (hc : 1 ≤ c) : 3 ≤ 3 ^ c :=
  calc 3 = 3 ^ 1 := by norm_num
    _ ≤ 3 ^ c := Nat.pow_le_pow_right (by norm_num) hc

theorem H22_mK_pos {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {B : Finset (Finset (ZMod n))} (hB : B ∈ blocks n) : 0 < H22_mK B := by
  obtain ⟨-, hlen, hq, -, hA, hBc⟩ := H22_block_facts hn ha hodd h3 hB
  have hpos := H22_orbit_card_pos (H22_rep B)
  unfold H22_mK
  split_ifs with h1 h2
  · omega
  · have := H22_three_le (hBc h2).2; omega
  · rw [hlen]; exact H11_three_pow_sub_one_pos hpos

theorem H22_mD_pos {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {B : Finset (Finset (ZMod n))} (hB : B ∈ blocks n) : 0 < H22_mD B := by
  obtain ⟨-, hlen, hq, -, hA, hBc⟩ := H22_block_facts hn ha hodd h3 hB
  have hpos := H22_orbit_card_pos (H22_rep B)
  unfold H22_mD
  split_ifs with h1 h2
  · have := H22_three_le (hA h1).2; omega
  · omega
  · rw [hlen]; exact H11_three_pow_sub_one_pos hpos

theorem H22_rootK {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type*} [Field L] {lam : ZMod n → L} (hl : lam ∈ H22_K n L) {B : Finset (Finset (ZMod n))}
    (hB : B ∈ blocks n) : lam (H22_rep B) ^ H22_mK B = 1 := by
  have h2 : 2 ∣ n := dvd_trans (by norm_num) (H19_four_dvd hn ha)
  obtain ⟨hρ, hlen, hq, hper, hA, hBc⟩ := H22_block_facts hn ha hodd h3 hB
  have hne := H22_T0_ne hl.1 hρ
  have k1 := hl.2 _ hρ
  unfold H22_mK
  split_ifs with c1 c2
  · rw [(hA c1).1, H11_T0_pow h2 hl.1 hρ] at k1
    rw [hq, pow_succ, k1, inv_mul_cancel₀ hne]
  · rw [(hBc c2).1, H11_T0_neg hl.1 (H11_pow_odd h2 _ hρ), H11_T0_pow h2 hl.1 hρ, inv_inj] at k1
    rw [hq]; exact H22_pow_sub_one hne k1
  · have e := H11_T0_pow h2 hl.1 hρ (orbit 3 (H22_rep B)).card
    rw [hper] at e
    rw [hlen]; exact H22_pow_sub_one hne e.symm

theorem H22_rootD {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type*} [Field L] {lam : ZMod n → L} (hl : lam ∈ H22_D n L) {B : Finset (Finset (ZMod n))}
    (hB : B ∈ blocks n) : lam (H22_rep B) ^ H22_mD B = 1 := by
  have h2 : 2 ∣ n := dvd_trans (by norm_num) (H19_four_dvd hn ha)
  obtain ⟨hρ, hlen, hq, hper, hA, hBc⟩ := H22_block_facts hn ha hodd h3 hB
  have hne := H22_T0_ne hl.1 hρ
  have k1 := hl.2 _ hρ
  unfold H22_mD
  split_ifs with c1 c2
  · rw [(hA c1).1, H11_T0_pow h2 hl.1 hρ] at k1
    rw [hq]; exact H22_pow_sub_one hne k1
  · rw [(hBc c2).1, H11_T0_neg hl.1 (H11_pow_odd h2 _ hρ), H11_T0_pow h2 hl.1 hρ] at k1
    have e : lam (H22_rep B) ^ 3 ^ ((orbit 3 (H22_rep B)).card / 2) *
        (lam (H22_rep B) ^ 3 ^ ((orbit 3 (H22_rep B)).card / 2))⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hne)
    rw [k1] at e
    rw [hq, pow_succ, e]
  · have e := H11_T0_pow h2 hl.1 hρ (orbit 3 (H22_rep B)).card
    rw [hper] at e
    rw [hlen]; exact H22_pow_sub_one hne e.symm

theorem H22_K_le {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    (L : Type*) [Field L] : (H22_K n L).Finite ∧ Nat.card (H22_K n L) ≤ ∏ B ∈ blocks n, H22_mK B := by
  have h4 := H19_four_dvd hn ha
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h4)
  exact H22_upper hev h4 (H22_K n L) (fun _ hl => hl.1) Inv.inv (fun _ hl => hl.2) H22_mK
    (fun _ hB => H22_mK_pos hn ha hodd h3 hB) (fun _ hl _ hB => H22_rootK hn ha hodd h3 hl hB)

theorem H22_D_le {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    (L : Type*) [Field L] : (H22_D n L).Finite ∧ Nat.card (H22_D n L) ≤ ∏ B ∈ blocks n, H22_mD B := by
  have h4 := H19_four_dvd hn ha
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h4)
  exact H22_upper hev h4 (H22_D n L) (fun _ hl => hl.1) id (fun _ hl => hl.2) H22_mD
    (fun _ hB => H22_mD_pos hn ha hodd h3 hB) (fun _ hl _ hB => H22_rootD hn ha hodd h3 hl hB)

/-- Exclusivity of the three cases on a block. -/
theorem H22_cases_excl {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {B : Finset (Finset (ZMod n))} (hB : B ∈ blocks n) :
    ((∃ O ∈ B, IsCaseA O) → ¬ ∃ O ∈ B, IsCaseB O) ∧
      ((∀ O ∈ B, ¬ IsCaseA O ∧ ¬ IsCaseB O) ↔ (¬ ∃ O ∈ B, IsCaseA O) ∧ ¬ ∃ O ∈ B, IsCaseB O) := by
  classical
  refine ⟨fun hA hB' => ?_, ⟨fun h => ⟨fun ⟨O, hO, hA⟩ => (h O hO).1 hA, fun ⟨O, hO, hB'⟩ => (h O hO).2 hB'⟩,
    fun ⟨hA, hB'⟩ O hO => ⟨fun h => hA ⟨O, hO, h⟩, fun h => hB' ⟨O, hO, h⟩⟩⟩⟩
  exact Finset.disjoint_left.mp (H19_AB_disj hn ha hodd h3) (mem_filter.mpr ⟨hB, hA⟩) (mem_filter.mpr ⟨hB, hB'⟩)

theorem H22_prod_mK {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n) :
    ∏ B ∈ blocks n, H22_mK B = fibreSize n := by
  unfold fibreSize blocksA blocksB blocksC
  rw [prod_filter, prod_filter, prod_filter, ← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun B hB => ?_
  obtain ⟨hAB, hC⟩ := H22_cases_excl hn ha hodd h3 hB
  by_cases hA : ∃ O ∈ B, IsCaseA O
  · have hB' := hAB hA
    have hC' : ¬ ∀ O ∈ B, ¬IsCaseA O ∧ ¬IsCaseB O := fun h => (hC.mp h).1 hA
    rw [ite_eq_left hA, ite_eq_right hB', ite_eq_right hC', H22_mK, ite_eq_left hA]
    ring
  · by_cases hB' : ∃ O ∈ B, IsCaseB O
    · have hC' : ¬ ∀ O ∈ B, ¬IsCaseA O ∧ ¬IsCaseB O := fun h => (hC.mp h).2 hB'
      rw [ite_eq_right hA, ite_eq_left hB', ite_eq_right hC', H22_mK, ite_eq_right hA, ite_eq_left hB']
      ring
    · have hC' : ∀ O ∈ B, ¬IsCaseA O ∧ ¬IsCaseB O := hC.mpr ⟨hA, hB'⟩
      rw [ite_eq_right hA, ite_eq_right hB', ite_eq_left hC', H22_mK, ite_eq_right hA, ite_eq_right hB']
      ring

theorem H22_prod_mD {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n) :
    ∏ B ∈ blocks n, H22_mD B = fibreProd n := by
  unfold fibreProd blocksA blocksB blocksC
  rw [prod_filter, prod_filter, prod_filter, ← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun B hB => ?_
  obtain ⟨hAB, hC⟩ := H22_cases_excl hn ha hodd h3 hB
  by_cases hA : ∃ O ∈ B, IsCaseA O
  · have hB' := hAB hA
    have hC' : ¬ ∀ O ∈ B, ¬IsCaseA O ∧ ¬IsCaseB O := fun h => (hC.mp h).1 hA
    rw [ite_eq_left hA, ite_eq_right hB', ite_eq_right hC', H22_mD, ite_eq_left hA]
    ring
  · by_cases hB' : ∃ O ∈ B, IsCaseB O
    · have hC' : ¬ ∀ O ∈ B, ¬IsCaseA O ∧ ¬IsCaseB O := fun h => (hC.mp h).2 hB'
      rw [ite_eq_right hA, ite_eq_left hB', ite_eq_right hC', H22_mD, ite_eq_right hA, ite_eq_left hB']
      ring
    · have hC' : ∀ O ∈ B, ¬IsCaseA O ∧ ¬IsCaseB O := hC.mpr ⟨hA, hB'⟩
      rw [ite_eq_right hA, ite_eq_right hB', ite_eq_left hC', H22_mD, ite_eq_right hA, ite_eq_right hB']
      ring

end Orders

/-! ## Part 5 — `ψ : 𝒟^0 → D0^inv`, `λ ↦ λ(k)λ(k+m)`, has kernel `K'`: `|𝒟^0| ≤ |K'| · |D0^inv|` -/

section Psi

variable {n : ℕ} [NeZero n]

/-- `ψ(λ)(k) := λ(k) λ(k+m)`. -/
def H22_psi {L : Type*} [Field L] (lam : ZMod n → L) : ZMod n → L := fun k => lam k * lam (k + half n)

theorem H22_T0_ne_all {L : Type*} [Field L] {lam : ZMod n → L} (hl : lam ∈ (topData0 n 3 : Set (ZMod n → L)))
    (k : ZMod n) : lam k ≠ 0 := by
  rcases Nat.even_or_odd k.val with hk | hk
  · rw [hl.2 k hk]; exact one_ne_zero
  · exact H22_T0_ne hl hk

theorem H22_psi_mem (hev : Even n) (h4 : 4 ∣ n) {L : Type*} [Field L] {lam : ZMod n → L}
    (hl : lam ∈ (topData0 n 3 : Set (ZMod n → L))) : H22_psi lam ∈ H22_D n L := by
  have h2 : 2 ∣ n := even_iff_two_dvd.mp hev
  have h3m : ((3 : ℕ) : ZMod n) * half n = half n := by
    rw [Nat.cast_ofNat, show (3 : ZMod n) * half n = half n + (half n + half n) by ring, H7_two_half hev, add_zero]
  refine ⟨⟨fun k hk => ⟨?_, ?_⟩, fun k hk => ?_⟩, fun k hk => ?_⟩
  · have hkm := H19_odd_add_half h2 h4 hk
    unfold H22_psi
    rw [show ((3 : ℕ) : ZMod n) * k + half n = ((3 : ℕ) : ZMod n) * (k + half n) by rw [mul_add, h3m],
      (hl.1 k hk).1, (hl.1 _ hkm).1, mul_pow]
  · have hkm := H19_odd_add_half h2 h4 hk
    unfold H22_psi
    rw [H7_neg_add_half hev k]
    calc lam k * lam (k + half n) * (lam (-k) * lam (-(k + half n)))
        = (lam k * lam (-k)) * (lam (k + half n) * lam (-(k + half n))) := by ring
      _ = 1 := by rw [(hl.1 k hk).2, (hl.1 _ hkm).2, one_mul]
  · unfold H22_psi
    rw [hl.2 k hk, hl.2 _ (H19_even_add_half h2 h4 hk), one_mul]
  · unfold H22_psi
    rw [add_assoc, H7_two_half hev, add_zero, mul_comm]

theorem H22_T0_card_le (hev : Even n) (h4 : 4 ∣ n) {L : Type*} [Field L] (hKfin : (H22_K n L).Finite)
    (hDfin : (H22_D n L).Finite) :
    Nat.card (topData0 n 3 : Set (ZMod n → L)) ≤ Nat.card (H22_K n L) * Nat.card (H22_D n L) := by
  classical
  have h2 : 2 ∣ n := even_iff_two_dvd.mp hev
  set T : Set (ZMod n → L) := (topData0 n 3 : Set (ZMod n → L)) with hT
  let sec : (ZMod n → L) → (ZMod n → L) := fun μ => if h : ∃ l ∈ T, H22_psi l = μ then Classical.choose h else 1
  have hsec : ∀ l ∈ T, sec (H22_psi l) ∈ T ∧ H22_psi (sec (H22_psi l)) = H22_psi l := by
    intro l hl
    have h : ∃ l' ∈ T, H22_psi l' = H22_psi l := ⟨l, hl, rfl⟩
    simp only [sec, dite_eq_left h]
    exact Classical.choose_spec h
  let F : (ZMod n → L) → (ZMod n → L) × (ZMod n → L) := fun l => (l * (sec (H22_psi l))⁻¹, H22_psi l)
  have hmaps : Set.MapsTo F T (H22_K n L ×ˢ H22_D n L) := by
    intro l hl
    obtain ⟨hs, hps⟩ := hsec l hl
    refine ⟨⟨H11_T0_mul hl (H11_T0_inv hs), fun k hk => ?_⟩, H22_psi_mem hev h4 hl⟩
    have hkm := H19_odd_add_half h2 h4 hk
    have e : sec (H22_psi l) k * sec (H22_psi l) (k + half n) = l k * l (k + half n) := congrFun hps k
    apply eq_inv_of_mul_eq_one_right
    simp only [F, Pi.mul_apply, Pi.inv_apply]
    calc l k * (sec (H22_psi l) k)⁻¹ * (l (k + half n) * (sec (H22_psi l) (k + half n))⁻¹)
        = (l k * l (k + half n)) * (sec (H22_psi l) k * sec (H22_psi l) (k + half n))⁻¹ := by
          rw [mul_inv]; ring
      _ = 1 := by rw [e]; exact mul_inv_cancel₀ (mul_ne_zero (H22_T0_ne hl hk) (H22_T0_ne hl hkm))
  have hinj : Set.InjOn F T := by
    intro l1 h1 l2 h2' heq
    have e2 : H22_psi l1 = H22_psi l2 := congrArg Prod.snd heq
    have e1 : l1 * (sec (H22_psi l1))⁻¹ = l2 * (sec (H22_psi l2))⁻¹ := congrArg Prod.fst heq
    rw [e2] at e1
    have hs := (hsec l2 h2').1
    funext k
    have := congrFun e1 k
    simp only [Pi.mul_apply, Pi.inv_apply] at this
    exact mul_right_cancel₀ (inv_ne_zero (H22_T0_ne_all hs k)) this
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq, ← Set.ncard_prod]
  exact Set.ncard_le_ncard_of_injOn F hmaps hinj (hKfin.prod hDfin)

end Psi

/-! ## Part 6 — `pairProd = Φ · fibreProd`: a block of case A or B is one pair, a block of case C is two pairs -/

section PairsBlocks

variable {n : ℕ} [NeZero n]

/-- The block of a pair `P = {O, O⁻¹}`: `P ∪ (-P)`. -/
def H22_blk (P : Finset (Finset (ZMod n))) : Finset (Finset (ZMod n)) := P ∪ P.image negO

theorem H22_blk_pair (O : Finset (ZMod n)) : H22_blk {O, inv O} = blockOf O := by
  ext X
  simp only [H22_blk, blockOf, mem_union, mem_insert, mem_singleton, mem_image]
  constructor
  · rintro ((rfl | rfl) | ⟨Y, (rfl | rfl), rfl⟩) <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr ⟨O, Or.inl rfl, rfl⟩
    · exact Or.inr ⟨inv O, Or.inr rfl, rfl⟩

theorem H22_pairLen {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {k : ZMod n} (hk : Odd k.val) : pairLen ({orbit 3 k, inv (orbit 3 k)} : Finset (Finset (ZMod n))) = (orbit 3 k).card := by
  classical
  have hne := H19_top_mem hn ha hodd h3 hk
  have hdisj : Disjoint (orbit 3 k) (inv (orbit 3 k)) := by
    rw [H6_inv_orbit] at hne ⊢
    exact H22_orbits_disj h3 (Ne.symm hne)
  unfold pairLen
  have hu : ({orbit 3 k, inv (orbit 3 k)} : Finset (Finset (ZMod n))).biUnion id = orbit 3 k ∪ inv (orbit 3 k) := by
    simp
  rw [hu, card_union_of_disjoint hdisj, H6_card_inv]
  omega

/-- The pairs over a block `blockOf O` are the `{O', O'⁻¹}`, `O' ∈ blockOf O`. -/
theorem H22_mem_fiber {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) {ρ : ZMod n} (hρ : Odd ρ.val)
    (P : Finset (Finset (ZMod n))) :
    (P ∈ topPairs n 3 ∧ H22_blk P = blockOf (orbit 3 ρ)) ↔ ∃ O' ∈ blockOf (orbit 3 ρ), P = {O', inv O'} := by
  have h4 := H19_four_dvd hn ha
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hev : Even n := even_iff_two_dvd.mpr h2
  constructor
  · rintro ⟨hP, hblk⟩
    obtain ⟨O', -, rfl⟩ := mem_image.mp hP
    rw [H22_blk_pair] at hblk
    exact ⟨O', by rw [← hblk]; exact H22_self_mem_blockOf O', rfl⟩
  · rintro ⟨O', hO', rfl⟩
    obtain ⟨z, hz, rfl⟩ := H19_blockOf_mem hev h2 h4 hρ hO'
    exact ⟨mem_image.mpr ⟨_, H22_orbit_mem_topOrbits hz, rfl⟩, by
      rw [H22_blk_pair]; exact H19_blockOf_closed hev _ _ hO'⟩

theorem H22_fiber_prod {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {B : Finset (Finset (ZMod n))} (hB : B ∈ blocks n) :
    ∏ P ∈ (topPairs n 3).filter (fun P => H22_blk P = B), (3 ^ pairLen P - 1) = H22_mK B * H22_mD B := by
  classical
  have h4 := H19_four_dvd hn ha
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
  have hev : Even n := even_iff_two_dvd.mpr h2
  obtain ⟨hρ, hlen, hq, -, hA, hBc⟩ := H22_block_facts hn ha hodd h3 hB
  obtain ⟨-, hBeq⟩ := H22_rep_spec hB
  obtain ⟨hAB, hC⟩ := H22_cases_excl hn ha hodd h3 hB
  generalize H22_rep B = ρ at hρ hlen hq hA hBc hBeq
  subst hBeq
  have hmem : ∀ P, P ∈ (topPairs n 3).filter (fun P => H22_blk P = blockOf (orbit 3 ρ)) ↔
      ∃ O' ∈ blockOf (orbit 3 ρ), P = {O', inv O'} := fun P => by
    rw [mem_filter]; exact H22_mem_fiber hn ha hρ P
  have hpl := H22_pairLen hn ha hodd h3 hρ
  set O := orbit 3 ρ with hO
  by_cases hAB' : (∃ O' ∈ blockOf O, IsCaseA O') ∨ (∃ O' ∈ blockOf O, IsCaseB O')
  · -- cases A and B: one pair
    have hfib : (topPairs n 3).filter (fun P => H22_blk P = blockOf O) = {{O, inv O}} := by
      have hBO : blockOf O = {O, inv O} := by
        rcases hAB' with hA' | hB'
        · exact (H19_card_AB hn ha hodd h3 hB (H22_self_mem_blockOf O) (Or.inl ((H22_caseA_iff hev O).mp hA'))).1
        · exact (H19_card_AB hn ha hodd h3 hB (H22_self_mem_blockOf O) (Or.inr ((H22_caseB_iff hev O).mp hB'))).1
      ext P
      rw [hmem, mem_singleton, hBO]
      constructor
      · rintro ⟨O', hO', rfl⟩
        rcases mem_insert.mp hO' with rfl | h
        · rfl
        · rw [mem_singleton] at h; subst h; rw [H3_inv_inv, pair_comm]
      · rintro rfl; exact ⟨O, mem_insert_self _ _, rfl⟩
    rw [hfib, prod_singleton, hpl]
    have hc : ∃ c, O.card = 2 * c := by
      rcases hAB' with hA' | hB'
      · obtain ⟨-, hge⟩ := hA hA'
        have hev' := caseAB_even_proved n a nodd hn ha hodd h3 _ (H22_orbit_mem_topOrbits hρ)
          (Or.inl ((H22_caseA_iff hev O).mp hA'))
        rw [← hO] at hev'
        obtain ⟨c, hc⟩ := hev'; exact ⟨c, by omega⟩
      · have hev' := caseAB_even_proved n a nodd hn ha hodd h3 _ (H22_orbit_mem_topOrbits hρ)
          (Or.inr ((H22_caseB_iff hev O).mp hB'))
        rw [← hO] at hev'
        obtain ⟨c, hc⟩ := hev'; exact ⟨c, by omega⟩
    obtain ⟨c, hc⟩ := hc
    have hc2 : O.card / 2 = c := by omega
    have hsq : 3 ^ O.card - 1 = (3 ^ c - 1) * (3 ^ c + 1) := by
      rw [hc, two_mul, pow_add]; exact H11_sq_sub_one _ (Nat.one_le_pow _ _ (by norm_num))
    unfold H22_mK H22_mD
    rcases hAB' with hA' | hB'
    · rw [ite_eq_left hA', ite_eq_left hA', hq, hc2, hsq, mul_comm]
    · have hnA : ¬ ∃ O' ∈ blockOf O, IsCaseA O' := fun h => hAB h hB'
      rw [ite_eq_right hnA, ite_eq_left hB', ite_eq_right hnA, ite_eq_left hB', hq, hc2, hsq]
  · -- case C: two pairs
    rw [not_or] at hAB'
    have hnA : ¬ ∃ O' ∈ blockOf O, IsCaseA O' := hAB'.1
    have hnB : ¬ ∃ O' ∈ blockOf O, IsCaseB O' := hAB'.2
    have hnAO : ¬ IsCaseA O := fun h => hnA ⟨O, H22_self_mem_blockOf O, h⟩
    have hnBO : ¬ IsCaseB O := fun h => hnB ⟨O, H22_self_mem_blockOf O, h⟩
    have hmo : negO O = orbit 3 (ρ + half n) := H19_negO_orbit hev ρ
    have hρm : Odd (ρ + half n).val := H19_odd_add_half h2 h4 hρ
    have hne : ({O, inv O} : Finset (Finset (ZMod n))) ≠ {negO O, inv (negO O)} := by
      intro h
      have hOm : O ∈ ({negO O, inv (negO O)} : Finset (Finset (ZMod n))) := by rw [← h]; exact mem_insert_self _ _
      rcases mem_insert.mp hOm with h1 | h1
      · exact hnAO h1.symm
      · rw [mem_singleton] at h1
        apply hnBO
        show negO O = inv O
        conv_rhs => rw [h1]
        rw [H3_inv_inv]
    have hfib : (topPairs n 3).filter (fun P => H22_blk P = blockOf O) = {{O, inv O}, {negO O, inv (negO O)}} := by
      ext P
      rw [hmem, mem_insert, mem_singleton]
      constructor
      · rintro ⟨O', hO', rfl⟩
        unfold blockOf at hO'
        simp only [mem_insert, mem_singleton] at hO'
        rcases hO' with rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inl (by rw [H3_inv_inv, pair_comm])
        · exact Or.inr rfl
        · exact Or.inr (by rw [H19_negO_inv hev, H3_inv_inv, pair_comm])
      · rintro (rfl | rfl)
        · exact ⟨O, H22_self_mem_blockOf O, rfl⟩
        · exact ⟨negO O, by unfold blockOf; simp, rfl⟩
    rw [hfib, prod_pair hne, hpl, hmo, H22_pairLen hn ha hodd h3 hρm, ← hmo, H22_card_negO]
    unfold H22_mK H22_mD
    rw [ite_eq_right hnA, ite_eq_right hnB, ite_eq_right hnA, ite_eq_right hnB, hlen]

theorem H22_pairProd {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n) :
    pairProd n 3 = fibreSize n * fibreProd n := by
  classical
  have hmaps : ∀ P ∈ topPairs n 3, H22_blk P ∈ blocks n := by
    intro P hP
    obtain ⟨O, hO, rfl⟩ := mem_image.mp hP
    rw [H22_blk_pair]
    exact mem_image_of_mem _ hO
  unfold pairProd
  rw [← prod_fiberwise_of_maps_to hmaps, prod_congr rfl (fun B hB => H22_fiber_prod hn ha hodd h3 hB),
    prod_mul_distrib, H22_prod_mK hn ha hodd h3, H22_prod_mD hn ha hodd h3]

end PairsBlocks

/-! ## Part 7 — assembly: `|K'| = Φ` (algebraically closed `L`), every fibre has `Φ` elements, the counts -/

section Assembly

variable {n : ℕ} [NeZero n]

theorem H22_one_mem_K (L : Type*) [Field L] : (1 : ZMod n → L) ∈ H22_K n L :=
  ⟨H11_T0_one, fun _ _ => by simp⟩

theorem H22_one_mem_D (L : Type*) [Field L] : (1 : ZMod n → L) ∈ H22_D n L :=
  ⟨H11_T0_one, fun _ _ => by simp⟩

/-- Steps (c)-(e) of the roadmap: `|K'| = Φ` over an algebraically closed field of characteristic 3. -/
theorem H22_K_card {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type*} [Field L] [CharP L 3] [IsAlgClosed L] (ω : L) (hω : IsPrimitiveRoot ω n) :
    Nat.card (H22_K n L) = fibreSize n := by
  have h4 := H19_four_dvd hn ha
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h4)
  obtain ⟨hKfin, hKle⟩ := H22_K_le hn ha hodd h3 L
  obtain ⟨hDfin, hDle⟩ := H22_D_le hn ha hodd h3 L
  rw [H22_prod_mK hn ha hodd h3] at hKle
  rw [H22_prod_mD hn ha hodd h3] at hDle
  have hle := H22_T0_card_le hev h4 hKfin hDfin
  rw [(thm_4_1_step2_proved n a nodd hn ha hodd h3 ω hω).2.1, H22_pairProd hn ha hodd h3] at hle
  have hKpos : 0 < Nat.card (H22_K n L) := by
    rw [Nat.card_coe_set_eq]; exact (Set.ncard_pos hKfin).mpr ⟨1, H22_one_mem_K L⟩
  have hDpos : 0 < Nat.card (H22_D n L) := by
    rw [Nat.card_coe_set_eq]; exact (Set.ncard_pos hDfin).mpr ⟨1, H22_one_mem_D L⟩
  have hS : 0 < fibreSize n := lt_of_lt_of_le hKpos hKle
  have hP : 0 < fibreProd n := lt_of_lt_of_le hDpos hDle
  have h1 : fibreSize n * fibreProd n ≤ fibreSize n * Nat.card (H22_D n L) :=
    le_trans hle (Nat.mul_le_mul_right _ hKle)
  have hdP : Nat.card (H22_D n L) = fibreProd n := le_antisymm hDle (Nat.le_of_mul_le_mul_left h1 hS)
  rw [hdP] at hle
  exact le_antisymm hKle (Nat.le_of_mul_le_mul_right hle hP)

/-- Theorem 5.1(c), first part, for EVERY field `L ⊇ F` with a primitive `n`-th root `ω`: a non-empty fibre has `Φ`
elements (unconditional: no open row is used). -/
theorem H22_fibre_card {a nodd : ℕ} (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd) (h3 : ¬ 3 ∣ n)
    {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (y : ZMod n → GaloisField 3 (n / 2)) (hy : y ∈ NFSet n 2) : Nat.card (fibre ω y) = fibreSize n := by
  have h4 := H19_four_dvd hn ha
  have hev : Even n := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h4)
  have hω' : IsPrimitiveRoot (algebraMap L (AlgebraicClosure L) ω) n :=
    hω.map_of_injective (algebraMap L (AlgebraicClosure L)).injective
  rw [← H22_fibre_map (L' := AlgebraicClosure L) ω y,
    Nat.card_congr (Set.BijOn.equiv _ (H22_fibre_bij hev h4 h3 _ hω' y hy))]
  have := H19_charP n (L := AlgebraicClosure L)
  exact H22_K_card hn ha hodd h3 _ hω'

/-- Counting a finite set by the fibres of a map, all of the same size. -/
theorem H22_card_fiberwise {α β : Type*} (s : Set α) (hs : s.Finite) (f : α → β) (c : ℕ)
    (hc : ∀ x ∈ s, Nat.card {x' | x' ∈ s ∧ f x' = f x} = c) : Nat.card s = Nat.card (f '' s) * c := by
  classical
  set S := hs.toFinset with hSdef
  have hS : s = ↑S := hs.coe_toFinset.symm
  rw [hS] at hc ⊢
  rw [← coe_image, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_coe_finset, Set.ncard_coe_finset,
    card_eq_sum_card_image f S]
  rw [sum_congr rfl (g := fun _ => c), sum_const, smul_eq_mul]
  intro b hb
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hb
  have := hc x (mem_coe.mpr hx)
  rw [← this, Nat.card_coe_set_eq, ← Set.ncard_coe_finset, coe_filter]
  rfl

theorem H22_fibre_eq {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L)
    (y : ZMod n → GaloisField 3 (n / 2)) :
    {x' | x' ∈ NFSet n 2 ∧ lowerData ω x' = lowerData ω y} = fibre ω y := by
  ext x'
  show (x' ∈ NFSet n 2 ∧ lowerData ω x' = lowerData ω y) ↔
    (x' ∈ NFSet n 2 ∧ ∀ k : ZMod n, Even k.val → dftA ω x' k = dftA ω y k)
  rw [funext_iff, Subtype.forall]
  exact Iff.rfl

/-- Row 18c (counting part) — Theorem 5.1(c) (s5_twonorms.tex:61-67) with the identification of fibres (:74-77,
P10s_main.tex:183-184). Statement VERBATIM from Xia/Paper/Statements.lean; extra hypothesis `hcount` = the row
`thm_4_1_count n a nodd hn ha hodd h3` (exact instance). The first conjunct does not use `hcount`
(see `H22_fibre_card`). -/
theorem thm_5_1_c_count_of (n a nodd : ℕ) [NeZero n] (hn : n = 2 ^ a * nodd) (ha : 3 ≤ a) (hodd : Odd nodd)
    (h3 : ¬ 3 ∣ n) {L : Type*} [Field L] [Algebra (GaloisField 3 (n / 2)) L] (ω : L) (hω : IsPrimitiveRoot ω n)
    (hcount : Nat.card (NFSet n 2) = 4 * pairProd n 3 ∧ (NFSet n 2).Nonempty ∧
      (Nat.card (NFSet n 2) : ℚ) = 4 * 3 ^ (n / 4) * ∏ P ∈ topPairs n 3, (1 - (3 : ℚ) ^ (-(pairLen P : ℤ)))) :
    (∀ y ∈ NFSet n 2, Nat.card (fibre ω y) = fibreSize n) ∧
      Nat.card (lowerData ω '' NFSet n 2) = 4 * fibreProd n ∧
      Nat.card (NFSet n 2) = fibreSize n * (4 * fibreProd n) := by
  have hpart1 : ∀ y ∈ NFSet n 2, Nat.card (fibre ω y) = fibreSize n :=
    fun y hy => H22_fibre_card hn ha hodd h3 ω hω y hy
  have hNF : Nat.card (NFSet n 2) = fibreSize n * (4 * fibreProd n) := by
    rw [hcount.1, H22_pairProd hn ha hodd h3]; ring
  refine ⟨hpart1, ?_, hNF⟩
  have hcw := H22_card_fiberwise (NFSet n 2) (Set.toFinite _) (lowerData ω) (fibreSize n)
    (fun y hy => by rw [H22_fibre_eq]; exact hpart1 y hy)
  have hSpos : 0 < fibreSize n := by
    rw [← H22_prod_mK hn ha hodd h3]
    exact prod_pos (fun B hB => H22_mK_pos hn ha hodd h3 hB)
  rw [hNF, mul_comm (Nat.card _) _] at hcw
  exact (Nat.eq_of_mul_eq_mul_left hSpos hcw).symm

end Assembly

end Xia.Proofs

#print axioms Xia.Proofs.thm_5_1_c_count_of
#print axioms Xia.Proofs.H22_fibre_card
#print axioms Xia.Proofs.H22_K_card
#print axioms Xia.Proofs.H22_pairProd
