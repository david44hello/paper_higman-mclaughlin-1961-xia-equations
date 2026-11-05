/- Xia/Proofs/Lemma41.lean — proofs of the rows L10_hX41 of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import Xia.Defs.DiffSet

namespace Xia.Proofs

open Xia Finset

/-! ## (T1) `n = 2^e`, `e` odd ⇒ `n ≡ 2 (mod 3)` -/

theorem H30_n_mod3 (n e : ℕ) (hne : n = 2 ^ e) (heo : Odd e) : n % 3 = 2 := by
  obtain ⟨j, rfl⟩ := heo
  subst hne
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

/-! ## (T2) Counting part: general finite field `K`, a finset `F` with `|F| = n + 1`, `|K| = n^2 + n + 1`,
and every non-zero `d` equal to `z - y` for exactly one pair in `F × F` (stated as: `#{z ∈ F : z - d ∈ F} = 1`). -/

/-- The `ℕ`-valued indicator of a finset. -/
def H30_ind {K : Type*} [DecidableEq K] (F : Finset K) (z : K) : ℕ := if z ∈ F then 1 else 0

/-- Parity of a symmetric double sum: `∑∑ f ≡ ∑ diag (mod 2)` (the involution `(x,y) ↦ (y,x)`). -/
theorem H30_double_sum_symm {α : Type*} [DecidableEq α] (s : Finset α) (f : α → α → ℕ)
    (hf : ∀ x y, f x y = f y x) :
    ∃ m : ℕ, ∑ x ∈ s, ∑ y ∈ s, f x y = ∑ x ∈ s, f x x + 2 * m := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨m + ∑ y ∈ s, f a y, ?_⟩
    simp only [Finset.sum_insert ha, Finset.sum_add_distrib]
    rw [hm, Finset.sum_congr rfl (fun x _ => hf x a)]
    ring

/-- Sharp rigidity (step 4): `a ≥ 1`, `∑ a = (n+1)^2`, `∑ a^2 = (n+1)(2n+1)` over `n^2+n+1` points ⇒ some
`a g = n + 1`. (With `s = a - 1`: `∑ s = n`, `∑ s^2 = n^2`, `0 ≤ s ≤ n`, so each `s ∈ {0, n}`.) -/
theorem H30_rigid {ι : Type*} [Fintype ι] (a : ι → ℕ) (n : ℕ) (hn0 : n ≠ 0)
    (hcard : Fintype.card ι = n ^ 2 + n + 1) (hpos : ∀ t, 1 ≤ a t)
    (hA : ∑ t, a t = (n + 1) * (n + 1)) (hB : ∑ t, a t ^ 2 = (n + 1) * (2 * n + 1)) :
    ∃ g, a g = n + 1 := by
  obtain ⟨s, hs⟩ : ∃ s : ι → ℕ, ∀ t, a t = s t + 1 :=
    ⟨fun t => a t - 1, fun t => by have := hpos t; show a t = a t - 1 + 1; omega⟩
  have has : a = fun t => s t + 1 := funext hs
  subst has
  have e1 : ∀ t, (s t + 1) ^ 2 = s t * s t + 2 * s t + 1 := fun t => by ring
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard, smul_eq_mul,
    mul_one] at hA
  simp only [e1, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, hcard,
    smul_eq_mul, mul_one] at hB
  have hS1 : ∑ t, s t = n := by nlinarith
  have hS2 : ∑ t, s t * s t = n * n := by nlinarith
  have hle : ∀ t, s t ≤ n := fun t => by
    have := Finset.single_le_sum (f := s) (fun i _ => Nat.zero_le (s i)) (Finset.mem_univ t)
    rwa [hS1] at this
  have hsq_le : ∀ t ∈ (Finset.univ : Finset ι), s t * s t ≤ n * s t :=
    fun t _ => Nat.mul_le_mul_right _ (hle t)
  have heq : ∑ t, s t * s t = ∑ t, n * s t := by rw [hS2, ← Finset.mul_sum, hS1]
  have hall := (Finset.sum_eq_sum_iff_of_le hsq_le).1 heq
  obtain ⟨g, -, hg⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := s)
    (by rw [hS1]; exact hn0)
  refine ⟨g, ?_⟩
  have hgn : s g = n := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hg) (hall g (Finset.mem_univ g))
  show s g + 1 = n + 1
  omega

section H30general

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

theorem H30_sum_ind_sub (F : Finset K) (c : K) : ∑ t : K, H30_ind F (c - t) = F.card := by
  rw [Fintype.sum_equiv (Equiv.subLeft c) (fun t => H30_ind F (c - t)) (H30_ind F)
    (fun t => by simp only [Equiv.subLeft_apply])]
  simp only [H30_ind]
  rw [Fintype.sum_ite_mem F (fun _ => (1 : ℕ)), Finset.sum_const, smul_eq_mul, mul_one]

theorem H30_sum_ind_mul (F : Finset K) (c c' : K) :
    ∑ t : K, H30_ind F (c - t) * H30_ind F (c' - t) = ∑ z ∈ F, H30_ind F (z - (c - c')) := by
  rw [Fintype.sum_equiv (Equiv.subLeft c) _ (fun z => H30_ind F z * H30_ind F (z - (c - c')))
    (fun t => by simp only [Equiv.subLeft_apply, show c - t - (c - c') = c' - t by ring])]
  rw [← Fintype.sum_ite_mem F]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  by_cases hz : z ∈ F <;> simp [H30_ind, hz]

omit [Fintype K] in
theorem H30_sum_ind_shift (F : Finset K) (n : ℕ) (hk : F.card = n + 1)
    (hN : ∀ d : K, d ≠ 0 → (F.filter (fun z => z - d ∈ F)).card = 1) (d : K) :
    ∑ z ∈ F, H30_ind F (z - d) = 1 + if d = 0 then n else 0 := by
  have e : ∑ z ∈ F, H30_ind F (z - d) = (F.filter (fun z => z - d ∈ F)).card := by
    rw [Finset.card_filter]; rfl
  rw [e]
  by_cases hd : d = 0
  · subst hd
    rw [Finset.filter_true_of_mem (fun z hz => by simpa using hz), hk, ite_eq_left rfl]
    omega
  · rw [hN d hd, ite_eq_right hd]

/-- Steps (1)-(5): the counting yields `g` with `2x - g ∈ F` for every `x ∈ F`. -/
theorem H30_exists_shift (F : Finset K) (n : ℕ) (hn : Even n) (hn0 : n ≠ 0) (hk : F.card = n + 1)
    (hcard : Fintype.card K = n ^ 2 + n + 1) (h2 : (2 : K) ≠ 0)
    (hN : ∀ d : K, d ≠ 0 → (F.filter (fun z => z - d ∈ F)).card = 1) :
    ∃ g : K, ∀ x ∈ F, 2 * x - g ∈ F := by
  have hS := H30_sum_ind_shift F n hk hN
  -- (1) `a t := ∑_{x ∈ F} [2x - t ∈ F]`; `∑_t a t = k^2`.
  have hA : ∑ t : K, ∑ x ∈ F, H30_ind F (2 * x - t) = (n + 1) * (n + 1) := by
    rw [Finset.sum_comm]
    simp only [H30_sum_ind_sub, Finset.sum_const, smul_eq_mul, hk]
  -- (3) `∑_t a t ^ 2 = k (2k - 1)`.
  have e2 : ∀ x y : K, 2 * x - 2 * y = 0 → x = y := by
    intro x y h
    rw [← mul_sub, mul_eq_zero] at h
    rcases h with h | h
    · exact absurd h h2
    · exact sub_eq_zero.1 h
  have inner : ∀ x ∈ F, ∑ y ∈ F, (1 + if 2 * x - 2 * y = 0 then n else 0) = 2 * n + 1 := by
    intro x hx
    have hc : ∀ y ∈ F, (1 + if 2 * x - 2 * y = 0 then n else 0) = 1 + if x = y then n else 0 := by
      intro y _
      by_cases hxy : x = y
      · subst hxy; simp
      · rw [ite_eq_right hxy, ite_eq_right (fun h => hxy (e2 x y h))]
    rw [Finset.sum_congr rfl hc, Finset.sum_add_distrib, Finset.sum_ite_eq, ite_eq_left hx]
    simp only [Finset.sum_const, smul_eq_mul, mul_one, hk]
    omega
  have hB : ∑ t : K, (∑ x ∈ F, H30_ind F (2 * x - t)) ^ 2 = (n + 1) * (2 * n + 1) := by
    calc ∑ t : K, (∑ x ∈ F, H30_ind F (2 * x - t)) ^ 2
        = ∑ t : K, ∑ x ∈ F, ∑ y ∈ F, H30_ind F (2 * x - t) * H30_ind F (2 * y - t) := by
          simp only [sq, Finset.sum_mul_sum]
      _ = ∑ x ∈ F, ∑ y ∈ F, ∑ t : K, H30_ind F (2 * x - t) * H30_ind F (2 * y - t) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
      _ = ∑ x ∈ F, ∑ y ∈ F, (1 + if 2 * x - 2 * y = 0 then n else 0) := by
          simp only [H30_sum_ind_mul, hS]
      _ = ∑ x ∈ F, (2 * n + 1) := Finset.sum_congr rfl inner
      _ = (n + 1) * (2 * n + 1) := by rw [Finset.sum_const, smul_eq_mul, hk]
  -- (2) every `a t` is odd, hence `≥ 1`.
  have hpos : ∀ t : K, 1 ≤ ∑ x ∈ F, H30_ind F (2 * x - t) := by
    intro t
    obtain ⟨m, hm⟩ := H30_double_sum_symm F (fun x y => H30_ind F (x + y - t))
      (fun x y => by simp only [add_comm x y])
    have hm' : ∑ x ∈ F, ∑ y ∈ F, H30_ind F (x + y - t) = ∑ x ∈ F, H30_ind F (x + x - t) + 2 * m := hm
    have e3 : ∀ x ∈ F, ∑ y ∈ F, H30_ind F (x + y - t) = 1 + if t = x then n else 0 := by
      intro x _
      rw [Finset.sum_congr rfl (fun y _ => by rw [show x + y - t = y - (t - x) by ring]), hS]
      by_cases htx : t = x
      · rw [ite_eq_left (sub_eq_zero.2 htx), ite_eq_left htx]
      · rw [ite_eq_right (fun h => htx (sub_eq_zero.1 h)), ite_eq_right htx]
    have hT : ∑ x ∈ F, ∑ y ∈ F, H30_ind F (x + y - t) = (n + 1) + if t ∈ F then n else 0 := by
      rw [Finset.sum_congr rfl e3, Finset.sum_add_distrib, Finset.sum_ite_eq]
      simp only [Finset.sum_const, smul_eq_mul, mul_one, hk]
    have hdiag : ∑ x ∈ F, H30_ind F (x + x - t) = ∑ x ∈ F, H30_ind F (2 * x - t) := by
      simp only [two_mul]
    have hm2 : ∑ x ∈ F, H30_ind F (2 * x - t) + 2 * m = (n + 1) + if t ∈ F then n else 0 := by
      rw [← hdiag, ← hm', hT]
    obtain ⟨r, hr⟩ := hn
    split_ifs at hm2 <;> omega
  -- (4) rigidity gives `g` with `a g = k`.
  obtain ⟨g, hg⟩ := H30_rigid (fun t => ∑ x ∈ F, H30_ind F (2 * x - t)) n hn0 hcard hpos hA hB
  have hg' : ∑ x ∈ F, H30_ind F (2 * x - g) = n + 1 := hg
  -- (5) `a g = |F|` forces `2x - g ∈ F` for all `x ∈ F`.
  refine ⟨g, ?_⟩
  have hle1 : ∀ x ∈ F, H30_ind F (2 * x - g) ≤ 1 := fun x _ => by
    unfold H30_ind; split_ifs <;> omega
  have hsum1 : ∑ x ∈ F, H30_ind F (2 * x - g) = ∑ x ∈ F, 1 := by
    rw [hg', Finset.sum_const, smul_eq_mul, mul_one, hk]
  have hall := (Finset.sum_eq_sum_iff_of_le hle1).1 hsum1
  intro x hx
  have h1x := hall x hx
  by_contra hcon
  simp [H30_ind, hcon] at h1x

omit [Fintype K] in
/-- Step (6): `2x - g ∈ F` for all `x ∈ F`, `F` multiplicatively closed, `1 ∈ F`, `0 ∉ F`, `|F| ≥ 2` and
`λ = 1` ⇒ `g = 0`, hence `2 ∈ F`. -/
theorem H30_shift_zero (F : Finset K) (h2 : (2 : K) ≠ 0)
    (hN : ∀ d : K, d ≠ 0 → (F.filter (fun z => z - d ∈ F)).card = 1)
    (hmul : ∀ x ∈ F, ∀ y ∈ F, x * y ∈ F) (h1 : (1 : K) ∈ F) (h0 : (0 : K) ∉ F)
    (hbig : 1 < F.card) (g : K) (hg : ∀ x ∈ F, 2 * x - g ∈ F) : (2 : K) ∈ F := by
  obtain ⟨h, hh, hh1⟩ := Finset.exists_mem_ne hbig 1
  have hh0 : h ≠ 0 := fun e => h0 (e ▸ hh)
  have hg0 : g = 0 := by
    by_contra hgne
    have ht : h * g - g ≠ 0 := by
      rw [show h * g - g = (h - 1) * g by ring]
      exact mul_ne_zero (sub_ne_zero.2 hh1) hgne
    have hcard := hN _ ht
    have hlt : 1 < (F.filter (fun z => z - (h * g - g) ∈ F)).card := by
      rw [Finset.one_lt_card]
      refine ⟨2 * h - g, ?_, 2 * (h * h) - g, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨hg h hh, ?_⟩
        rw [show 2 * h - g - (h * g - g) = h * (2 * 1 - g) by ring]
        exact hmul h hh _ (hg 1 h1)
      · rw [Finset.mem_filter]
        refine ⟨hg _ (hmul h hh h hh), ?_⟩
        rw [show 2 * (h * h) - g - (h * g - g) = h * (2 * h - g) by ring]
        exact hmul h hh _ (hg h hh)
      · intro e
        have h3 : 2 * h * (1 - h) = 0 := by linear_combination e
        rcases mul_eq_zero.1 h3 with h' | h'
        · exact (mul_ne_zero h2 hh0) h'
        · exact hh1 (sub_eq_zero.1 h').symm
    rw [hcard] at hlt
    exact lt_irrefl _ hlt
  have h2F := hg 1 h1
  rwa [hg0, mul_one, sub_zero] at h2F

end H30general

/-! ## (T2) in our instance: `F = H_{v,n}` as a finset of `ZMod (pp n)`. -/

theorem H30_two_mem (n : ℕ) (hn2 : 2 ∣ n) (hn : 2 ≤ n) (hp : (pp n).Prime)
    (hD : IsDiffSet (pp n) (Hpow (pp n) n) (n + 1) 1) : (2 : ZMod (pp n)) ∈ Hpow (pp n) n := by
  classical
  have : Fact (pp n).Prime := ⟨hp⟩
  have : NeZero (pp n) := ⟨hp.ne_zero⟩
  let F : Finset (ZMod (pp n)) := Finset.univ.filter (fun a => a ∈ Hpow (pp n) n)
  have hF : ∀ a, a ∈ F ↔ a ∈ Hpow (pp n) n := fun a => by simp [F]
  have hFset : (↑F : Set (ZMod (pp n))) = Hpow (pp n) n := by
    ext a; simp [F]
  have hk : F.card = n + 1 := by
    have h1 := hD.1
    rw [← hFset, Set.ncard_coe_finset] at h1
    exact h1
  have hN : ∀ d : ZMod (pp n), d ≠ 0 → (F.filter (fun z => z - d ∈ F)).card = 1 := by
    intro d hd
    refine (Nat.card_eq_finsetCard _).symm.trans (Eq.trans (Nat.card_congr ?_) (hD.2 d hd))
    exact
      { toFun := fun z => ⟨(z.1, z.1 - d), by
          have hz := z.2
          simp only [Finset.mem_filter, hF] at hz
          exact ⟨hz.1, hz.2, by ring⟩⟩
        invFun := fun pr => ⟨pr.1.1, by
          obtain ⟨hx, hy, hxy⟩ := pr.2
          simp only [Finset.mem_filter, hF]
          refine ⟨hx, ?_⟩
          rw [show pr.1.1 - d = pr.1.2 by linear_combination hxy]
          exact hy⟩
        left_inv := fun z => rfl
        right_inv := fun pr => by
          obtain ⟨⟨x, y⟩, hx, hy, hxy⟩ := pr
          subst hxy
          apply Subtype.ext
          simp }
  have h2 : (2 : ZMod (pp n)) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod (pp n)) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have hle := Nat.le_of_dvd (by norm_num) h'
    simp only [pp] at hle
    nlinarith
  have hcard : Fintype.card (ZMod (pp n)) = n ^ 2 + n + 1 := by
    rw [ZMod.card]; rfl
  have hn0 : n ≠ 0 := by omega
  obtain ⟨g, hg⟩ := H30_exists_shift F n (even_iff_two_dvd.2 hn2) hn0 hk hcard h2 hN
  have hmul : ∀ x ∈ F, ∀ y ∈ F, x * y ∈ F := by
    intro x hx y hy
    rw [hF] at hx hy ⊢
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨c, hc, rfl⟩ := hy
    exact ⟨b * c, mul_ne_zero hb hc, by ring⟩
  have h1 : (1 : ZMod (pp n)) ∈ F := by
    rw [hF]; exact ⟨1, one_ne_zero, (one_pow n).symm⟩
  have h0 : (0 : ZMod (pp n)) ∉ F := by
    rw [hF]
    rintro ⟨b, hb, hb0⟩
    exact hb ((pow_eq_zero_iff hn0).1 hb0.symm)
  have hbig : 1 < F.card := by rw [hk]; omega
  exact (hF 2).1 (H30_shift_zero F h2 hN hmul h1 h0 hbig g hg)

/-! ## (T3) The hypothesis `hX41` of `prop_6_1_noX35` (Xia Lemma 4.1 in our instance). -/

theorem L10_hX41_proved (n e : ℕ) [NeZero n] (hne : n = 2 ^ e) (he : 3 ≤ e) (heo : Odd e) :
    (pp n).Prime → IsDiffSet (pp n) (Hpow (pp n) n) (n + 1) 1 →
      n % 3 = 2 ∧ (2 : ZMod (pp n)) ∈ Hpow (pp n) n := by
  intro hp hD
  have h8 : 8 ≤ n := by
    rw [hne]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hn2 : 2 ∣ n := by
    rw [hne]; exact dvd_pow_self 2 (by omega)
  exact ⟨H30_n_mod3 n e hne heo, H30_two_mem n hn2 (by omega) hp hD⟩

end Xia.Proofs

#print axioms Xia.Proofs.H30_n_mod3
#print axioms Xia.Proofs.H30_two_mem
#print axioms Xia.Proofs.L10_hX41_proved
