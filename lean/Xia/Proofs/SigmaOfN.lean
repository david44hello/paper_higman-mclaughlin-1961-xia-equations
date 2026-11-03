/- Xia/Proofs/SigmaOfN.lean — proofs of the rows sigma_of_n of Xia/Paper/Statements.lean.
Copyright (C) Dave Goel 2026--now. All rights reserved. -/
import Xia.Defs.Symmetry
import Xia.Proofs.NumberTheory

namespace Xia.Proofs

open Xia Finset

/-- An exponent `c` with `g^c = 3` in `ZMod p` is nonzero (`g^0 = 1 ≠ 3`, as `p > 2`). -/
lemma H36_exp_ne_zero (n : ℕ) (hn8 : 8 ≤ n) (g : (ZMod (pp n))ˣ) (c : ℕ)
    (hc : (g : ZMod (pp n)) ^ c = 3) : c ≠ 0 := by
  rintro rfl
  rw [pow_zero] at hc
  have h2 : ((2 : ℕ) : ZMod (pp n)) = 0 := by
    push_cast
    linear_combination -hc
  rw [ZMod.natCast_eq_zero_iff] at h2
  have hle := Nat.le_of_dvd (by norm_num) h2
  have hppn := H1_pp_ge n
  omega

/-- `3` is a power of the generator `g`: some `c` has `g^c = 3` in `ZMod p` (`3 ≠ 0` as `p > 3`). -/
lemma H36_exists_exp (n : ℕ) (hp : (pp n).Prime) (hn8 : 8 ≤ n) (g : (ZMod (pp n))ˣ)
    (hg : ∀ x : (ZMod (pp n))ˣ, x ∈ Subgroup.zpowers g) :
    ∃ c : ℕ, (g : ZMod (pp n)) ^ c = 3 := by
  have hF : Fact (pp n).Prime := ⟨hp⟩
  have hppn := H1_pp_ge n
  have h30 : (3 : ZMod (pp n)) ≠ 0 := by
    have : ((3 : ℕ) : ZMod (pp n)) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    simpa using this
  obtain ⟨c, hc⟩ := (Submonoid.mem_powers_iff _ _).1
    (mem_powers_iff_mem_zpowers.2 (hg (Units.mk0 3 h30)))
  refine ⟨c, ?_⟩
  rw [← Units.val_pow_eq_pow_val, hc]
  rfl

/-- The proof's formula: `σ = gcd(c, n)` for every nonzero `c` with `g^c = 3`, by comparing the orders
of `ϖ^σ` (order `n/σ`) and `χ(3) = χ(g)^c` (order `n / gcd(n, c)`). -/
lemma H36_sigma_eq_gcd (n : ℕ) (hn0 : n ≠ 0) {M : Type*} [Field M] (χ : MulChar (ZMod (pp n)) M)
    (g : (ZMod (pp n))ˣ) (hχg : IsPrimitiveRoot (χ (g : ZMod (pp n))) n) (ϖ : M)
    (hϖ : IsPrimitiveRoot ϖ n) (σ : ℕ) (hσ : σ ∣ n) (hσ0 : 0 < σ) (h3 : χ 3 = ϖ ^ σ) (c : ℕ)
    (hc0 : c ≠ 0) (hc : (g : ZMod (pp n)) ^ c = 3) : σ = Nat.gcd c n := by
  have hχ3 : χ 3 = (χ (g : ZMod (pp n))) ^ c := by rw [← hc, map_pow]
  have hord1 : orderOf (ϖ ^ σ) = n / σ := (hϖ.pow_of_dvd hσ0.ne' hσ).eq_orderOf.symm
  have hord2 : orderOf ((χ (g : ZMod (pp n))) ^ c) = n / Nat.gcd n c := by
    rw [orderOf_pow' _ hc0, ← hχg.eq_orderOf]
  rw [← h3, hχ3, hord2] at hord1
  rw [Nat.gcd_comm]
  exact (Nat.div_eq_iff_eq_of_dvd_dvd hn0 hσ (Nat.gcd_dvd_left n c)).1 hord1.symm

/-- `ord(3^{(p-1)/n}) = n / gcd(n, c)` in `F_p` when `g^c = 3`, `c ≠ 0`: `3^{(p-1)/n} = (g^{(p-1)/n})^c`
and `g^{(p-1)/n}` has order `n` (`g` has order `p - 1 = n(n+1)`). -/
lemma H36_order_three_pow (n : ℕ) (hp : (pp n).Prime) (hn8 : 8 ≤ n) (g : (ZMod (pp n))ˣ)
    (hg : ∀ x : (ZMod (pp n))ˣ, x ∈ Subgroup.zpowers g) (c : ℕ) (hc0 : c ≠ 0)
    (hc : (g : ZMod (pp n)) ^ c = 3) :
    orderOf ((3 : ZMod (pp n)) ^ ((pp n - 1) / n)) = n / Nat.gcd n c := by
  have hF : Fact (pp n).Prime := ⟨hp⟩
  have hppn := H1_pp_ge n
  have hord : orderOf g = pp n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have hpp1 : pp n - 1 = n * (n + 1) := by unfold pp; rw [Nat.add_sub_cancel]; ring
  have hdvd : n ∣ orderOf g := by rw [hord, hpp1]; exact Dvd.intro _ rfl
  have hord0 : orderOf g ≠ 0 := by rw [hord]; omega
  have hordh : orderOf (g ^ ((pp n - 1) / n)) = n := by
    rw [← hord]; exact orderOf_pow_orderOf_div hord0 hdvd
  have heq : (3 : ZMod (pp n)) ^ ((pp n - 1) / n)
      = (((g ^ ((pp n - 1) / n)) ^ c : (ZMod (pp n))ˣ) : ZMod (pp n)) := by
    rw [← hc, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← pow_mul, ← pow_mul, mul_comm]
  rw [heq, orderOf_units, orderOf_pow' _ hc0, hordh]

/-- Row sigma_of_n (draft v2.60) — s2_xia.tex:17, proof of Lemma 2.2 (s2_xia.tex:35-38). -/
theorem sigma_of_n_proved (n : ℕ) (h8 : 8 ∣ n) (hp : (pp n).Prime) {M : Type*} [Field M] (χ : MulChar (ZMod (pp n)) M)
    (g : (ZMod (pp n))ˣ) (hg : ∀ x : (ZMod (pp n))ˣ, x ∈ Subgroup.zpowers g)
    (hχg : IsPrimitiveRoot (χ (g : ZMod (pp n))) n) (ϖ : M) (hϖ : IsPrimitiveRoot ϖ n) (σ : ℕ) (hσ : σ ∣ n)
    (hσ0 : 0 < σ) (h3 : χ 3 = ϖ ^ σ) :
    σ = n / orderOf ((3 : ZMod (pp n)) ^ ((pp n - 1) / n)) ∧ ∀ c : ℕ, (g : ZMod (pp n)) ^ c = 3 → σ = Nat.gcd c n := by
  have hn8 : 8 ≤ n := H1_n_ge n h8 hp
  have hn0 : n ≠ 0 := by omega
  have hall : ∀ c : ℕ, (g : ZMod (pp n)) ^ c = 3 → σ = Nat.gcd c n := fun c hc =>
    H36_sigma_eq_gcd n hn0 χ g hχg ϖ hϖ σ hσ hσ0 h3 c (H36_exp_ne_zero n hn8 g c hc) hc
  refine ⟨?_, hall⟩
  obtain ⟨c, hc⟩ := H36_exists_exp n hp hn8 g hg
  rw [H36_order_three_pow n hp hn8 g hg c (H36_exp_ne_zero n hn8 g c hc) hc,
    Nat.div_div_self (Nat.gcd_dvd_left n c) hn0, Nat.gcd_comm]
  exact hall c hc

#print axioms sigma_of_n_proved

end Xia.Proofs
