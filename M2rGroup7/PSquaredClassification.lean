import Mathlib
import M2rGroup7.CyclicGroup

/-!
# Classification of groups of order `p^2`

This file formalizes the classification of groups of order `p^2` for a prime
`p`: every such group is isomorphic either to the cyclic group of order `p^2`
or to the direct product of two cyclic groups of order `p`.
-/

namespace M2rGroup7.PSquaredClassification

open scoped IsMulCommutative

/-- A group of order `p^2` is commutative. -/
theorem isMulCommutative_of_card_eq_prime_sq {p : ℕ} [Fact p.Prime] {G : Type*}
    [Group G] (h : Nat.card G = p ^ 2) : IsMulCommutative G :=
  ⟨⟨IsPGroup.commutative_of_card_eq_prime_sq h⟩⟩

/-- For any `cyclicHom n a h`, applied at `x : CyclicGroup n`, we get
`a ^ (toAdd x).val`. -/
private lemma cyclicHom_apply_eq_zpow'
    (n : Nat) [NeZero n] {G : Type*} [Group G] (a : G) (h : a ^ n = 1)
    (x : CyclicGroup n) :
    cyclicHom n a h x = a ^ ((Multiplicative.toAdd x).val : ℤ) := by
  change Additive.toMul ((ZMod.lift n
      ⟨zmultiplesHom (Additive G) (Additive.ofMul a),
        by change (n : ℤ) • Additive.ofMul a = 0
           rw [← ofMul_zpow, zpow_natCast, h, ofMul_one]⟩) (Multiplicative.toAdd x))
      = a ^ ((Multiplicative.toAdd x).val : ℤ)
  set m : ℕ := (Multiplicative.toAdd x).val with hm
  conv_lhs => rw [show (Multiplicative.toAdd x : ZMod n) = (((m : ℤ) : ZMod n)) from by
    push_cast; exact (ZMod.natCast_zmod_val _).symm]
  rw [ZMod.lift_coe]
  rw [zmultiplesHom_apply, ← ofMul_zpow]
  rfl

/-- `Multiplicative.ofAdd 1` generates `CyclicGroup n` as zpowers. -/
private lemma ofAdd_one_zpowers_top' (n : Nat) [NeZero n] :
    (Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod n)) : Subgroup (CyclicGroup n)) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro x
  refine Subgroup.mem_zpowers_iff.mpr ⟨((Multiplicative.toAdd x).val : ℤ), ?_⟩
  change Multiplicative.ofAdd (1 : ZMod n) ^ ((Multiplicative.toAdd x).val : ℤ) = x
  rw [← Multiplicative.ofAdd.apply_symm_apply x]
  change Multiplicative.ofAdd (1 : ZMod n) ^ ((Multiplicative.toAdd x).val : ℤ)
      = Multiplicative.ofAdd (Multiplicative.toAdd x)
  rw [← ofAdd_zsmul, zsmul_one]
  congr 1
  push_cast
  exact ZMod.natCast_zmod_val _

/-- The range of `cyclicHom n a h` equals `Subgroup.zpowers a`. -/
private lemma cyclicHom_range' (n : Nat) [NeZero n] {G : Type*} [Group G] (a : G) (h : a ^ n = 1) :
    (cyclicHom n a h).range = Subgroup.zpowers a := by
  rw [MonoidHom.range_eq_map, ← ofAdd_one_zpowers_top' n, MonoidHom.map_zpowers]
  congr 1
  rw [cyclicHom_apply_eq_zpow']
  have hn_pos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  by_cases hn1 : n = 1
  · subst hn1
    change a ^ ((Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 1))).val : ℤ) = a
    have hval : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 1))).val = 0 := by
      simp [Subsingleton.elim (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 1))) 0]
    rw [hval]
    simpa using h.symm
  · change a ^ ((Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod n))).val : ℤ) = a
    have h2 : 2 ≤ n := by omega
    have hval : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod n))).val = 1 := by
      change (1 : ZMod n).val = 1
      rw [ZMod.val_one_eq_one_mod, Nat.one_mod_eq_one.mpr (by omega)]
    rw [hval]; simp

/-- A non-cyclic group of order `p^2` is isomorphic to `CyclicGroup p × CyclicGroup p`. -/
theorem mulEquiv_prod_of_card_eq_prime_sq_of_not_isCyclic {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G] (h : Nat.card G = p ^ 2) (hnc : ¬ IsCyclic G) :
    Nonempty (G ≃* CyclicGroup p × CyclicGroup p) := by
  have hp : p.Prime := Fact.out
  haveI hpne : NeZero p := ⟨hp.ne_zero⟩
  haveI hmc : IsMulCommutative G := isMulCommutative_of_card_eq_prime_sq h
  have hcomm : ∀ a b : G, Commute a b := fun a b => (hmc.is_comm.comm a b)
  haveI : Finite G := Nat.finite_of_card_ne_zero (h ▸ pow_ne_zero 2 hp.ne_zero)
  haveI : Nontrivial G := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    rw [h]; exact one_lt_pow₀ hp.one_lt two_ne_zero
  have hexp : Monoid.exponent G = p :=
    (not_isCyclic_iff_exponent_eq_prime hp h).mp hnc
  have hord : ∀ g : G, g ≠ 1 → orderOf g = p := fun g hg =>
    (Monoid.exponent_eq_prime_iff hp).mp hexp g hg
  have hpow : ∀ g : G, g ^ p = 1 := fun g => by
    have := Monoid.pow_exponent_eq_one g; rw [hexp] at this; exact this
  obtain ⟨x, hx1⟩ : ∃ x : G, x ≠ 1 := exists_ne 1
  have hxord : orderOf x = p := hord x hx1
  have hxp : x ^ p = 1 := hpow x
  have hcard_x : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, hxord]
  have hzp_ne_top : Subgroup.zpowers x ≠ ⊤ := by
    intro htop
    have h1 : Nat.card (Subgroup.zpowers x) = Nat.card G := by
      rw [htop]; exact Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [hcard_x, h] at h1
    have : p ^ 1 = p ^ 2 := by simpa using h1
    have := Nat.pow_right_injective hp.two_le this
    exact absurd this (by decide)
  obtain ⟨y, hy_not⟩ : ∃ y : G, y ∉ Subgroup.zpowers x :=
    SetLike.exists_not_mem_of_ne_top _ hzp_ne_top
  have hy1 : y ≠ 1 := fun h1 => hy_not (h1 ▸ Subgroup.one_mem _)
  have hyord : orderOf y = p := hord y hy1
  have hyp : y ^ p = 1 := hpow y
  have hcard_y : Nat.card (Subgroup.zpowers y) = p := by
    rw [Nat.card_zpowers, hyord]
  have hdisj : Disjoint (Subgroup.zpowers x) (Subgroup.zpowers y) := by
    rw [disjoint_iff]
    set I : Subgroup G := Subgroup.zpowers x ⊓ Subgroup.zpowers y with hI
    have hsub_le : I ≤ Subgroup.zpowers y := inf_le_right
    have hdvd : Nat.card I ∣ Nat.card (Subgroup.zpowers y) :=
      Subgroup.card_dvd_of_le hsub_le
    rw [hcard_y] at hdvd
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp_eq
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : I = Subgroup.zpowers y := by
        apply Subgroup.eq_of_le_of_card_ge hsub_le
        rw [hp_eq, hcard_y]
      have hy_in : y ∈ Subgroup.zpowers x := by
        have : y ∈ I := by rw [heq]; exact Subgroup.mem_zpowers _
        exact this.1
      exact hy_not hy_in
  let iota_x : CyclicGroup p →* G := cyclicHom p x hxp
  let iota_y : CyclicGroup p →* G := cyclicHom p y hyp
  have hrange_x : iota_x.range = Subgroup.zpowers x := cyclicHom_range' p x hxp
  have hrange_y : iota_y.range = Subgroup.zpowers y := cyclicHom_range' p y hyp
  have hcomm_iota : ∀ (a : CyclicGroup p) (b : CyclicGroup p),
      Commute (iota_x a) (iota_y b) := fun a b => hcomm _ _
  let Φ : CyclicGroup p × CyclicGroup p →* G := iota_x.noncommCoprod iota_y hcomm_iota
  have hΦ_range : Φ.range = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    change (iota_x.noncommCoprod iota_y hcomm_iota).range = _
    rw [MonoidHom.noncommCoprod_range, hrange_x, hrange_y]
  have hcompl : Subgroup.IsComplement' (Subgroup.zpowers x) (Subgroup.zpowers y) :=
    Subgroup.isComplement'_of_card_mul_and_disjoint
      (by rw [hcard_x, hcard_y, ← sq, ← h]) hdisj
  have hsup : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤ := hcompl.sup_eq_top
  have hΦ_surj : Function.Surjective Φ := by
    rw [← MonoidHom.range_eq_top]
    rw [hΦ_range, hsup]
  have hcard_prod : Nat.card (CyclicGroup p × CyclicGroup p) = p ^ 2 := by
    rw [Nat.card_prod, card_cyclicGroup, sq]
  have hcard_eq : Nat.card (CyclicGroup p × CyclicGroup p) = Nat.card G := by
    rw [hcard_prod, h]
  have hΦ_bij : Function.Bijective Φ :=
    (Nat.bijective_iff_surjective_and_card Φ).mpr ⟨hΦ_surj, hcard_eq⟩
  let e : CyclicGroup p × CyclicGroup p ≃* G := MulEquiv.ofBijective Φ hΦ_bij
  exact ⟨e.symm⟩

/-- A group of order `p^2` is isomorphic to `CyclicGroup (p^2)` or to
`CyclicGroup p × CyclicGroup p`. -/
theorem p_squared_classification {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    (h : Nat.card G = p ^ 2) :
    Nonempty (G ≃* CyclicGroup (p ^ 2)) ∨
      Nonempty (G ≃* CyclicGroup p × CyclicGroup p) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  by_cases hc : IsCyclic G
  · left
    haveI := hc
    exact ⟨mulEquivOfCyclicCardEq (h.trans (card_cyclicGroup (p ^ 2)).symm)⟩
  · right
    exact mulEquiv_prod_of_card_eq_prime_sq_of_not_isCyclic h hc

end M2rGroup7.PSquaredClassification
