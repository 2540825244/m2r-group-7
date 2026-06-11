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

/-- `cyclicHom n a h` sends `Multiplicative.ofAdd 1` to `a`. -/
private lemma cyclicHom_ofAdd_one -- (extracted by Fuse golfer)
    (n : Nat) [NeZero n] {G : Type*} [Group G]
    (a : G) (h : a ^ n = 1) :
    cyclicHom n a h (Multiplicative.ofAdd (1 : ZMod n)) = a := by
  change Additive.toMul (ZMod.lift n _ (1 : ZMod n)) = a
  rw [show (1 : ZMod n) = ((1 : ℤ) : ZMod n) by push_cast; rfl, ZMod.lift_coe,
    zmultiplesHom_apply, one_zsmul]
  rfl

/-- A non-cyclic group of order `p^2` is isomorphic to `CyclicGroup p × CyclicGroup p`. -/
theorem mulEquiv_prod_of_card_eq_prime_sq_of_not_isCyclic {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G] (h : Nat.card G = p ^ 2) (hnc : ¬ IsCyclic G) :
    Nonempty (G ≃* CyclicGroup p × CyclicGroup p) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : IsMulCommutative G := isMulCommutative_of_card_eq_prime_sq h
  haveI : Finite G := Nat.finite_of_card_ne_zero (h ▸ pow_ne_zero 2 hp.ne_zero)
  haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp
    (h ▸ one_lt_pow₀ hp.one_lt two_ne_zero)
  have hexp : Monoid.exponent G = p := (not_isCyclic_iff_exponent_eq_prime hp h).mp hnc
  have hpow : ∀ g : G, g ^ p = 1 := fun g => hexp ▸ Monoid.pow_exponent_eq_one g
  have hord : ∀ g : G, g ≠ 1 → orderOf g = p :=
    (Monoid.exponent_eq_prime_iff hp).mp hexp
  obtain ⟨x, hx1⟩ : ∃ x : G, x ≠ 1 := exists_ne 1
  have hcard_x : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, hord x hx1]
  have hzp_ne_top : Subgroup.zpowers x ≠ ⊤ := fun htop => by
    have hpp : orderOf x = p ^ 2 := h ▸ orderOf_eq_card_of_zpowers_eq_top htop
    rw [hord x hx1] at hpp
    have : p ^ 1 = p ^ 2 := by rw [pow_one]; exact hpp
    exact absurd (Nat.pow_right_injective hp.two_le this) (by decide)
  obtain ⟨y, hy_not⟩ := SetLike.exists_not_mem_of_ne_top _ hzp_ne_top
  have hy1 : y ≠ 1 := fun h1 => hy_not (h1 ▸ Subgroup.one_mem _)
  have hcard_y : Nat.card (Subgroup.zpowers y) = p := by
    rw [Nat.card_zpowers, hord y hy1]
  have hdisj : Disjoint (Subgroup.zpowers x) (Subgroup.zpowers y) := by
    rw [disjoint_iff]
    have hdvd : Nat.card (Subgroup.zpowers x ⊓ Subgroup.zpowers y : Subgroup G) ∣ p :=
      hcard_y ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp_eq
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · refine absurd ?_ hy_not
      have heq : Subgroup.zpowers x ⊓ Subgroup.zpowers y = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (hp_eq.trans hcard_y.symm).ge
      exact (heq ▸ Subgroup.mem_zpowers y).1
  -- Build Φ : CyclicGroup p × CyclicGroup p →* G using the universal property of cyclic groups.
  let iota_x : CyclicGroup p →* G := cyclicHom p x (hpow x)
  let iota_y : CyclicGroup p →* G := cyclicHom p y (hpow y)
  let Φ : CyclicGroup p × CyclicGroup p →* G :=
    iota_x.noncommCoprod iota_y fun _ _ => mul_comm _ _
  let g : CyclicGroup p := Multiplicative.ofAdd (1 : ZMod p)
  have hx_eq : iota_x g = x := cyclicHom_ofAdd_one p x (hpow x)
  have hy_eq : iota_y g = y := cyclicHom_ofAdd_one p y (hpow y)
  have hΦ_surj : Function.Surjective Φ := by
    rw [← MonoidHom.range_eq_top, ← top_le_iff,
      ← (Subgroup.isComplement'_of_card_mul_and_disjoint
          (by rw [hcard_x, hcard_y, ← sq, ← h]) hdisj).sup_eq_top, sup_le_iff]
    refine ⟨Subgroup.zpowers_le_of_mem ⟨(g, 1), ?_⟩,
            Subgroup.zpowers_le_of_mem ⟨(1, g), ?_⟩⟩
    · change iota_x g * iota_y 1 = x; rw [map_one, mul_one, hx_eq]
    · change iota_x 1 * iota_y g = y; rw [map_one, one_mul, hy_eq]
  exact ⟨(MulEquiv.ofBijective Φ ((Nat.bijective_iff_surjective_and_card Φ).mpr
    ⟨hΦ_surj, by rw [Nat.card_prod, card_cyclicGroup, ← sq, h]⟩)).symm⟩

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
