import Mathlib.Logic.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Equiv.Basic
import «M2rGroup7».SmallGroupsLibrary
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Logic.Unique
import OrderPQ

/-- A group of order p² is isomorphic to CyclicGroup (p²) or CyclicGroup p × CyclicGroup p. -/
theorem p_squared_classification {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G]
    (h : Nat.card G = p ^ 2) :
    Nonempty (G ≃* CyclicGroup (p ^ 2)) ∨ Nonempty (G ≃* CyclicGroup p × CyclicGroup p) := by
  by_cases hc : IsCyclic G
  · left
    haveI := hc
    exact ⟨mulEquivOfCyclicCardEq (h.trans (card_cyclicGroup (p ^ 2)).symm)⟩
  · right
    obtain ⟨e⟩ := nonempty_mulEquiv_prod_of_card_eq_prime_pow_two_of_not_isCyclic h hc
    -- MulZMod p and CyclicGroup p are both def Multiplicative (ZMod p), so equal
    haveI : NeZero p := ⟨hp.elim.pos.ne'⟩
    have hmz : MulZMod p ≃* CyclicGroup p :=
      mulEquivOfCyclicCardEq (nat_card_mulZMod.trans (card_cyclicGroup p).symm)
    exact ⟨e.trans (MulEquiv.prodCongr hmz hmz)⟩

/-- A group of order 6 is isomorphic to CyclicGroup 6 or DihedralGroup 3. -/
theorem order6_classification {G : Type*} [Group G] (h : Nat.card G = 6) :
    Nonempty (G ≃* CyclicGroup 6) ∨ Nonempty (G ≃* DihedralGroup 3) := by
  by_cases hc : IsCyclic G
  · left
    haveI := hc
    exact ⟨mulEquivOfCyclicCardEq (h.trans (card_cyclicGroup 6).symm)⟩
  · right
    haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
    haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
    have hD : Nat.card (DihedralGroup 3) = 2 * 3 := DihedralGroup.nat_card
    have hDnc : ¬IsCyclic (DihedralGroup 3) := DihedralGroup.not_isCyclic (by decide)
    have h23 : Nat.card G = 2 * 3 := by linarith
    exact nonempty_mulEquiv_of_card_eq_prime_mul_prime_of_not_isCyclic' (by norm_num) h23 hc hD hDnc

/-- A group of order 10 is isomorphic to CyclicGropu 10 or DihedralGroup 5. -/
theorem order10_classification {G : Type*} [Group G] (h : Nat.card G = 10) :
    Nonempty (G ≃* CyclicGroup 10) ∨ Nonempty (G ≃* DihedralGroup 5) := by
  by_cases hc : IsCyclic G
  · left
    haveI := hc
    exact ⟨mulEquivOfCyclicCardEq (h.trans (card_cyclicGroup 10).symm)⟩
  · right
    haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
    haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hD : Nat.card (DihedralGroup 5) = 2 * 5 := DihedralGroup.nat_card
    have hDnc : ¬IsCyclic (DihedralGroup 5) := DihedralGroup.not_isCyclic (by decide)
    have h25 : Nat.card G = 2 * 5 := by linarith
    exact nonempty_mulEquiv_of_card_eq_prime_mul_prime_of_not_isCyclic' (by norm_num) h25 hc hD hDnc
