import Mathlib.Logic.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Equiv.Basic
import «M2rGroup7».SmallGroupsLibrary
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Logic.Unique

def maximumOrder : Nat := 3

variable (n : ℕ) (G : Type*) [Group G]

macro "classify_prime" p:num h:term : tactic => `(tactic|(
  have : Fact (Nat.Prime $p) := ⟨by decide⟩
  use 1
  have hr : MulEquiv (retrieve $p 1) (CyclicGroup $p) := by
    have hr_is_c : retrieve $p 1 = CyclicGroup $p := by rfl
    exact (MulEquiv.refl (CyclicGroup $p))
  apply Nonempty.intro
  have hg : MulEquiv G (CyclicGroup $p) := by
    have h_g_card : Nat.card G = $p := $h
    have : IsCyclic G := isCyclic_of_prime_card h_g_card
    refine (mulEquivOfCyclicCardEq ?_)
    have h_r_card : Nat.card (CyclicGroup $p) = $p := card_cyclicGroup $p
    rw [h_g_card, h_r_card]
  apply MulEquiv.symm at hr
  exact MulEquiv.trans hg hr))

theorem classification [hp : Fact (n <= maximumOrder)] (h : Nat.card G = n) :
  (∃ i : Nat, Nonempty (MulEquiv G (retrieve n i)))
 :=
  match n with
  | 1 => by
    use 1
    apply Nonempty.intro

    have : Unique (retrieve 1 1) := by
      have hr : retrieve 1 1 = Unit := by rfl
      rw [hr]
      infer_instance

    have hg := Nat.card_eq_one_iff_unique.mp h
    have h_nonempty := hg.right
    have : Subsingleton G := hg.left
    have : Inhabited G := Classical.inhabited_of_nonempty h_nonempty
    have h_unique := Unique.mk' G

    exact MulEquiv.ofUnique

  | 2 => by
    classify_prime 2 h

  | 3 => by
    classify_prime 3 h

  | 4 => by
    sorry

  | 5 => by
    classify_prime 5 h

  | 6 => by
    sorry

  | 7 => by
    classify_prime 7 h

  | 8 => by
    sorry

  | 9 => by
    sorry

  | 10 => by
    sorry

  | 11 => by
    classify_prime 11 h

  | _ => by
    have hn := n > maximumOrder
    sorry
