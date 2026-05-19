import Mathlib.Logic.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Equiv.Basic
import «M2rGroup7».SmallGroupsLibrary
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Logic.Unique

def maximumOrder : Nat := 3

variable (n : ℕ) (G : Type*) [Group G]

theorem classification [hp: Fact (n <= maximumOrder)] (h : Nat.card G = n) :
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
    use 1
    sorry
  | 3 => by
    use 1
    sorry
  | _ => by
    have hn := n > maximumOrder
    sorry

theorem prime_classification [hp: Fact n.Prime] (h : Nat.card G = n) :
  (∃ i : Nat, Nonempty (MulEquiv G (retrieve n i)))
 :=
  -- apply isCyclic_of_prime_card
  sorry
