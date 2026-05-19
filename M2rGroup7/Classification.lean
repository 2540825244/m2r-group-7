import Mathlib.Logic.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Equiv.Basic
import «M2rGroup7».SmallGroupsLibrary
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

def maximumOrder : Nat := 3

variable (n : ℕ) (G : Type*) [Group G]

theorem classification [hp: Fact (n <= maximumOrder)] (h : Nat.card G = n) :
  (∃ i : Nat, Nonempty (MulEquiv G (retrieve n i)))
 :=
  match n with
  | 1 => by
    -- use 1
    -- apply Nonempty.intro
    -- have : Unique G := Nat.card_eq_one_iff_unique.mp h
    -- exact (MulEquiv.ofUnique G (retrieve 1 1))
    sorry

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
