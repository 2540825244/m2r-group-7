import Mathlib.Logic.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Equiv.Basic
import «M2rGroup7».SmallGroupsLibrary
import «M2rGroup7».PqCase
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Logic.Unique
import OrderPQ

def maximumOrder : Nat := 9

variable (n : ℕ) (G : Type*) [Group G]

theorem prime_classification [hn : Fact n.Prime] (h : Nat.card G = n) :
(Nonempty (MulEquiv G (CyclicGroup n))) := by
  apply Nonempty.intro
  have h_g_card : Nat.card G = n := h
  have : IsCyclic G := isCyclic_of_prime_card h_g_card
  refine (mulEquivOfCyclicCardEq ?_)
  have h_c_card: Nat.card (CyclicGroup n) = n := card_cyclicGroup n
  rw [h_g_card, h_c_card]

macro "classify_prime" p:num h:term : tactic => `(tactic|(
  have : Fact (Nat.Prime $p) := ⟨by decide⟩
  use 1
  have hr : MulEquiv (retrieve $p 1) (CyclicGroup $p) := by
    have hr_is_c : retrieve $p 1 = CyclicGroup $p := by rfl
    exact (MulEquiv.refl (CyclicGroup $p))
  apply prime_classification
  exact $h))

macro "classify_prime_sq" p:num h:term : tactic => `(tactic|(
  haveI : Fact (Nat.Prime $p) := ⟨by decide⟩
  obtain (hiso | hiso) := p_squared_classification (p := $p) ($h |>.trans (by decide))
  · exact ⟨1, hiso⟩
  · exact ⟨2, hiso⟩))

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

  | 4 => by classify_prime_sq 2 h

  | 5 => by
    classify_prime 5 h

  | 6 => by
    obtain (hiso | hiso) := order6_classification h
    · exact ⟨2, hiso⟩
    · exact ⟨1, hiso⟩

  | 7 => by
    classify_prime 7 h

  | 8 => by
    sorry

  | 9 => by classify_prime_sq 3 h

  | 10 => by
    sorry

  | 11 => by
    classify_prime 11 h

  | _ => by
    have hn := n > maximumOrder
    sorry
