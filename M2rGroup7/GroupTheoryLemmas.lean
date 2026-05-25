import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Logic.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Equiv.Basic
import «M2rGroup7».PqCase
import «M2rGroup7».SylowUtils
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Logic.Unique
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Fintype.Defs
import Mathlib.SetTheory.Cardinal.Defs
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.PNat.Prime
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.PGroup
import OrderPQ
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Finite.Card
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.Nat.Totient

/-- A group homomorphism out of a cyclic group is fully determined by
    its value on a generator. -/
lemma monoidHom_eq_of_generator_eq
    {G H : Type*} [Group G] [Group H]
    {f_1 f_2 : G →* H}
    {g : G} (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (h : f_1 g = f_2 g) : f_1 = f_2 := by
    ext x
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    rw [← hl, map_zpow f_1 g l, map_zpow f_2 g l, h]

lemma cyclic_subgroup_of_cyclic_group_is_unique {n d : ℕ} (h_d_div_n : d ∣ n) (h_n_pos : n > 0) : Nat.card ({K : Subgroup (CyclicGroup n) | Nat.card K = d}) = 1
:= by
  -- Step 1:
  sorry

lemma aut_of_cyclic_p2 {p : ℕ} [h_p_prime : Fact p.Prime] : Nonempty (MulAut (CyclicGroup (p ^ 2)) ≃* CyclicGroup (p * (p - 1))) := by
    -- Aut(C_(p^2)) ≃* (ZMod (p ^ 2))ˣ
    have h_aut_c_p2_iso_cyclic : MulAut (CyclicGroup (p ^ 2)) ≃* (ZMod (p ^ 2))ˣ := by
        have h_aut := IsCyclic.mulAutMulEquiv (CyclicGroup (p ^ 2))
        rw [card_cyclicGroup (p ^ 2)] at h_aut
        exact h_aut

    -- (ZMod (p ^ 2))ˣ is cyclic
    have h_units_cyclic : IsCyclic (ZMod (p ^ 2))ˣ := by
        by_cases h_p2 : p = 2
        · subst h_p2
          exact ZMod.isCyclic_units_four
        · exact ZMod.isCyclic_units_of_prime_pow p h_p_prime.out h_p2 2

    have h_zmod_unit_order : Nat.card ((ZMod (p ^ 2))ˣ) = (p ^ 2).totient := by
        have := _root_.ZMod.card_units_eq_totient (p ^ 2)
        rw [Nat.card_eq_fintype_card]
        exact this

    have h_p2_totient : (p ^ 2).totient = p * (p - 1) := by
        have := Nat.totient_prime_pow_succ h_p_prime.out 1
        grind

    rw [h_p2_totient] at h_zmod_unit_order

    have h_iso_helper : Multiplicative (ZMod (p * (p - 1))) ≃* (ZMod (p ^ 2))ˣ := by
        have h' := zmodCyclicMulEquiv h_units_cyclic
        rw [h_zmod_unit_order] at h'
        exact h'

    have h_iso : CyclicGroup (p * (p - 1)) ≃* (ZMod (p ^ 2))ˣ := h_iso_helper

    have h_aut_equiv : MulAut (CyclicGroup (p ^ 2)) ≃* CyclicGroup (p * (p - 1)) :=
        h_aut_c_p2_iso_cyclic.trans h_iso.symm

    exact Nonempty.intro h_aut_equiv
