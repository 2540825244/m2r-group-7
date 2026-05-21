import Mathlib.Logic.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Equiv.Basic
import «M2rGroup7».SmallGroupsLibrary
import «M2rGroup7».PqCase
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Logic.Unique
import Mathlib.SetTheory.Cardinal.Finite
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

variable (G : Type*) [Group G]

theorem p2q_classification {p : ℕ} {q : ℕ} [h_p_prime : Fact p.Prime] [h_q_prime : Fact q.Prime] (h_p_ne_q : p ≠ q) (h_p_bound : p ≤ 3) (h : Nat.card G = p^2 * q) :
  True := by

    let n_p := Nat.card (Sylow p G)
    let n_q := Nat.card (Sylow q G)

    -- Claim 1: n_p = 1 or n_q = 1

    have n_p_or_n_q_one : n_p = 1 ∨ n_q = 1 := by
      rcases lt_trichotomy p q with h_lt | h_eq | h_gt
      · -- case h_lt : p < q
        sorry
      · -- case h_eq : p = q  (impossible since p ≠ q)
        exact absurd h_eq h_p_ne_q
      · -- case h_gt : q < p
        -- Step 1: n_p divides q and n_p ≡ 1 (mod p).

        let P : Sylow p G := default

        -- G is finite
        haveI : Finite G := by
          apply Nat.finite_of_card_ne_zero
          rw [h]
          have p_ne : p ≠ 0 := Nat.Prime.ne_zero h_p_prime.elim
          have q_ne : q ≠ 0 := Nat.Prime.ne_zero h_q_prime.elim
          simp; tauto

        -- Order of Sylow p-group is p^2
        have h_p_p2 : Nat.card P = p^2 := by
          rw [Sylow.card_eq_multiplicity]
          rw [h]
          have hcop : Nat.Coprime (p ^ 2) q := by
            exact (h_p_prime.out.coprime_iff_not_dvd.mpr (fun h => absurd (h_q_prime.out.eq_one_or_self_of_dvd p h)
              (by rintro (h1 | h2); exact h_p_prime.out.one_lt.ne' h1; exact h_p_ne_q h2))).pow_left 2
          rw [Nat.factorization_mul_of_coprime hcop, Finsupp.add_apply,
              Nat.factorization_pow_self h_p_prime.out,
              h_q_prime.out.factorization, Finsupp.single_apply, if_neg (Ne.symm h_p_ne_q), add_zero]

        -- Index of Sylow p-group is q
        have h_p_idx_q : P.index = q := by
          have h_index_mul_card := Subgroup.index_mul_card (↑P: Subgroup G)
          rw [h_p_p2, h] at h_index_mul_card
          have h_p_ne_zero := h_p_prime.elim.ne_zero
          nlinarith

        -- n_p divides q

        have h_n_p_div_q : n_p ∣ q := by
          have h_sylow_dvd_p_index := Sylow.card_dvd_index P
          rw [h_p_idx_q] at h_sylow_dvd_p_index
          exact h_sylow_dvd_p_index

        -- n_p is 1 (mod p)

        have h_n_p_one_mod_p : n_p ≡ 1 [MOD p] := by
          show Nat.card (Sylow p G) ≡ 1 [MOD p]
          exact card_sylow_modEq_one p G

        -- Step 2: Only divisor of q that's ≡ 1 (mod p) is 1. So n_p = 1.
        left
        rcases h_q_prime.out.eq_one_or_self_of_dvd n_p h_n_p_div_q with h | h
        · exact h
        · exfalso
          have hmod := h_n_p_one_mod_p
          rw [h] at hmod
          unfold Nat.ModEq at hmod
          rw [Nat.mod_eq_of_lt h_gt, Nat.mod_eq_of_lt h_p_prime.out.one_lt] at hmod
          linarith [h_q_prime.out.one_lt]


    -- Case 2: p < q

    -- Step 1: n_q can be either 1, p, p^2

    -- Step 2: n_q ≠ p as then q | p−1 contradicting p < q

    -- Step 3: If n_q ≠ 1, then n_q = p^2

    -- Step 4: p^2 Sylow q-subgroup are trivially intersecting, so contribute p²(q−1) elements of order q

    -- Step 5: Remaining p² elements form one Sylow p-subgroup, so n_p = 1
