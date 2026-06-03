import Mathlib
import «M2rGroup7».SmallGroupsLibrary
import «M2rGroup7».Lemmas.GroupTheoryLemmas

set_option maxHeartbeats 800000

/-!
# Cyclic group definitions and the canonical action of C_p on C_{p²}

This file defines `CyclicGroup`, `cyclicHom`, and the canonical semidirect product
action `cpSqAction p : CyclicGroup p →* MulAut (CyclicGroup (p ^ 2))`.
-/

/-- The canonical action of `C_p` on `C_{p²}` by an automorphism of order p.
This is the unique (up to isomorphism) non-trivial semidirect product action. -/
noncomputable def cpSqAction (p : ℕ) [hp : Fact p.Prime] :
    CyclicGroup p →* MulAut (CyclicGroup (p ^ 2)) := by
  have iso := Classical.choice (aut_of_cyclic_p2 (h_p_prime := hp))
  let gen : CyclicGroup (p * (p - 1)) := Multiplicative.ofAdd 1
  let h : MulAut (CyclicGroup (p ^ 2)) := iso.symm (gen ^ (p - 1))
  apply cyclicHom p h
  change iso.symm (gen ^ (p - 1)) ^ p = 1

  rw [← map_pow, ← iso.symm.map_one]
  congr 1
  change (gen ^ (p - 1)) ^ p = 1
  rw [← pow_mul]
  have hord : orderOf gen = p * (p - 1) := by
    change addOrderOf (1 : ZMod (p * (p - 1))) = p * (p - 1)
    exact ZMod.addOrderOf_one _
  rw [show (p - 1) * p = p * (p - 1) from mul_comm _ _]
  have hpow : gen ^ (p * (p - 1)) = 1 := by
    have := pow_orderOf_eq_one gen; rwa [hord] at this
  exact hpow
