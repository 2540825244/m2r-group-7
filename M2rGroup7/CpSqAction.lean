import Mathlib

set_option maxHeartbeats 800000

/-!
# Cyclic group definitions and the canonical action of C_p on C_{p²}

This file defines `CyclicGroup`, `cyclicHom`, and the canonical semidirect product
action `cpSqAction p : CyclicGroup p →* MulAut (CyclicGroup (p ^ 2))`.
-/

/-- Cyclic group of order n as a multiplicative type. -/
def CyclicGroup (n : Nat) [NeZero n] := Multiplicative (ZMod n)
  deriving DecidableEq, Group, IsCyclic, Fintype, DivisionCommMonoid

theorem card_cyclicGroup (n : Nat) [NeZero n] : Nat.card (CyclicGroup n) = n := by
  delta CyclicGroup
  rw [Nat.card_congr Multiplicative.toAdd]
  exact Nat.card_zmod n

/-- Build a monoid hom out of `CyclicGroup n` from an element whose `n`th power is `1`. -/
def cyclicHom (n : Nat) [NeZero n] {G : Type*} [Group G] (a : G) (h : a ^ n = 1) :
    CyclicGroup n →* G :=
  AddMonoidHom.toMultiplicativeLeft <| ZMod.lift n
    ⟨zmultiplesHom (Additive G) (Additive.ofMul a), by
      change (n : ℤ) • Additive.ofMul a = 0
      rw [← ofMul_zpow, zpow_natCast, h, ofMul_one]⟩

instance instNeZeroPrimePow {p : ℕ} [h : Fact p.Prime] {n : ℕ} : NeZero (p ^ n) := by
  have hp : Nat.Prime p := h.out
  exact ⟨(pow_pos hp.pos n).ne'⟩

instance instNeZeroPrimeMulPredPrime {p : ℕ} [h : Fact p.Prime] : NeZero (p * (p - 1)) := by
  have hp : Nat.Prime p := h.out
  have h2 : 2 ≤ p := hp.two_le
  exact ⟨Nat.mul_ne_zero (by omega) (by omega)⟩

lemma aut_of_cyclic_p2 {p : ℕ} [h_p_prime : Fact p.Prime] :
    Nonempty (MulAut (CyclicGroup (p ^ 2)) ≃* CyclicGroup (p * (p - 1))) := by
  have h_aut_c_p2_iso_cyclic : MulAut (CyclicGroup (p ^ 2)) ≃* (ZMod (p ^ 2))ˣ := by
    have h_aut := IsCyclic.mulAutMulEquiv (CyclicGroup (p ^ 2))
    rw [card_cyclicGroup (p ^ 2)] at h_aut
    exact h_aut
  have h_units_cyclic : IsCyclic (ZMod (p ^ 2))ˣ := by
    by_cases h_p2 : p = 2
    · subst h_p2; exact ZMod.isCyclic_units_four
    · exact ZMod.isCyclic_units_of_prime_pow p h_p_prime.out h_p2 2
  have h_zmod_unit_order : Nat.card ((ZMod (p ^ 2))ˣ) = (p ^ 2).totient := by
    rw [Nat.card_eq_fintype_card]; exact ZMod.card_units_eq_totient (p ^ 2)
  have h_p2_totient : (p ^ 2).totient = p * (p - 1) := by
    have := Nat.totient_prime_pow_succ h_p_prime.out 1; grind
  rw [h_p2_totient] at h_zmod_unit_order
  have h_iso_helper : Multiplicative (ZMod (p * (p - 1))) ≃* (ZMod (p ^ 2))ˣ := by
    have h' := zmodCyclicMulEquiv h_units_cyclic
    rw [h_zmod_unit_order] at h'; exact h'
  have h_iso : CyclicGroup (p * (p - 1)) ≃* (ZMod (p ^ 2))ˣ := h_iso_helper
  exact ⟨h_aut_c_p2_iso_cyclic.trans h_iso.symm⟩

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
