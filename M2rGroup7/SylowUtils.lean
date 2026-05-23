import Mathlib.GroupTheory.Sylow
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finite.Card

/-- In a finite group of order p^a * q^b (p, q distinct primes),
    every Sylow p-subgroup has order p^a. -/
lemma sylow_card_eq {p q : ℕ} {a b : ℕ}
    [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q)
    {G : Type*} [Group G] [Finite G]
    (h : Nat.card G = p ^ a * q ^ b) (P : Sylow p G) :
    Nat.card ↥(P : Subgroup G) = p ^ a := by
  rw [Sylow.card_eq_multiplicity, h]
  have hcop : Nat.Coprime (p ^ a) (q ^ b) :=
    ((hp.out.coprime_iff_not_dvd.mpr fun hdvd =>
      absurd (hq.out.eq_one_or_self_of_dvd p hdvd)
        (by rintro (h1 | h2)
            · exact hp.out.one_lt.ne' h1
            · exact hpq h2)).pow_left a).pow_right b
  rw [Nat.factorization_mul_of_coprime hcop, Finsupp.add_apply,
      Nat.factorization_pow_self hp.out]
  have hqb : (q ^ b).factorization p = 0 := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, hq.out.factorization,
        Finsupp.single_apply, if_neg (Ne.symm hpq)]
    simp
  rw [hqb, add_zero]

/-- In a finite group of order p^a * q^b (p, q distinct primes),
    every Sylow p-subgroup has index q^b. -/
lemma sylow_index_eq {p q : ℕ} {a b : ℕ}
    [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q)
    {G : Type*} [Group G] [Finite G]
    (h : Nat.card G = p ^ a * q ^ b) (P : Sylow p G) :
    (P : Subgroup G).index = q ^ b := by
  have hcard := Subgroup.index_mul_card (P : Subgroup G)
  rw [sylow_card_eq hpq h P, h] at hcard
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.out.pos a) (hcard.trans (mul_comm _ _))
