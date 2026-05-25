import Mathlib.GroupTheory.Sylow
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finite.Card
import Mathlib.GroupTheory.SemidirectProduct
import «M2rGroup7».GroupTheoryLemmas

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

theorem semidirectProduct_iso_of_conjugate_action
    {H K : Type*} [Group H] [Group K]
    {f_1 f_2 : K →* MulAut H}
    (h : MulAut H) (β : MulAut K)
    (hconj : ∀ x : K, f_2 x = h * f_1 (β x) * h⁻¹) :
    Nonempty (SemidirectProduct H K f_1 ≃* SemidirectProduct H K f_2) :=
  ⟨SemidirectProduct.congr h β.symm fun g => by
    ext n
    simp [MulEquiv.trans_apply, hconj (β.symm g), MulAut.mul_apply,
          MulAut.inv_apply, MulEquiv.apply_symm_apply]⟩

/-- WIP, do not use this lemma
    If K is cyclic and Aut(H) is abelian, two homomorphisms f g : K → Aut(H) define
    isomorphic semidirect products if they have the same image. -/
lemma semidirectProduct_iso_iff_range_eq
    {H K : Type*} [Group H] [Group K] [IsCyclic K]
    (h_mul_comm : IsMulCommutative (MulAut H))
    (f_1 f_2 : K →* MulAut H) (h_range_eq : f_1.range = f_2.range) :
    Nonempty (SemidirectProduct H K f_1 ≃* SemidirectProduct H K f_2) := by
  -- k is a generator of K
  obtain ⟨k, hk⟩ := IsCyclic.exists_generator (α := K)

  have : ∃ β : (MulAut K), ∀ x : K, f_2 x = f_1 (β x) := by

    sorry

  obtain ⟨β, hβ⟩ := this

  exact semidirectProduct_iso_of_conjugate_action 1 β (by simp [hβ])

  -- Goal: f_2(x) = h f_1(beta(x)) h^-1 for every x in K, h in Aut(H), for some beta in Aut(K)
  -- Equivalent to: f_2(k) = f_1(beta(k)) for some beta in Aut(K)
  -- Now f_1 to Im(f_1) to f_2 is a isomorphism between K and K, so let beta be that and done
