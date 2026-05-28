import «M2rGroup7».SmallGroupsLibrary
import «M2rGroup7».PqCase
import Mathlib

namespace OrderSixteen.Prelim

/-- Center of a $p$-group is nontrivial: if $G$ is a nontrivial finite $p$-group
then $Z(G)$ is nontrivial. Direct wrapper around `IsPGroup.center_nontrivial`. -/
theorem pgroup_center_nontrivial {p : ℕ} {G : Type*} [Group G] [Finite G] [Nontrivial G]
    (hp : IsPGroup p G) : Nontrivial (Subgroup.center G) :=
  sorry

/-- For a finite group $G$, $|Z(G)|$ divides $|G|$. Direct wrapper around
`Subgroup.card_subgroup_dvd_card` applied to the center. -/
theorem center_divides_card (G : Type*) [Group G] [Finite G] :
    Nat.card (Subgroup.center G) ∣ Nat.card G :=
  sorry

/-- Divisors of $16 = 2^4$ are powers of $2$ with exponent at most $4$. -/
theorem two_power_divisors {d : ℕ} (h : d ∣ 16) :
    ∃ k ≤ 4, d = 2 ^ k :=
  sorry

/-- If $|G| = 16$ then $G$ is a $2$-group. Direct wrapper around
`IsPGroup.of_card` with $16 = 2^4$. -/
theorem pgroup_of_card_sixteen {G : Type*} [Group G] (h : Nat.card G = 16) :
    IsPGroup 2 G :=
  sorry

/-- A group of prime cardinality is cyclic. Direct wrapper around
Mathlib's `isCyclic_of_prime_card`. -/
theorem cyclic_of_prime_card {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (h : Nat.card G = p) : IsCyclic G :=
  sorry

/-- If every element of $G$ satisfies $x^2 = 1$, then $G$ is abelian.
Wrapper around `Commute.of_orderOf_dvd_two`. -/
theorem order2_implies_abelian {G : Type*} [Group G]
    (h : ∀ x : G, x ^ 2 = 1) : ∀ a b : G, a * b = b * a :=
  sorry

/-- Fundamental theorem of finite abelian groups: every finite abelian group
(written additively) is isomorphic to a direct sum of cyclic groups of
prime-power order. Wrapper around `AddCommGroup.equiv_directSum_zmod_of_finite`.

The statement mirrors the Mathlib shape (additive form). -/
theorem fundamental_finite_abelian (G : Type*) [AddCommGroup G] [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ) (_ : ∀ i, n i ≠ 0),
      Nonempty (G ≃+ ⨁ i : ι, ZMod (n i)) :=
  sorry

/-- A group $G$ is commutative iff $Z(G) = \top$. -/
theorem abelian_iff_center_top (G : Type*) [Group G] :
    (∀ a b : G, a * b = b * a) ↔ Subgroup.center G = ⊤ :=
  sorry

/-- If $G/Z(G)$ is cyclic, then $G$ is commutative. Wrapper around
`commutative_of_cyclic_center_quotient` applied to the canonical surjection
$G \to G / Z(G)$. -/
theorem cyclic_center_quotient_abelian (G : Type*) [Group G]
    (h : IsCyclic (G ⧸ Subgroup.center G)) :
    ∀ a b : G, a * b = b * a :=
  sorry

/-- If $G$ is a finite group then $|G/Z(G)| \cdot |Z(G)| = |G|$.
Wrapper around `Subgroup.index_mul_card` applied to the center, together with
the identification of $|G/Z(G)|$ with the index of $Z(G)$. -/
theorem quotient_by_center_card (G : Type*) [Group G] [Finite G] :
    Nat.card (G ⧸ Subgroup.center G) * Nat.card (Subgroup.center G) = Nat.card G :=
  sorry

end OrderSixteen.Prelim

namespace OrderSixteen

variable (G : Type*) [h_group : Group G] [Finite G] {h_sixteen : Nat.card G = 16}

theorem center_order_sixteen (h : Nat.card (Subgroup.center G) = 16)
  : Nonempty (G ≃* CyclicGroup 16) ∨
    Nonempty (G ≃* CyclicGroup 8 × CyclicGroup 2) ∨
    Nonempty (G ≃* CyclicGroup 4 × CyclicGroup 4) ∨
    Nonempty (G ≃* CyclicGroup 4 × CyclicGroup 2 × CyclicGroup 2) ∨
    Nonempty (G ≃* CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2)
  := by
  sorry

theorem center_order_eight (h : Nat.card (Subgroup.center G) = 8)
  : False
  := by
  haveI : CommGroup G := {
    h_group with
      mul_comm := sorry
  }
  have : Subgroup.center G = ⊤ := sorry
  sorry

theorem center_order_four (h : Nat.card (Subgroup.center G) = 4)
  : Nonempty (G ≃* (CyclicGroup 2 × CyclicGroup 2) ⋊[c4OnC2sqSwap] CyclicGroup 4) ∨
    Nonempty (G ≃* CyclicGroup 4 ⋊[c4OnC4Inv] CyclicGroup 4) ∨
    Nonempty (G ≃* CyclicGroup 8 ⋊[c2OnC8Pow5] CyclicGroup 2) ∨
    Nonempty (G ≃* CyclicGroup 2 × DihedralGroup 4) ∨
    Nonempty (G ≃* CyclicGroup 2 × QuaternionGroup 2) ∨
    Nonempty (G ≃* (CyclicGroup 4 × CyclicGroup 2) ⋊[c2OnK8Psi6] CyclicGroup 2)
  := by
  sorry

theorem center_order_two (h : Nat.card (Subgroup.center G) = 2)
  : Nonempty (G ≃* DihedralGroup 8) ∨
    Nonempty (G ≃* CyclicGroup 8 ⋊[c2OnC8Pow3] CyclicGroup 2) ∨
    Nonempty (G ≃* QuaternionGroup 4)
  := by
  sorry

end OrderSixteen

theorem sixteen_classification {G : Type*} [Group G] (h_sixteen : Nat.card G = 16)
  : ∃ i : Nat, ∃ hv : ValidIndex 16 i,
    haveI : ValidIndex 16 i := hv
    Nonempty (MulEquiv G (retrieve 16 i))
  := by
  haveI h_finite : Finite G := Nat.finite_of_card_ne_zero (by rw [h_sixteen]; norm_num)
  haveI h_nontrivial : Nontrivial G := by
    haveI : Fintype G := Fintype.ofFinite G
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, h_sixteen]
    norm_num
  have h_2group : IsPGroup 2 G :=
    IsPGroup.of_card (show Nat.card G = 2 ^ 4 from by rw [h_sixteen]; norm_num)
  haveI h_center_nontrivial : Nontrivial ↥(Subgroup.center G) :=
    IsPGroup.center_nontrivial h_2group
  have h_center_gt_one : 1 < Nat.card ↥(Subgroup.center G) := Finite.one_lt_card
  have h_center_dvd : Nat.card ↥(Subgroup.center G) ∣ 16 := by
    have := Subgroup.card_subgroup_dvd_card (Subgroup.center G)
    rwa [h_sixteen] at this
  obtain ⟨k, hk_le, hk_eq⟩ : ∃ k ≤ 4, Nat.card ↥(Subgroup.center G) = 2 ^ k := by
    rwa [show (16 : ℕ) = 2 ^ 4 from by norm_num,
         Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)] at h_center_dvd
  interval_cases k
  · -- k = 0: |Z(G)| = 1, contradicts nontrivial center
    simp only [pow_zero] at hk_eq; linarith
  · -- k = 1: |Z(G)| = 2
    norm_num at hk_eq
    obtain (hiso | hiso | hiso) := OrderSixteen.center_order_two G hk_eq
    · exact ⟨7, by decide, hiso⟩
    · exact ⟨8, by decide, hiso⟩
    · exact ⟨9, by decide, hiso⟩
  · -- k = 2: |Z(G)| = 4
    norm_num at hk_eq
    obtain (hiso | hiso | hiso | hiso | hiso | hiso) := OrderSixteen.center_order_four G hk_eq
    · exact ⟨3, by decide, hiso⟩
    · exact ⟨4, by decide, hiso⟩
    · exact ⟨6, by decide, hiso⟩
    · exact ⟨11, by decide, hiso⟩
    · exact ⟨12, by decide, hiso⟩
    · exact ⟨13, by decide, hiso⟩
  · -- k = 3: |Z(G)| = 8, impossible (center_order_eight returns False)
    norm_num at hk_eq
    exact (OrderSixteen.center_order_eight G hk_eq).elim
  · -- k = 4: |Z(G)| = 16, G is abelian
    norm_num at hk_eq
    obtain (hiso | hiso | hiso | hiso | hiso) := OrderSixteen.center_order_sixteen G hk_eq
    · exact ⟨1, by decide, hiso⟩
    · exact ⟨5, by decide, hiso⟩
    · exact ⟨2, by decide, hiso⟩
    · exact ⟨10, by decide, hiso⟩
    · exact ⟨14, by decide, hiso⟩
