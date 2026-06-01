import «M2rGroup7».SmallGroupsLibrary
import «M2rGroup7».PqCase
import Mathlib

namespace OrderSixteen

/-- Isomorphism for Wild's Fact 1. -/
noncomputable def fact1_mulEquiv
    {G : Type*} [Group G] (H₁ H₂ : Subgroup G)
    (h_disj : H₁ ⊓ H₂ = ⊥)
    (h_comm : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x) :
    (H₁ × H₂) ≃* ↑(H₁ ⊔ H₂) :=
  sorry

/-- Wild's Fact 1: If `H₁` and `H₂` are subgroups of `G` such that `H₁ ⊓ H₂ = {e}`
    and `∀ x ∈ H₁, ∀ y ∈ H₂, xy = yx`,
    then `H₁H₂` is a subgroup isomorphic to the direct product  `H₁ × H₂`. -/
lemma fact1 {G : Type*} [Group G] (H₁ H₂ : Subgroup G)
    (h_disj : H₁ ⊓ H₂ = ⊥)
    (h_comm : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x) :
    Nonempty (H₁ × H₂ ≃* ↑(H₁ ⊔ H₂)) :=
  ⟨fact1_mulEquiv H₁ H₂ h_disj h_comm⟩


/-- Wild's Fact 2, first part: If the order of each member of `G` is at most 2,
    then `G` is abelian. -/
lemma fact2_part1 {G : Type*} [Group G] (h : ∀ x : G, x ^ 2 = 1) :
    IsMulCommutative G := sorry

/-- Wild's Fact 2, second part: If the order of each member of `G` is at most 2
    and `G` is finite, then `G ≃ C₂ × ⋯ × C₂`. -/
lemma fact2_part2 {G : Type*} [Group G] [Finite G] (h : ∀ x : G, x ^ 2 = 1) :
    ∃ n : ℕ, Nonempty (G ≃* (Fin n → CyclicGroup 2)) := sorry

structure ExtensionType where
  N : Type*
  [g : Group N]
  n : Nat
  act : MulAut N
  glue : N
  map_glue : act glue = glue
  pow_n : act^ n = MulAut.conj glue

instance (E : ExtensionType) : Group E.N := E.g

structure ExtRel (E_1 E_2 : ExtensionType) where
  φ : E_1.N ≃* E_2.N
  act_conj : E_2.act = (φ.symm.trans E_1.act).trans φ
  act_glue : E_2.glue = φ E_1.glue



end OrderSixteen
