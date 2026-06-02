import «M2rGroup7».SixteenClassification.Preliminary
import «M2rGroup7».SixteenClassification.Blueprints

namespace OrderSixteen

lemma exists_normal_C8_or_C4_C2
    {G : Type*} [Group G]
    (hn : Nat.card G = 16)
    (h_non_iso : IsEmpty (G ≃* CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2)) :
    (∃ H : Subgroup G, H.Normal ∧ Nonempty (H ≃* CyclicGroup 8)) ∨
    (∃ H : Subgroup G, H.Normal ∧ Nonempty (H ≃* CyclicGroup 4 × CyclicGroup 2)) := by
  by_cases h_order_8 : ∃ x : G , orderOf x = 8
  · -- There is element of order 8, then C8 ◃ G
    left
    obtain ⟨x, hx⟩ := h_order_8
    let H := Subgroup.zpowers x
    use H
    have hi : H.index = 2 := by
      sorry
    haveI : H.Normal := Subgroup.normal_of_index_eq_two hi
    have h_card : Nat.card H = 8 := by
      sorry
    haveI : IsCyclic H := by
      sorry
    let iso : H ≃* CyclicGroup 8 := mulEquivOfCyclicCardEq (
        by simp only [h_card, card_cyclicGroup]
      )
    tauto
  · -- There are no elements of order 8, then K8 ◃ G
    right
    have h_max_order : ∃ z : G , orderOf z = 4 := by
      sorry
    obtain ⟨z, hz⟩ : ∃ z : G, orderOf z = 2 := by
      -- prime_dvd_card_center
      sorry
    let H := Subgroup.zpowers z
    haveI : H.Normal := by
      sorry
    by_cases hx : ∃ x : G , orderOf x = 4 ∧ x^2 ≠ z
    · -- There is x of order 4 such that x^2 ≠ z
      obtain ⟨x, hx⟩ := hx
      let L := Subgroup.zpowers x
      have h_disj : H ⊓ L = ⊥ := by
        sorry
      let K := Subgroup.closure {x, z}
      use K
      haveI : K.Normal := by
        sorry
      let iso : K ≃* CyclicGroup 4 × CyclicGroup 2 := by
        have h_card : Nat.card H = 2 := by
          sorry
        letI : H ≃* CyclicGroup 2 := mulEquivOfCyclicCardEq (
            by simp only [h_card, card_cyclicGroup]
          )
        have l_card : Nat.card L = 4 := by
          sorry
        letI : L ≃* CyclicGroup 4 := mulEquivOfCyclicCardEq (
            by simp only [l_card, card_cyclicGroup]
          )
        -- apply mulEquiv_sup_of_disjoint_comm
        sorry
      tauto
    · -- Every x of order 4 has x^2 = z
      have hx : ∀ x : G, orderOf x = 4 → x^2 = z := by simp_all
      sorry

theorem realise_ext_type_if_not_iso_to_C2_4
    {G : Type*} [Group G]
    (hn : Nat.card G = 16)
    (h_non_iso : IsEmpty (G ≃* CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2)) :
    Nonempty (RealiseExtType G ext_16_1) ∨
    Nonempty (RealiseExtType G ext_16_2) ∨
    Nonempty (RealiseExtType G ext_16_3) ∨
    Nonempty (RealiseExtType G ext_16_4) ∨
    Nonempty (RealiseExtType G ext_16_5) ∨
    Nonempty (RealiseExtType G ext_16_6) ∨
    Nonempty (RealiseExtType G ext_16_7) ∨
    Nonempty (RealiseExtType G ext_16_8) ∨
    Nonempty (RealiseExtType G ext_16_9) ∨
    Nonempty (RealiseExtType G ext_16_10) ∨
    Nonempty (RealiseExtType G ext_16_11) ∨
    Nonempty (RealiseExtType G ext_16_12) ∨
    Nonempty (RealiseExtType G ext_16_13) := by
  sorry

end OrderSixteen
