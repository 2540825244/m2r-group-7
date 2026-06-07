import Mathlib
import «M2rGroup7».CyclicGroup
import «M2rGroup7».Lemmas.SylowUtils

theorem classification_4q [Group G] (h : Nat.card G = 30) :
  Nonempty (G ≃* CyclicGroup 30) := by
  haveI : Finite G := by
    apply Nat.finite_of_card_ne_zero; rw [h]
    omega
  let n_3 := Nat.card (Sylow 3 G)
  let n_5 := Nat.card (Sylow 5 G)
  haveI : Fact (Nat.Prime 5) := by decide
  have n_3_or_n_5_one : n_3 = 1 ∨ n_5 = 1 := pqr_group_has_normal_sylow_qr_subgroup G
    (p := 2) (q := 3) (r:= 5) (by omega) (by omega) (by omega)
  rcases n_3_or_n_5_one with h_n3_1 | h_n5_1
  · -- h_n3_1 : n_3 = 1
    sorry
  · sorry
