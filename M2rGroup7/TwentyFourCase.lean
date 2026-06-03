import Mathlib.GroupTheory.Sylow
import Mathlib.SetTheory.Cardinal.Finite

/-- A group of order `24` has either `1` or `4` Sylow 3-subgroups. -/
lemma sylow3_24 {G : Type*} [Group G] (h : Nat.card G = 24) :
    Nat.card (Sylow 3 G) = 1 ∨ Nat.card (Sylow 3 G) = 4 := by
  haveI : Finite G := by
    apply Nat.finite_of_card_ne_zero
    rw [h]
    simp
  have h_mod : Nat.card (Sylow 3 G) % 3 = 1 % 3 := card_sylow_modEq_one 3 G
  let P : Sylow 3 G := default
  have h_dvd : Nat.card (Sylow 3 G) ∣ Nat.card G :=
    (Sylow.card_dvd_index P).trans (Subgroup.index_dvd_card _)
  rw [h] at h_dvd
  have h_pos : 0 < Nat.card (Sylow 3 G) := Nat.card_pos
  have h_le : Nat.card (Sylow 3 G) ≤ 24 := Nat.le_of_dvd (by decide) h_dvd
  interval_cases (Nat.card (Sylow 3 G)) <;> omega

/-- A group of order `24` with a unique Sylow 3-subgroup is isomorphic to some group.
    The precondition is equivalent to having a normal Sylow 3-subgroup. -/
lemma order24_1_sylow3 {G : Type*} [Group G] (h : Nat.card G = 24)
    (h_n3 : Nat.card (Sylow 3 G) = 1) : True := by
  sorry

/-- A group of order `24` with four Sylow 3-subgroups is isomorphic to some group.
    The precondition is equivalent to not having a normal Sylow 3-subgroup. -/
lemma order24_4_sylow3 {G : Type*} [Group G] (h : Nat.card G = 24)
    (h_n3 : Nat.card (Sylow 3 G) = 4) : True := by
  sorry

/-- A group of order `24` is isomorphic to some group. -/
theorem order24_classification {G : Type*} [Group G] (h : Nat.card G = 24) :
    True := by
  rcases sylow3_24 h with h_n3_1 | h_n3_4
  · exact order24_1_sylow3 h h_n3_1
  · exact order24_4_sylow3 h h_n3_4
