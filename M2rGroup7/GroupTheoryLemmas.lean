import Mathlib.GroupTheory.SpecificGroups.Cyclic
import «M2rGroup7».SmallGroupsLibrary

/-- A group homomorphism out of a cyclic group is fully determined by
    its value on a generator. -/
lemma monoidHom_eq_of_generator_eq
    {G H : Type*} [Group G] [Group H]
    {f_1 f_2 : G →* H}
    {g : G} (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (h : f_1 g = f_2 g) : f_1 = f_2 := by
    ext x
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    rw [← hl, map_zpow f_1 g l, map_zpow f_2 g l, h]

theorem cyclic_subgroup_of_cyclic_group_is_unique {n d : ℕ} (h_d_div_n : d ∣ n) (h_n_pos : n > 0) : Nat.card ({K : Subgroup (CyclicGroup n) | Nat.card K = d}) = 1
:= by
  -- Step 1:
  sorry
