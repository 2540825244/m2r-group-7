import «M2rGroup7».SmallGroupsLibrary
import «M2rGroup7».Classification
import «M2rGroup7».Uniqueness

theorem unique_classification
    (G : Type*) [Group G]
    (hpos : Nat.card G > 0) (hmax : Nat.card G <= maximumOrder) :
    ∃! i : Nat, ∃ _ : ValidIndex (Nat.card G) i,
      Nonempty (MulEquiv G (retrieve (Nat.card G) i)) := by
  haveI : NeZero (Nat.card G) := ⟨by omega⟩
  haveI : Fact (Nat.card G ≤ maximumOrder) := ⟨hmax⟩
  obtain ⟨i, hv, hiso⟩ := classification (Nat.card G) G rfl
  refine ⟨i, ⟨hv, hiso⟩, fun i' ⟨hv', hiso'⟩ => ?_⟩
  by_contra hi_ne
  haveI : ValidIndex (Nat.card G) i := hv
  haveI : ValidIndex (Nat.card G) i' := hv'
  haveI : Fact (Nat.card G ≠ Nat.card G ∨ i ≠ i') := ⟨Or.inr (Ne.symm hi_ne)⟩
  obtain ⟨f⟩ := hiso
  obtain ⟨g⟩ := hiso'
  exact (uniqueness (Nat.card G) i (Nat.card G) i').false (f.symm.trans g)
