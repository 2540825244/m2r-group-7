import «M2rGroup7».SixteenClassification.Preliminary
import «M2rGroup7».SixteenClassification.Extensions
import «M2rGroup7».SixteenClassification.Blueprints
import «M2rGroup7».SixteenClassification.Classification
import «M2rGroup7».SmallGroupsLibrary

namespace OrderSixteen

/-- Every group of order 16 is isomorphic to `retrieve 16 i` for some valid index `i`. -/
theorem order_sixteen_retrieve
    {G : Type*} [Group G]
    (hn : Nat.card G = 16) :
    ∃ i : Nat, ∃ _ : ValidIndex 16 i, Nonempty (G ≃* retrieve 16 i) := by
  rcases order_sixteen_classification_normalized hn with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨1,  by decide, h⟩
  · exact ⟨2,  by decide, h⟩
  · exact ⟨3,  by decide, h⟩
  · exact ⟨4,  by decide, h⟩
  · exact ⟨5,  by decide, h⟩
  · exact ⟨6,  by decide, h⟩
  · exact ⟨7,  by decide, h⟩
  · exact ⟨8,  by decide, h⟩
  · exact ⟨9,  by decide, h⟩
  · exact ⟨10, by decide, h⟩
  · exact ⟨11, by decide, h⟩
  · exact ⟨12, by decide, h⟩
  · exact ⟨13, by decide, h⟩
  · exact ⟨14, by decide, h⟩

end OrderSixteen
