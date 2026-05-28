import Mathlib
import «M2rGroup7».Lemmas.NumberTheoryUtils

/-- A homomorphism with trivial range is itself trivial. -/
lemma eq_one_of_range_card_one {G H : Type*} [Group G] [Group H]
    {f : G →* H} (h : Nat.card f.range = 1) : f = 1 := by
  have hbot : f.range = ⊥ := by rwa [Subgroup.eq_bot_iff_card]
  ext g
  have hg : f g ∈ f.range := MonoidHom.mem_range.mpr ⟨g, rfl⟩
  rwa [hbot, Subgroup.mem_bot] at hg

/-- If the domain and codomain have coprime cardinalities, the homomorphism is trivial. -/
lemma eq_one_of_coprime_card {G H : Type*} [Group G] [Group H]
    {φ : G →* H} (hcop : Nat.Coprime (Nat.card G) (Nat.card H)) : φ = 1 := by
  apply eq_one_of_range_card_one
  have h1 : Nat.card φ.range ∣ Nat.card G := Subgroup.card_range_dvd φ
  have h2 : Nat.card φ.range ∣ Nat.card H := Subgroup.card_subgroup_dvd_card φ.range
  have h := Nat.dvd_gcd h1 h2
  rwa [hcop, Nat.dvd_one] at h
