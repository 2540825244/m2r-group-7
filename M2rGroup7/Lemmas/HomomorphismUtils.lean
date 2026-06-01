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

/-- Transporting a non-trivial action along isomorphisms yields a non-trivial action.
    If `φ : K →* MulAut N` is non-trivial and `eN : N ≃* N'`, `eK : K ≃* K'`, then
    the conjugated action `(MulAut.congr eN) ∘ φ ∘ eK⁻¹` is also non-trivial. -/
lemma transported_action_ne_one
    {N N' K K' : Type*} [Group N] [Group N'] [Group K] [Group K']
    (eN : N ≃* N') (eK : K ≃* K')
    {φ : K →* MulAut N} (hφ : φ ≠ 1) :
    (MulAut.congr eN).toMonoidHom.comp (φ.comp eK.symm.toMonoidHom) ≠ 1 := by
  intro h_eq
  apply hφ
  refine MonoidHom.ext fun k => ?_
  have h1 : ((MulAut.congr eN).toMonoidHom.comp (φ.comp eK.symm.toMonoidHom)) (eK k) = 1 := by
    rw [h_eq]; simp
  have h2 : ((MulAut.congr eN).toMonoidHom.comp (φ.comp eK.symm.toMonoidHom)) (eK k) =
      (MulAut.congr eN) (φ k) := by simp [MulEquiv.symm_apply_apply]
  rw [h2] at h1
  exact (MulEquiv.map_eq_one_iff _).mp h1
