import «M2rGroup7».SmallGroupsLibrary
import «M2rGroup7».PqCase
import Mathlib

namespace OrderSixteen

section Preliminary

/-- Wild's Fact 1: If `H₁ ⊓ H₂ = ⊥` and elements of `H₁` commute with elements of `H₂`,
    the multiplication map `H₁ × H₂ → H₁ ⊔ H₂` is a group isomorphism.
    Proved via `Subgroup.coe_mul_of_right_le_normalizer_left`. -/
noncomputable def mulEquiv_sup_of_disjoint_comm
    {G : Type*} [Group G] (H₁ H₂ : Subgroup G)
    (h_disj : H₁ ⊓ H₂ = ⊥)
    (h_comm : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x) :
    (H₁ × H₂) ≃* ↑(H₁ ⊔ H₂) := by
  -- H₂ normalises H₁: commutativity forces conjugation y * x * y⁻¹ = x
  have hH₂_norm : H₂ ≤ Subgroup.normalizer H₁ := fun y hy => by
    rw [Subgroup.mem_normalizer_iff]; intro x; constructor
    · intro hx
      have : y * x * y⁻¹ = x :=
        calc y * x * y⁻¹ = x * y * y⁻¹ := by rw [← h_comm x hx y hy]
          _ = x := by group
      rwa [this]
    · intro hyx
      have comm_z : y * x * y⁻¹ * y⁻¹ = y⁻¹ * (y * x * y⁻¹) :=
        h_comm (y * x * y⁻¹) hyx y⁻¹ (H₂.inv_mem hy)
      have hxz : x = y * x * y⁻¹ :=
        calc x = y⁻¹ * (y * x * y⁻¹) * y := by group
          _ = y * x * y⁻¹ * y⁻¹ * y := by rw [← comm_z]
          _ = y * x * y⁻¹ := by group
      rwa [hxz]
  let φ : H₁ × H₂ →* ↑(H₁ ⊔ H₂) :=
    { toFun := fun p => ⟨↑p.1 * ↑p.2,
        (H₁ ⊔ H₂).mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        simp only [Prod.mul_def, Subgroup.coe_mul]
        calc (↑a.1 : G) * ↑b.1 * (↑a.2 * ↑b.2)
            = ↑a.1 * (↑b.1 * ↑a.2) * ↑b.2 := by group
          _ = ↑a.1 * (↑a.2 * ↑b.1) * ↑b.2 := by rw [h_comm ↑b.1 b.1.2 ↑a.2 a.2.2]
          _ = ↑a.1 * ↑a.2 * (↑b.1 * ↑b.2) := by group) }
  refine MulEquiv.ofBijective φ ⟨?_, ?_⟩
  · intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ hab
    have hab' : (↑a₁ : G) * ↑a₂ = ↑b₁ * ↑b₂ := Subtype.ext_iff.mp hab
    have key : (↑a₁ : G)⁻¹ * ↑b₁ ∈ H₁ ⊓ H₂ := Subgroup.mem_inf.mpr ⟨
      H₁.mul_mem (H₁.inv_mem a₁.2) b₁.2,
      show (↑a₁ : G)⁻¹ * ↑b₁ ∈ H₂ from by
        have heq : (↑a₁ : G)⁻¹ * ↑b₁ = ↑a₂ * (↑b₂ : G)⁻¹ :=
          calc (↑a₁ : G)⁻¹ * ↑b₁
              = (↑a₁ : G)⁻¹ * (↑b₁ * ↑b₂) * (↑b₂ : G)⁻¹ := by group
            _ = (↑a₁ : G)⁻¹ * (↑a₁ * ↑a₂) * (↑b₂ : G)⁻¹ := by rw [← hab']
            _ = ↑a₂ * (↑b₂ : G)⁻¹ := by group
        rw [heq]; exact H₂.mul_mem a₂.2 (H₂.inv_mem b₂.2)⟩
    rw [h_disj] at key
    have hval₁ : (↑a₁ : G) = ↑b₁ := inv_mul_eq_one.mp (Subgroup.mem_bot.mp key)
    have hval₂ : (↑a₂ : G) = ↑b₂ :=
      calc (↑a₂ : G) = (↑a₁ : G)⁻¹ * (↑a₁ * ↑a₂) := by group
        _ = (↑a₁ : G)⁻¹ * (↑b₁ * ↑b₂) := by rw [hab']
        _ = ↑b₂ := by rw [← hval₁]; group
    exact Prod.ext (Subtype.ext hval₁) (Subtype.ext hval₂)
  · open scoped Pointwise in
    intro ⟨g, hg⟩
    have hg' : g ∈ (H₁ : Set G) * H₂ := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left H₁ H₂ hH₂_norm]
      exact SetLike.mem_coe.mpr hg
    obtain ⟨h₁, h₁_mem, h₂, h₂_mem, heq⟩ := Set.mem_mul.mp hg'
    exact ⟨⟨⟨h₁, h₁_mem⟩, ⟨h₂, h₂_mem⟩⟩, Subtype.ext heq⟩

/-- Wild's Fact 2, first part: If every element of `G` squares to 1, then `G` is abelian.
    Follows from `Commute.of_orderOf_dvd_two`. -/
lemma isMulCommutative_of_sq_eq_one {G : Type*} [Group G] (h : ∀ x : G, x ^ 2 = 1) :
    IsMulCommutative G where
  is_comm := ⟨fun a b =>
    (Commute.of_orderOf_dvd_two (fun x => orderOf_dvd_of_pow_eq_one (h x)) a b).eq⟩

/-- Wild's Fact 2, second part: If every element of `G` squares to 1 and `G` is finite,
    then `G ≃ Fin n → C₂` for some `n`. -/
lemma mulEquiv_pi_cyclicTwo_of_sq_eq_one {G : Type*} [Group G] [Finite G]
    (h : ∀ x : G, x ^ 2 = 1) :
    ∃ n : ℕ, Nonempty (G ≃* (Fin n → CyclicGroup 2)) := sorry

/-- Wild's Fact 3: `Aut(C₄) ≃ C₂`. -/
lemma aut_C4_iso_C2 : Nonempty (MulAut (CyclicGroup 4) ≃* CyclicGroup 2) := sorry

/-- Wild's Fact 3: `Aut(C₈) ≃ C₂ × C₂`. -/
lemma aut_C8_iso_C2_prod_C2 :
    Nonempty (MulAut (CyclicGroup 8) ≃* CyclicGroup 2 × CyclicGroup 2) := sorry

/-- Wild's Fact 4: `Aut(K₈) ≃ D₈`, where `K₈ = C₄ × C₂`. -/
lemma aut_C4_prod_C2_iso_D8 :
    Nonempty (MulAut (CyclicGroup 4 × CyclicGroup 2) ≃* DihedralGroup 4) := sorry

/-- Wild's Fact 5: For any element `v` in a finite group `G`,
    `|class(v)| · |C(v)| = |G|` (orbit-stabilizer for conjugation).
    Follows from `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`. -/
lemma card_conj_orbit_mul_card_centralizer {G : Type*} [Group G] [Finite G] (v : G) :
    Nat.card (MulAction.orbit (ConjAct G) (ConjAct.toConjAct v)) *
    Nat.card (MulAction.stabilizer (ConjAct G) (ConjAct.toConjAct v)) =
    Nat.card G := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  simp only [Nat.card_eq_fintype_card]
  exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) (ConjAct.toConjAct v)

/-- Wild's Fact 6: If `|G| = pⁿ` with `n > 0` for a prime `p`, then `p ∣ |Z(G)|`.
    Follows from `IsPGroup.card_center_eq_prime_pow`. -/
lemma prime_dvd_card_center {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : Nat.Prime p) {n : ℕ} (hn : Nat.card G = p ^ n) (hn_pos : 0 < n) :
    p ∣ Nat.card (Subgroup.center G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsPGroup p G := IsPGroup.of_card hn
  obtain ⟨k, hk_pos, hk⟩ := IsPGroup.card_center_eq_prime_pow hn hn_pos
  exact hk ▸ dvd_pow_self p hk_pos.ne'

end Preliminary

end OrderSixteen
