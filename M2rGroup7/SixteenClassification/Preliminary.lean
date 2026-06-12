import «M2rGroup7».SmallGroupsLibrary
import «M2rGroup7».PqCase
import «M2rGroup7».SixteenClassification.Blueprints
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Group.Equiv.Finite
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.Rank

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
      have : y * x * y⁻¹ = x := by rw [← h_comm x hx y hy]; group
      rwa [this]
    · intro hyx
      have heq : y * x * y⁻¹ = x :=
        mul_right_cancel ((h_comm (y * x * y⁻¹) hyx y⁻¹ (H₂.inv_mem hy)).trans (by group))
      exact heq ▸ hyx
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
    ∃ n : ℕ, Nonempty (G ≃* (Fin n → CyclicGroup 2)) := by
  letI hcomm : IsMulCommutative G := isMulCommutative_of_sq_eq_one h
  letI : CommGroup G := CommGroup.ofIsMulCommutative
  obtain ⟨ι, instι, nf, hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  -- All nf i = 2, since the group exponent divides 2 and nf i > 1
  have hn2 : ∀ i : ι, nf i = 2 := fun i => by
    have hexpG : Monoid.exponent G ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one h
    have hdvd_i : Monoid.exponent (Multiplicative (ZMod (nf i))) ∣
        Monoid.exponent ((j : ι) → Multiplicative (ZMod (nf j))) :=
      MonoidHom.exponent_dvd (f := Pi.evalMonoidHom _ i) (Function.surjective_eval i)
    have hdvd2 : nf i ∣ 2 := by
      rw [show Monoid.exponent (Multiplicative (ZMod (nf i))) =
          AddMonoid.exponent (ZMod (nf i)) from rfl, ZMod.exponent] at hdvd_i
      exact hdvd_i.trans ((Monoid.exponent_eq_of_mulEquiv e) ▸ hexpG)
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdvd2 with h1 | h2
    · exact absurd (hn i) (by omega)
    · exact h2
  refine ⟨Fintype.card ι, ⟨e.trans ?_⟩⟩
  refine (MulEquiv.piCongrRight (fun i => ?_)).trans
    (MulEquiv.arrowCongr (Fintype.equivFin ι) (MulEquiv.refl _))
  rw [hn2 i]; exact MulEquiv.refl _

/-- Wild's Fact 3: `Aut(C₄) ≃ C₂`. -/
noncomputable def autC4Equiv : MulAut (CyclicGroup 4) ≃* CyclicGroup 2 := by
  haveI : IsCyclic (ZMod 4)ˣ := ZMod.isCyclic_units_four
  have hcard : Nat.card (ZMod 4)ˣ = Nat.card (CyclicGroup 2) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, card_cyclicGroup]
    decide
  have e₁ : MulAut (CyclicGroup 4) ≃* (ZMod 4)ˣ := by
    have := IsCyclic.mulAutMulEquiv (CyclicGroup 4)
    rwa [card_cyclicGroup] at this
  exact e₁.trans (mulEquivOfCyclicCardEq hcard)

lemma aut_C4_iso_C2 : Nonempty (MulAut (CyclicGroup 4) ≃* CyclicGroup 2) := ⟨autC4Equiv⟩

/-- Wild's Fact 3: `Aut(C₈) ≃ C₂ × C₂`. -/
noncomputable def autC8Equiv : MulAut (CyclicGroup 8) ≃* CyclicGroup 2 × CyclicGroup 2 := by
  haveI h8K : IsKleinFour (ZMod 8)ˣ := by
    apply IsKleinFour.mk
    · rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]; decide
    · have hdvd : Monoid.exponent (ZMod 8)ˣ ∣ 2 :=
        Monoid.exponent_dvd_of_forall_pow_eq_one (by decide)
      have hpos : 0 < Monoid.exponent (ZMod 8)ˣ :=
        Monoid.exponent_pos_of_exists 2 two_pos (by decide)
      have hne1 : Monoid.exponent (ZMod 8)ˣ ≠ 1 := by
        intro h1
        rw [Monoid.exp_eq_one_iff] at h1
        haveI := h1
        exact absurd (@Nat.card_unique (ZMod 8)ˣ ⟨1⟩ ‹_›)
          (by simp only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]; decide)
      have := Nat.le_of_dvd two_pos hdvd; omega
  have hexp2 : Monoid.exponent (CyclicGroup 2) = 2 := ZMod.exponent 2
  haveI hC2K : IsKleinFour (CyclicGroup 2 × CyclicGroup 2) := by
    apply IsKleinFour.mk
    · simp only [Nat.card_prod, card_cyclicGroup]
    · rw [Monoid.exponent_prod, hexp2]; decide
  have e₁ : MulAut (CyclicGroup 8) ≃* (ZMod 8)ˣ := by
    have := IsCyclic.mulAutMulEquiv (CyclicGroup 8)
    rwa [card_cyclicGroup] at this
  exact e₁.trans IsKleinFour.nonempty_mulEquiv.some

lemma aut_C8_iso_C2_prod_C2 :
    Nonempty (MulAut (CyclicGroup 8) ≃* CyclicGroup 2 × CyclicGroup 2) := ⟨autC8Equiv⟩

/-- The order-4 generator `(g₄, 1)` of `K₈ = C₄ × C₂`. -/
def k8GenA : CyclicGroup 4 × CyclicGroup 2 := (Multiplicative.ofAdd 1, 1)

/-- The order-2 generator `(1, g₂)` of `K₈ = C₄ × C₂`. -/
def k8GenB : CyclicGroup 4 × CyclicGroup 2 := (1, Multiplicative.ofAdd 1)

/-- The order-4 automorphism of `K₈`: `(x, y) ↦ (x · c4Half^y, ofAdd((x mod 2) + y))`. -/
def rhoAutK8 : MulAut (CyclicGroup 4 × CyclicGroup 2) where
  toFun p := ⟨p.1 * c4Half ^ (Multiplicative.toAdd p.2).val,
    Multiplicative.ofAdd (((Multiplicative.toAdd p.1).val : ZMod 2) + Multiplicative.toAdd p.2)⟩
  invFun p := ⟨p.1⁻¹ * c4Half ^ (Multiplicative.toAdd p.2).val,
    Multiplicative.ofAdd (((Multiplicative.toAdd p.1).val : ZMod 2) + Multiplicative.toAdd p.2)⟩
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

/-- The order-2 automorphism of `K₈`: `(x, y) ↦ (x, ofAdd((x mod 2) + y))`. -/
def sigmaAutK8 : MulAut (CyclicGroup 4 × CyclicGroup 2) where
  toFun p := ⟨p.1,
    Multiplicative.ofAdd (((Multiplicative.toAdd p.1).val : ZMod 2) + Multiplicative.toAdd p.2)⟩
  invFun p := ⟨p.1,
    Multiplicative.ofAdd (((Multiplicative.toAdd p.1).val : ZMod 2) + Multiplicative.toAdd p.2)⟩
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

/-- The explicit homomorphism `f : D₄ → Aut(K₈)` sending the rotation `r i ↦ rhoAutK8^i` and the
reflection `sr i ↦ sigmaAutK8 · rhoAutK8^i`. It is the inverse iso of `autK8Equiv`. -/
def k8AutHom : DihedralGroup 4 →* MulAut (CyclicGroup 4 × CyclicGroup 2) where
  toFun d := match d with
    | DihedralGroup.r i => rhoAutK8 ^ i.val
    | DihedralGroup.sr i => sigmaAutK8 * rhoAutK8 ^ i.val
  map_one' := by decide
  map_mul' := by decide

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
-- Injectivity is an 8-case `decide` via `injective_iff_map_eq_one`; it does not enumerate `MulAut`,
-- but the kernel computation needs a raised heartbeat budget.
/-- `k8AutHom` is injective. -/
theorem k8AutHom_injective : Function.Injective k8AutHom := by
  rw [injective_iff_map_eq_one]; decide

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
-- An automorphism is determined by its values on the two generators `k8GenA`, `k8GenB`; every
-- valid (decidably constrained) pair of generator images is hit by some `k8AutHom d`. This avoids
-- enumerating all of `Aut(K₈)` (which only `native_decide` could do within budget) and needs a
-- raised heartbeat budget.
/-- `k8AutHom` is surjective. -/
theorem k8AutHom_surjective : Function.Surjective k8AutHom := by
  -- two automorphisms agreeing on the generators are equal
  have hdet : ∀ φ ψ : MulAut (CyclicGroup 4 × CyclicGroup 2),
      φ k8GenA = ψ k8GenA → φ k8GenB = ψ k8GenB → φ = ψ := by
    intro φ ψ ha hb
    apply MulEquiv.ext; intro x
    obtain ⟨i, j, hx⟩ : ∃ i j : ℕ, x = k8GenA ^ i * k8GenB ^ j :=
      ⟨(Multiplicative.toAdd x.1).val, (Multiplicative.toAdd x.2).val, by revert x; decide⟩
    rw [hx]; simp only [map_mul, map_pow, ha, hb]
  intro φ
  set u := φ k8GenA with hu
  set v := φ k8GenB with hv
  have c1 : u ^ 4 = 1 := by rw [hu, ← map_pow]; rw [show k8GenA ^ 4 = 1 from by decide, map_one]
  have c2 : v ^ 2 = 1 := by rw [hv, ← map_pow]; rw [show k8GenB ^ 2 = 1 from by decide, map_one]
  have c3 : u ^ 2 ≠ 1 := by
    rw [hu, ← map_pow]; intro h
    exact (by decide : k8GenA ^ 2 ≠ 1) ((map_eq_one_iff φ φ.injective).mp h)
  have c4 : v ≠ 1 := by
    rw [hv]; intro h; exact (by decide : k8GenB ≠ 1) ((map_eq_one_iff φ φ.injective).mp h)
  have c5 : u * v = v * u := by
    rw [hu, hv, ← map_mul, ← map_mul, show k8GenA * k8GenB = k8GenB * k8GenA from by decide]
  have c6 : v ≠ u := by rw [hu, hv]; intro h; exact (by decide : k8GenB ≠ k8GenA) (φ.injective h)
  have c7 : v ≠ u ^ 2 := by
    rw [hu, hv, ← map_pow]; intro h; exact (by decide : k8GenB ≠ k8GenA ^ 2) (φ.injective h)
  have c8 : v ≠ u ^ 3 := by
    rw [hu, hv, ← map_pow]; intro h; exact (by decide : k8GenB ≠ k8GenA ^ 3) (φ.injective h)
  have key : ∀ u v : CyclicGroup 4 × CyclicGroup 2,
      u ^ 4 = 1 → v ^ 2 = 1 → u ^ 2 ≠ 1 → v ≠ 1 → u * v = v * u →
      v ≠ u → v ≠ u ^ 2 → v ≠ u ^ 3 →
      ∃ d : DihedralGroup 4, k8AutHom d k8GenA = u ∧ k8AutHom d k8GenB = v := by decide
  obtain ⟨d, hda, hdb⟩ := key u v c1 c2 c3 c4 c5 c6 c7 c8
  exact ⟨d, hdet (k8AutHom d) φ hda hdb⟩

/-- Wild's Fact 4: `Aut(K₈) ≃ D₈`, where `K₈ = C₄ × C₂`.

The explicit homomorphism `k8AutHom : D₄ → Aut(K₈)` is a bijection (`k8AutHom_injective`,
`k8AutHom_surjective`), hence an isomorphism. -/
noncomputable def autK8Equiv : MulAut (CyclicGroup 4 × CyclicGroup 2) ≃* DihedralGroup 4 :=
  (MulEquiv.ofBijective k8AutHom ⟨k8AutHom_injective, k8AutHom_surjective⟩).symm

lemma aut_C4_prod_C2_iso_D8 :
    Nonempty (MulAut (CyclicGroup 4 × CyclicGroup 2) ≃* DihedralGroup 4) := ⟨autK8Equiv⟩

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

/-- Every automorphism of `C₄` is either the identity or the inverse map. -/
lemma MulAut.forall_eq_C4 (τ : MulAut (CyclicGroup 4)) :
    τ = 1 ∨ τ = c4OnC4Inv (Multiplicative.ofAdd 1) := by
  revert τ; decide

/-- The canonical generator `ofAdd 1` generates `CyclicGroup n`: every `x` is one of its powers. -/
private lemma cyclicGroup_eq_gen_pow {n : ℕ} [NeZero n] (x : CyclicGroup n) :
    x = (Multiplicative.ofAdd (1 : ZMod n)) ^ ((Multiplicative.toAdd x).val : ℕ) := by
  rw [← Multiplicative.ofAdd.apply_symm_apply x]
  change Multiplicative.ofAdd (Multiplicative.toAdd x)
      = Multiplicative.ofAdd (1 : ZMod n) ^ ((Multiplicative.toAdd x).val : ℕ)
  rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one]
  congr 1
  exact (ZMod.natCast_zmod_val _).symm

/-- If an automorphism `τ` of `CyclicGroup 8` sends the generator to `g^k`, then `τ x = x^k`. -/
private lemma autC8_eq_pow_of_gen {k : ℕ} (τ : MulAut (CyclicGroup 8))
    (hk : τ (Multiplicative.ofAdd 1) = (Multiplicative.ofAdd (1 : ZMod 8)) ^ k)
    (x : CyclicGroup 8) :
    τ x = x ^ k := by
  have step1 : τ x = (τ (Multiplicative.ofAdd 1)) ^ ((Multiplicative.toAdd x).val) := by
    conv_lhs => rw [cyclicGroup_eq_gen_pow x]
    exact map_pow τ _ _
  rw [step1, hk]
  conv_rhs => rw [cyclicGroup_eq_gen_pow x]
  exact pow_right_comm _ _ _

private lemma c2OnC8Pow3_apply (x : CyclicGroup 8) :
    c2OnC8Pow3 (Multiplicative.ofAdd 1) x = x ^ 3 := by
  unfold c2OnC8Pow3
  rw [cyclicHom_apply_eq_zpow]
  have hval : ((Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))).val : ℤ) = 1 := by decide
  rw [hval, zpow_one]; rfl

private lemma c2OnC8Pow5_apply (x : CyclicGroup 8) :
    c2OnC8Pow5 (Multiplicative.ofAdd 1) x = x ^ 5 := by
  unfold c2OnC8Pow5
  rw [cyclicHom_apply_eq_zpow]
  have hval : ((Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))).val : ℤ) = 1 := by decide
  rw [hval, zpow_one]; rfl

private lemma c2OnC8Pow7_apply (x : CyclicGroup 8) :
    c2OnC8Pow7 (Multiplicative.ofAdd 1) x = x ^ 7 := by
  unfold c2OnC8Pow7
  rw [cyclicHom_apply_eq_zpow]
  have hval : ((Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))).val : ℤ) = 1 := by decide
  rw [hval, zpow_one]; rfl

/-- Every automorphism of `C₈` is one of the four explicit maps `x ↦ xᵏ` for `k ∈ {1,3,5,7}`. -/
lemma MulAut.forall_eq_C8 (τ : MulAut (CyclicGroup 8)) :
    τ = 1 ∨
    τ = c2OnC8Pow3 (Multiplicative.ofAdd 1) ∨
    τ = c2OnC8Pow5 (Multiplicative.ofAdd 1) ∨
    τ = c2OnC8Pow7 (Multiplicative.ofAdd 1) := by
  set g : CyclicGroup 8 := Multiplicative.ofAdd 1 with hg
  -- τ g has order 8 = orderOf g, so it is `g^m` for an m coprime to 8
  have hord : orderOf (τ g) = 8 := by
    rw [MulEquiv.orderOf_eq]
    change orderOf (Multiplicative.ofAdd (1 : ZMod 8)) = 8
    rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  -- Write τ g = ofAdd m
  obtain ⟨m, hm⟩ : ∃ m : ZMod 8, τ g = Multiplicative.ofAdd m :=
    ⟨Multiplicative.toAdd (τ g), rfl⟩
  have hmord : addOrderOf m = 8 := by
    rw [← orderOf_ofAdd_eq_addOrderOf, ← hm]; exact hord
  -- The only m with addOrderOf m = 8 in ZMod 8 are 1, 3, 5, 7
  have hcases : m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 7 := by
    -- `addOrderOf m = 8` forces `4 • m ≠ 0`, a decidable condition characterising the odd residues
    have h4 : (4 : ℕ) • m ≠ 0 := by
      intro hc
      have hdvd : addOrderOf m ∣ 4 := addOrderOf_dvd_of_nsmul_eq_zero hc
      rw [hmord] at hdvd; omega
    have key : ∀ m : ZMod 8, (4 : ℕ) • m ≠ 0 → m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 7 := by decide
    exact key m h4
  -- In each case express τ g as g^k and apply autC8_eq_pow_of_gen
  rcases hcases with h | h | h | h
  · left
    ext x
    have : τ x = x ^ 1 := autC8_eq_pow_of_gen τ (by rw [hm, h]; norm_num) x
    rw [this, pow_one]; rfl
  · right; left
    ext x
    have hτ : τ x = x ^ 3 := autC8_eq_pow_of_gen τ (by rw [hm, h]; rfl) x
    rw [hτ, c2OnC8Pow3_apply]
  · right; right; left
    ext x
    have hτ : τ x = x ^ 5 := autC8_eq_pow_of_gen τ (by rw [hm, h]; rfl) x
    rw [hτ, c2OnC8Pow5_apply]
  · right; right; right
    ext x
    have hτ : τ x = x ^ 7 := autC8_eq_pow_of_gen τ (by rw [hm, h]; rfl) x
    rw [hτ, c2OnC8Pow7_apply]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
-- Transport `τ` along the bijection `k8AutHom : D₄ ≃ Aut(K₈)` to a `d : D₄` with `d² = 1`, then
-- classify the involutions of `D₄` up to conjugacy by a `decide` over `D₄ × D₄` (8×8 cases),
-- mapping conjugacy reps back to `1, ψ₃, ψ₅, ψ₆`. This avoids enumerating `Aut(K₈)` directly
-- (which only `native_decide` could) and needs a raised heartbeat budget.
/-- Every involution in `Aut(K₈)` is conjugate to one of the four representatives
    `1, ψ₃, ψ₅, ψ₆`. -/
lemma MulAut.involution_K8_conj_to_rep
    (τ : MulAut (CyclicGroup 4 × CyclicGroup 2)) (hτ : τ ^ 2 = 1) :
    ∃ σ : MulAut (CyclicGroup 4 × CyclicGroup 2),
      σ * τ * σ⁻¹ = 1 ∨
      σ * τ * σ⁻¹ = psi3 ∨
      σ * τ * σ⁻¹ = psi5 ∨
      σ * τ * σ⁻¹ = psi6 := by
  obtain ⟨d, rfl⟩ := k8AutHom_surjective τ
  have hd2 : d ^ 2 = 1 := k8AutHom_injective (by rw [map_pow, hτ, map_one])
  -- conjugacy classification of involutions in D₄, with reps pulled back to 1/ψ₃/ψ₅/ψ₆
  have core : ∀ d : DihedralGroup 4, d ^ 2 = 1 →
      ∃ c : DihedralGroup 4,
        k8AutHom (c * d * c⁻¹) = 1 ∨ k8AutHom (c * d * c⁻¹) = psi3 ∨
        k8AutHom (c * d * c⁻¹) = psi5 ∨ k8AutHom (c * d * c⁻¹) = psi6 := by decide
  obtain ⟨c, hc⟩ := core d hd2
  refine ⟨k8AutHom c, ?_⟩
  rwa [show k8AutHom c * k8AutHom d * (k8AutHom c)⁻¹ = k8AutHom (c * d * c⁻¹) from by
    rw [map_mul, map_mul, map_inv]]

end Preliminary

end OrderSixteen
