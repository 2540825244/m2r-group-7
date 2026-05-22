import Mathlib.Logic.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Equiv.Basic
import «M2rGroup7».SmallGroupsLibrary
import «M2rGroup7».PqCase
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Logic.Unique
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Fintype.Defs
import Mathlib.SetTheory.Cardinal.Defs
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.PNat.Prime
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.PGroup
import OrderPQ
import Mathlib.Algebra.Group.Defs
import Paperproof
import Mathlib.SetTheory.Cardinal.Finite

def maximumOrder : Nat := 9

variable (n : ℕ) (G : Type*) [Group G]

lemma isMulCommutative_iff {M : Type*} [Mul M] : IsMulCommutative M ↔ ∀ a b : M, a * b = b * a := by
  grind [IsMulCommutative, Std.Commutative]

theorem center_eq_top_iff : Subgroup.center G = ⊤ ↔ IsMulCommutative G := by
  simp [Subgroup.eq_top_iff', isMulCommutative_iff, Subgroup.mem_center_iff, eq_comm]

/-- An abelian group of order `p^3` is isomorphic to one of `CyclicGroup p^3`,
    `CyclicGroup p^2 × CyclicGroup p`, `CyclicGroup p × CyclicGroup p × CyclicGroup p`. -/
theorem prime_cubed_non_abelian_classification {p : ℕ} [hn : Fact p.Prime] (h_na : ¬IsMulCommutative G) (h : Nat.card G = p^3) :
  True := by
  -- Define Z as the center of G
  set Z := Subgroup.center G with hZ
  -- Claim 1: |Z(G)| = p and so Z(G) isomorphic to C_p
  -- Step 1: Z(G) subgroup of G implies |Z(G)| in {1, p, p^2, p^3}
  have h_z_order_divides_p_3 := by
    apply Subgroup.card_subgroup_dvd_card Z
  rw [h] at h_z_order_divides_p_3
  rw [dvd_prime_pow hn.out.prime] at h_z_order_divides_p_3
  obtain ⟨i, h'⟩ := h_z_order_divides_p_3
  obtain ⟨h_bound, h_z_order_p_i⟩ := h'

  -- Step 2: |Z(G)| ≠ 1 as centers of p-groups are non-trivial

  have : Finite G := by
    apply Nat.finite_of_card_ne_zero
    rw [h]
    have p_ne : p ≠ 0 := Nat.Prime.ne_zero hn.elim
    exact pow_ne_zero 3 p_ne

  have : Nontrivial G := by
    have p_3_gt_1 : p^3 > 1 := by
      have p_gt_1 : p > 1 := hn.out.one_lt
      exact one_lt_pow₀ p_gt_1 (by norm_num)
    have : Fintype G := Fintype.ofFinite G
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, h]
    exact p_3_gt_1

  have h_p_group : IsPGroup p G := by
    apply IsPGroup.of_card
    exact h

  have h_z_nontrivial : Nontrivial ↥Z := IsPGroup.center_nontrivial h_p_group
  have h_z_card_gt_one : 1 < Nat.card ↥Z := Finite.one_lt_card

  have h_i_ne_zero : i ≠ 0 := by
    intro hi0

    rw [hi0, pow_zero] at h_z_order_p_i
    obtain ⟨u, hu⟩ := h_z_order_p_i
    apply mul_eq_one.mp at hu
    obtain ⟨h_ord_one, _⟩ := hu
    omega

  -- Step 3: |Z(G)| ≠ p^3 as then Z(G) isomorphic to G which is iff G is abelian, contradiction

  have h_z_card_ne_p3 : Nat.card ↥Z ≠ (p^3) := by
    intro h_z_p3
    have h_z_eq_g : Z = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top, h_z_p3, h]
    have h_g_abelian : IsMulCommutative G := by
      rw [← center_eq_top_iff, ← hZ]
      exact h_z_eq_g
    exact absurd h_g_abelian h_na

  -- Step 4: |Z(G)| ≠ p^2 as then |G/Z(G)| = p and so it is cyclic so G is abelian, contradiction

  have h_z_card_ne_p2 : Nat.card ↥Z ≠ (p^2) := by
    intro h_z_p2

    have : Z.Normal := by
      rw [hZ]
      exact Subgroup.instNormalCenter

    have h_z_idx_p : Z.index = p := by
      have h_index_mul_card := Subgroup.index_mul_card Z
      rw [h_z_p2, h] at h_index_mul_card
      have h_p_ne_zero := hn.elim.ne_zero
      nlinarith

    have h_g_quot_z_p_card : Nat.card (G ⧸ Z) = p := by
      rw [← h_z_idx_p]
      apply Subgroup.index_eq_card

    have : IsCyclic (G ⧸ Z) := by
      exact isCyclic_of_prime_card h_g_quot_z_p_card

    have h_ker_subgroup_z : (QuotientGroup.mk' Z).ker ≤ Z := by
      rw [QuotientGroup.ker_mk' Z]

    -- have h_g_comm : CommGroup G := by
    --   exact commGroupOfCyclicCenterQuotient (QuotientGroup.mk' Z) (h_ker_subgroup_z)

    have h_comm := commutative_of_cyclic_center_quotient (QuotientGroup.mk' Z) (h_ker_subgroup_z)

    contrapose! h_na
    rw [isMulCommutative_iff]
    intro a
    intro b
    specialize h_comm a b
    exact h_comm

  have h_z_card_eq_p : Nat.card Z = p := by
    have h_card_eq : Nat.card ↥Z = p ^ i :=
      Nat.dvd_antisymm h_z_order_p_i.dvd h_z_order_p_i.symm.dvd
    have hne2 : i ≠ 2 := by
      intro h2; rw [h2] at h_card_eq; exact h_z_card_ne_p2 h_card_eq
    have hne3 : i ≠ 3 := by
      intro h3; rw [h3] at h_card_eq; exact h_z_card_ne_p3 h_card_eq
    have hi1 : i = 1 := by omega
    rw [h_card_eq, hi1, pow_one]


  -- Claim 2: G / Z is C_p x C_p

  -- Step 1: G / Z is order p^2

  have h_z_idx_p2 : Z.index = p^2 := by
    have h_index_mul_card := Subgroup.index_mul_card Z
    rw [h_z_card_eq_p, h] at h_index_mul_card
    have h_p_ne_zero := hn.elim.ne_zero
    nlinarith

  have h_g_quot_z_p_card : Nat.card (G ⧸ Z) = p^2 := by
    rw [← h_z_idx_p2]
    apply Subgroup.index_eq_card

  have h_g_quot_z_classify := p_squared_classification h_g_quot_z_p_card

  -- Step 2: G / Z cannot be cyclic because G is not abelian
  -- Step 3: Hence G / Z is C_p x C_p

  have h_g_quot_z_is_Cp_x_Cp : Nonempty (MulEquiv (G ⧸ Z) (CyclicGroup p × CyclicGroup p)) := by
    cases h_g_quot_z_classify with
      | inl h_g_quot_z_is_Cp2 =>
        -- Contradictive Case
        have h_g_quot_z_cyclic : IsCyclic (G ⧸ Z) := by
          let iso := Classical.choice h_g_quot_z_is_Cp2
          rw [MulEquiv.isCyclic iso]
          infer_instance

        sorry
      | inr hb =>
        exact hb

  -- Claim 3: [G, G] = Z(G)

  -- Step 1: Z(G) contains [G, G] as Z(G) is normal and G/N abelian iff N contains [G, G]

  -- Step 2: [G, G] is either trivial group or Z(G) but it is trivial iff G is abelian which is not true



  -- Claim 4: There exists a, b in G such that aZ, bZ non-identity in G/Z and generate G/Z

  -- Step 1: There exist aZ, bZ that generate G/Z as G/Z is C_p x C_p

  -- Step 2: As G -> G/Z is surjective, claim holds



  -- Claim 5: Z, a, b generate G

  -- Step 1: Let g in G, gZ is generated by aZ and bZ

  -- Step 2: g z_1 = <a, b> z_2

  -- Step 3: Hence g = <a, b> z_2 z_1^-1



  -- Claim 6: a, b do not commute

  -- Step 1: If a, b commute then centraliser C_G(a) contains Z, a, b

  -- Step 2: C_G(a) =* G

  -- Step 3: Hence a in Z but aZ is not identity in G/Z



  -- Claim 7: [a, b] is a non-identity element and generates Z

  -- Step 1: [a, b] non-identity because a, b do not commute

  -- Step 2: Z is C_p and so is generated by [a, b] as it is generated by any non-identity element



  -- Claim 8: a, b have order either p or p^2

  -- Step 1: a, b have order either 1, p, p^2, p^3

  -- Step 2: a, b not identity so not order 1

  -- Step 3: G is not abelian, so not cyclic, so a, b not order p^3



  -- Claim 9: a^p, b^p in Z

  -- Step 1: G/Z is C_p x C_p so for every element g, (gZ)^p = Z

  -- Step 2: a^p, b^p in Z

  sorry

theorem prime_cubed_and_abelian_classification {p : ℕ} [hn : Fact p.Prime] [IsMulCommutative G] (h : Nat.card G = p^3) :
  (Nonempty (MulEquiv G (CyclicGroup (p^3)))) ∨
  (Nonempty (MulEquiv G (CyclicGroup (p^2) × CyclicGroup p))) ∨
  (Nonempty (MulEquiv G (CyclicGroup p × CyclicGroup p × CyclicGroup p)))
  := by
  haveI hfin : Finite G := Nat.finite_of_card_ne_zero (h ▸ pow_ne_zero 3 hn.elim.ne_zero)
  -- Case 1: G is cyclic → G ≅ CyclicGroup (p³)
  by_cases hc : IsCyclic G
  · left
    haveI := hc
    exact ⟨mulEquivOfCyclicCardEq (h.trans (card_cyclicGroup _).symm)⟩
  -- G is not cyclic; split on whether G has an element of order p²
  · by_cases hexp2 : ∃ g : G, orderOf g = p ^ 2
    · -- Case 2: G has element of order p² → G ≅ C_{p²} × C_p
      right; left
      obtain ⟨g, hg⟩ := hexp2
      let H := Subgroup.closure (setOf (· = g))
      let G_H := G ⧸ H
      sorry

    · -- Case 3: no element of order ≥ p², so every element satisfies g^p = 1
      right; right
      -- Every element satisfies g^p = 1
      have hpow : ∀ g : G, g ^ p = 1 := by
        intro g
        have hdvd : orderOf g ∣ p ^ 3 := h ▸ orderOf_dvd_natCard g
        rw [Nat.dvd_prime_pow hn.out] at hdvd
        obtain ⟨k, hk3, hgk⟩ := hdvd
        -- k ≠ 3: else orderOf g = card G so G is cyclic, contradicting hc
        have hk3' : k ≠ 3 :=
          fun hk3e => hc (isCyclic_of_orderOf_eq_card g (hgk ▸ hk3e ▸ h.symm))
        -- k ≠ 2: contradicts hexp2
        have hk2' : k ≠ 2 := fun hk2e => hexp2 ⟨g, hgk ▸ hk2e ▸ rfl⟩
        -- so k ≤ 1, meaning orderOf g ∣ p
        have hk1 : k ≤ 1 := by omega
        have hk1' : p ^ k ∣ p ^ 1 := Nat.pow_dvd_pow p hk1
        rw [pow_one] at hk1'
        rw [← hgk] at hk1'
        exact orderOf_dvd_iff_pow_eq_one.mp hk1'
      -- Give Additive G a ZMod p-module structure
      haveI hnezerp : NeZero p := ⟨hn.elim.ne_zero⟩
      haveI hmod : Module (ZMod p) (Additive G) := AddCommGroup.zmodModule (n := p) fun a => by
        nth_rewrite 1 [← ofMul_toMul a]
        rw [← ofMul_pow, hpow (Additive.toMul a)]
        trivial
      haveI hfree : Module.Free (ZMod p) (Additive G) := Module.Free.of_divisionRing _ _
      haveI hfinmod : Module.Finite (ZMod p) (Additive G) := Module.Finite.of_finite
      -- finrank = 3 from p^finrank = Nat.card (Additive G) = p^3
      have hfinrank : Module.finrank (ZMod p) (Additive G) = 3 := by
        have hcardAG : Nat.card (Additive G) = p ^ 3 :=
          (Nat.card_congr Additive.toMul).trans h
        have hcard := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive G)
        rw [Nat.card_zmod, hcardAG] at hcard
        exact Nat.pow_right_injective hn.out.one_lt hcard.symm
      -- Get a Fin 3 basis and linear equivalence Additive G ≃ₗ[ZMod p] (Fin 3 → ZMod p)
      let e_lin := (Module.finBasisOfFinrankEq (ZMod p) (Additive G) hfinrank).equivFun
      -- Direct MulEquiv: G →* (Fin 3 → CyclicGroup p) via e_lin
      have e_mul : G ≃* (Fin 3 → CyclicGroup p) :=
        { toFun := fun g i => Multiplicative.ofAdd (e_lin (Additive.ofMul g) i)
          invFun := fun f => Additive.toMul (e_lin.symm (fun i => Multiplicative.toAdd (f i)))
          left_inv := fun g => by simp
          right_inv := fun f => by ext i; simp
          map_mul' := fun g1 g2 => by
            ext i
            simp only [ofMul_mul, LinearEquiv.map_add, Pi.add_apply, Pi.mul_apply,
              ← ofAdd_add, toAdd_ofAdd]
            trivial }
      have e_fin3 : (Fin 3 → CyclicGroup p) ≃* CyclicGroup p × CyclicGroup p × CyclicGroup p :=
        { toFun := fun f => (f 0, f 1, f 2)
          invFun := fun ⟨a, b, c⟩ => Fin.cons a (Fin.cons b (fun _ => c))
          left_inv := fun f => funext fun i => by
            fin_cases i <;>
              simp [Fin.cons_zero, Fin.cons_succ]
              <;> trivial
          right_inv := fun ⟨a, b, c⟩ => by
            simp [Fin.cons_zero, Fin.cons_succ]
            trivial
          map_mul' := fun f g => rfl }
      exact ⟨e_mul.trans e_fin3⟩


-- theorem alt_no_claude_prime_cubed_and_abelian_classification {p : ℕ} [hn : Fact p.Prime] [CommGroup G] (h : Nat.card G = p^3) :
--   (Nonempty (MulEquiv G (CyclicGroup (p^3)))) ∨
--   (Nonempty (MulEquiv G (CyclicGroup (p^2) × CyclicGroup p))) ∨
--   (Nonempty (MulEquiv G (CyclicGroup p × CyclicGroup p × CyclicGroup p)))
--   := by
--     have : Finite G := by
--       apply Nat.finite_of_card_ne_zero
--       rw [h]
--       have p_ne : p ≠ 0 := Nat.Prime.ne_zero hn.elim
--       exact pow_ne_zero 3 p_ne
--     have h_finite_cycles := CommGroup.equiv_prod_multiplicative_zmod_of_finite G

--     obtain ⟨IndexType, h_index_fin, order_func, h_cycles_nontrivial, h_prod⟩ := h_finite_cycles

--     by_contra h_not_iso

--     match h_index_n : Fintype.card IndexType with
--       | 0 =>
--         -- apply Fintype.card_eq_zero_iff.mp at h_index_n
--         have : Nat.card ((i : IndexType) → Multiplicative (ZMod (order_func i))) = 1 := by
--           sorry
--         --Not possible
--         sorry
--       | 1 =>
--         have : Nonempty (G ≃* CyclicGroup (p ^ 3)) := by
--           sorry
--         tauto
--       | 2 =>
--         have : Nonempty (G ≃* CyclicGroup (p ^ 2) × CyclicGroup p) := by
--           sorry
--         tauto
--       | 3 =>
--         have : Nonempty (G ≃* CyclicGroup p × CyclicGroup p × CyclicGroup p) := by
--           sorry
--         tauto
--       | k+3 =>
--         -- Not possible
--         sorry


/-- A group of prime order is isomorphic to the cyclic group of the same order. -/
theorem prime_classification [hn : Fact n.Prime] (h : Nat.card G = n) :
(Nonempty (MulEquiv G (CyclicGroup n))) := by
  apply Nonempty.intro
  have h_g_card : Nat.card G = n := h
  have : IsCyclic G := isCyclic_of_prime_card h_g_card
  refine (mulEquivOfCyclicCardEq ?_)
  have h_c_card: Nat.card (CyclicGroup n) = n := card_cyclicGroup n
  rw [h_g_card, h_c_card]

macro "classify_prime" p:num h:term : tactic => `(tactic|(
  have : Fact (Nat.Prime $p) := ⟨by decide⟩
  use 1
  have hr : MulEquiv (retrieve $p 1) (CyclicGroup $p) := by
    have hr_is_c : retrieve $p 1 = CyclicGroup $p := by rfl
    exact (MulEquiv.refl (CyclicGroup $p))
  apply prime_classification
  exact $h))

macro "classify_prime_sq" p:num h:term : tactic => `(tactic|(
  haveI : Fact (Nat.Prime $p) := ⟨by decide⟩
  obtain (hiso | hiso) := p_squared_classification (p := $p) ($h |>.trans (by decide))
  · exact ⟨1, hiso⟩
  · exact ⟨2, hiso⟩))

/-- A group of order at most `maximumOrder` is isomorphic to some group obtained by `retrieve`. -/
theorem classification [hp : Fact (n <= maximumOrder)] (h : Nat.card G = n) :
  (∃ i : Nat, Nonempty (MulEquiv G (retrieve n i)))
 :=
  match n with
  | 1 => by
    use 1
    apply Nonempty.intro

    have : Unique (retrieve 1 1) := by
      have hr : retrieve 1 1 = Unit := by rfl
      rw [hr]
      infer_instance

    have hg := Nat.card_eq_one_iff_unique.mp h
    have h_nonempty := hg.right
    have : Subsingleton G := hg.left
    have : Inhabited G := Classical.inhabited_of_nonempty h_nonempty
    have h_unique := Unique.mk' G

    exact MulEquiv.ofUnique

  | 2 => by
    classify_prime 2 h

  | 3 => by
    classify_prime 3 h

  | 4 => by classify_prime_sq 2 h

  | 5 => by
    classify_prime 5 h

  | 6 => by
    obtain (hiso | hiso) := order6_classification h
    · exact ⟨2, hiso⟩
    · exact ⟨1, hiso⟩

  | 7 => by
    classify_prime 7 h

  | 8 => by
    sorry

  | 9 => by classify_prime_sq 3 h

  | 10 => by
    sorry

  | 11 => by
    classify_prime 11 h

  | _ => by
    have hn := n > maximumOrder
    sorry
