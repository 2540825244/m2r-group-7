import Mathlib.Logic.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Equiv.Basic
import «M2rGroup7».CpSqAction
import «M2rGroup7».SmallGroupsLibrary
import «M2rGroup7».PqCase
import «M2rGroup7».P2qClassification.P2qClassification
import «M2rGroup7».P2qClassification.PqClassification
import «M2rGroup7».UT3
import «M2rGroup7».CaseA
import «M2rGroup7».CaseB
import «M2rGroup7».CaseC
import «M2rGroup7».OddCaseA
import «M2rGroup7».OddCaseB
import «M2rGroup7».OddCaseC
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

import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Data.Bracket
import Mathlib.Algebra.Group.TypeTags.Basic
import Paperproof
import Mathlib.SetTheory.Cardinal.Finite

open scoped commutatorElement

lemma AddSubgroup.closure_singleton_int_one_eq_top : closure ({1} : Set ℤ) = ⊤ := by
  ext
  simp only [Int.addSubgroupClosure_one, mem_top]

variable (n : ℕ) (G : Type*) [Group G]

lemma isMulCommutative_of_commGroup {M : Type*} [CommGroup M] : IsMulCommutative M :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

lemma isMulCommutative_iff {M : Type*} [Mul M] :
    IsMulCommutative M ↔ ∀ a b : M, a * b = b * a := by
  grind [IsMulCommutative, Std.Commutative]

lemma isMulCommutative_of_mulEquiv {M N : Type*} [Group M] [Group N]
    (e : M ≃* N) (h : IsMulCommutative N) : IsMulCommutative M := by
  exact ⟨⟨fun x y => e.injective (by rw [e.map_mul, e.map_mul]; exact h.is_comm.comm (e x) (e y))⟩⟩

theorem center_eq_top_iff : Subgroup.center G = ⊤ ↔ IsMulCommutative G := by
  simp [Subgroup.eq_top_iff', isMulCommutative_iff, Subgroup.mem_center_iff, eq_comm]

theorem prime_cubed_non_abelian_classification {p : ℕ} [hn : Fact p.Prime]
  (h_na : ¬IsMulCommutative G) (h : Nat.card G = p ^ 3) :
  (p = 2 ∧ ((Nonempty (MulEquiv G (DihedralGroup 4))) ∨
             (Nonempty (MulEquiv G (QuaternionGroup 2))))) ∨
  (p ≠ 2 ∧ ((Nonempty (MulEquiv G (UT3 p))) ∨
             (Nonempty (MulEquiv G (CyclicGroup (p^2) ⋊[cpSqAction p] CyclicGroup p))))) := by

  set Z := Subgroup.center G with hZ

  -- Claim 1: |Z(G)| = p and so Z(G) isomorphic to C_p

  have h_z_order_divides_p_3 := by
    apply Subgroup.card_subgroup_dvd_card Z

  rw [h] at h_z_order_divides_p_3
  rw [dvd_prime_pow hn.out.prime] at h_z_order_divides_p_3
  obtain ⟨i, h'⟩ := h_z_order_divides_p_3
  obtain ⟨h_bound, h_z_order_p_i⟩ := h'

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

  have h_z_card_ne_p3 : Nat.card ↥Z ≠ (p^3) := by
    intro h_z_p3
    have h_z_eq_g : Z = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top, h_z_p3, h]
    have h_g_abelian : IsMulCommutative G := by
      rw [← center_eq_top_iff, ← hZ]
      exact h_z_eq_g
    exact absurd h_g_abelian h_na

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
    have h_comm := commutative_of_cyclic_center_quotient (QuotientGroup.mk' Z) (h_ker_subgroup_z)
    contrapose! h_na
    rw [isMulCommutative_iff]
    intro a b
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

  have h_z_idx_p2 : Z.index = p^2 := by
    have h_index_mul_card := Subgroup.index_mul_card Z
    rw [h_z_card_eq_p, h] at h_index_mul_card
    have h_p_ne_zero := hn.elim.ne_zero
    nlinarith

  have h_g_quot_z_p_card : Nat.card (G ⧸ Z) = p^2 := by
    rw [← h_z_idx_p2]
    apply Subgroup.index_eq_card

  have h_g_quot_z_classify := p_squared_classification h_g_quot_z_p_card

  have h_g_quot_z_is_Cp_x_Cp : Nonempty (MulEquiv (G ⧸ Z) (CyclicGroup p × CyclicGroup p)) := by
    cases h_g_quot_z_classify with
      | inl h_g_quot_z_is_Cp2 =>
        -- Contradictive Case
        have h_g_quot_z_cyclic : IsCyclic (G ⧸ Z) := by
          let iso := Classical.choice h_g_quot_z_is_Cp2
          rw [MulEquiv.isCyclic iso]
          infer_instance
        exfalso
        apply h_na
        have h_ker_subgroup_z : (QuotientGroup.mk' Z).ker ≤ Z := by
          rw [QuotientGroup.ker_mk' Z]
        have h_comm := commutative_of_cyclic_center_quotient (QuotientGroup.mk' Z) h_ker_subgroup_z
        rw [isMulCommutative_iff]
        intro a b
        exact h_comm a b
      | inr hb =>
        exact hb

  -- Claim 3: [G, G] = Z(G)

  have h_quotient_z_abelian : IsMulCommutative (G ⧸ Z) := by
    obtain ⟨e⟩ := h_g_quot_z_is_Cp_x_Cp
    have h_Cp_Cp_comm : IsMulCommutative (CyclicGroup p × CyclicGroup p) :=
      ⟨⟨fun a b => mul_comm a b⟩⟩
    exact isMulCommutative_of_mulEquiv e h_Cp_Cp_comm

  have h_comm_sub_z : commutator G ≤ Z :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp h_quotient_z_abelian.is_comm

  have hcomm_nontrivial : commutator G ≠ ⊥ := by
    intro h
    apply h_na
    have h_center : Subgroup.center G = ⊤ := (commutator_eq_bot_iff_center_eq_top G).mp h
    exact IsMulCommutative.mk ⟨fun a b => by
      have ha : a ∈ Subgroup.center G := h_center ▸ Subgroup.mem_top a
      symm
      exact (Subgroup.mem_center_iff.mp ha) b⟩

  have h_or : Nat.card (commutator G) = 1 ∨ Nat.card (commutator G) = p := by
    have hdvd : Nat.card (commutator G) ∣ Nat.card Z :=
      Subgroup.card_dvd_of_le h_comm_sub_z
    have hdvd_p : Nat.card (commutator G) ∣ p := h_z_card_eq_p ▸ hdvd
    exact Nat.Prime.eq_one_or_self_of_dvd hn.out _ hdvd_p

  have h_ne_one : Nat.card (commutator G) ≠ 1 := by
    intro h
    exact hcomm_nontrivial (Subgroup.card_eq_one.mp h)

  have h_card_comm : Nat.card (commutator G) = p := h_or.resolve_left h_ne_one

  have h_card_subgroupOf : Nat.card ((commutator G).subgroupOf Z) = Nat.card (commutator G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h_comm_sub_z).toEquiv

  have h_card_comm_z : Nat.card (commutator G) = Nat.card Z := h_card_comm.trans h_z_card_eq_p.symm

  have h_comm_top : (commutator G).subgroupOf Z = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top]
    rw [h_card_subgroupOf]
    exact h_card_comm_z

  have h_comm_eq_z : commutator G = Z := by
    rw [Subgroup.subgroupOf_eq_top] at h_comm_top
    exact le_antisymm h_comm_sub_z h_comm_top

  -- Claim 4: There exists a, b in G such that aZ, bZ non-identity in G/Z and generate G/Z

  obtain ⟨x⟩ := h_g_quot_z_is_Cp_x_Cp

  let gen1 : CyclicGroup p × CyclicGroup p := (Multiplicative.ofAdd (1 : ZMod p), 1)
  let gen2 : CyclicGroup p × CyclicGroup p := (1, Multiplicative.ofAdd (1 : ZMod p))

  let aZ : G ⧸ Z := x.symm gen1
  let bZ : G ⧸ Z := x.symm gen2

  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective aZ
  obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective bZ

  have hgen1_ne : gen1 ≠ 1 := by
    simp only [ne_eq, Prod.mk_eq_one, and_true, gen1]
    intro h
    have : (1 : ZMod p) = 0 := Multiplicative.ofAdd.injective h
    exact absurd this one_ne_zero

  have hgen2_ne : gen2 ≠ 1 := by
    simp only [ne_eq, Prod.mk_eq_one, true_and, gen2]
    intro h
    have : (1 : ZMod p) = 0 := Multiplicative.ofAdd.injective h
    exact absurd this one_ne_zero

  have haZ_ne : aZ ≠ 1 := by
    intro h
    apply hgen1_ne
    exact x.symm.injective (by simp [aZ, h])

  have hbZ_ne : bZ ≠ 1 := by
    intro h
    apply hgen2_ne
    exact x.symm.injective (by simp [bZ, h])

  have h_hom_a : x (QuotientGroup.mk' Z a) = gen1 := by
    have hmk : QuotientGroup.mk' Z a = ↑a := rfl
    rw [hmk, ha]; simp only [aZ]; exact x.apply_symm_apply gen1

  have h_hom_b : x (QuotientGroup.mk' Z b) = gen2 := by
    have hmk : QuotientGroup.mk' Z b = ↑b := rfl
    rw [hmk, hb]; simp only [bZ]; exact x.apply_symm_apply gen2

  have hgen_cp : ∀ a : CyclicGroup p, ∃ k : ℤ, (Multiplicative.ofAdd (1 : ZMod p)) ^ k = a := by
    intro a
    refine ⟨(Multiplicative.toAdd a).cast, ?_⟩
    rw [← ofAdd_zsmul, zsmul_one]
    rw [ZMod.intCast_zmod_cast]
    rw [ofAdd_toAdd]

  have hprod_gen : ∀ q : CyclicGroup p × CyclicGroup p,
    ∃ m n : ℤ, q = gen1 ^ m * gen2 ^ n := by
    intro ⟨a, b⟩
    obtain ⟨m, hm⟩ := hgen_cp a
    obtain ⟨n, hn⟩ := hgen_cp b
    refine ⟨m, n, ?_⟩
    simp only [Prod.pow_mk, one_zpow, Prod.mk_mul_mk, mul_one, one_mul, Prod.ext_iff, gen1, gen2]
    constructor
    · exact hm.symm
    · exact hn.symm

  have hquot_gen : ∀ q : G ⧸ Z, ∃ m n : ℤ, q = aZ ^ m * bZ ^ n := by
    intro q
    obtain ⟨m, n, hmn⟩ := hprod_gen (x q)
    refine ⟨m, n, ?_⟩
    have := congr_arg x.symm hmn
    simp only [MulEquiv.symm_apply_apply, MulEquiv.map_mul, map_zpow, aZ, bZ] at this ⊢
    exact this

  -- Claim 5: Z, a, b generate G

  have hG_gen : ∀ g : G, ∃ m n : ℤ, ∃ z ∈ Z, g = a ^ m * b ^ n * z := by
    intro g
    obtain ⟨m, n, hmn⟩ := hquot_gen (QuotientGroup.mk' Z g)
    refine ⟨m, n, ?_⟩
    simp only [QuotientGroup.mk'_apply, aZ, bZ] at hmn
    change ↑g = aZ ^ m * bZ ^ n at hmn
    rw [← ha, ← hb] at hmn
    rw [← QuotientGroup.mk_zpow, ← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul] at hmn
    rw [QuotientGroup.eq] at hmn
    exact ⟨(a ^ m * b ^ n)⁻¹ * g,
      by rw [← Subgroup.inv_mem_iff]; convert hmn using 1; group,
      by group⟩

  -- Claim 6: a, b do not commute

  have hab_comm : a * b ≠ b * a := by
    intro h_comm
    have h_b_cent : b ∈ Subgroup.centralizer {a} := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      simp only [Set.mem_singleton_iff] at hg
      rw [hg]
      exact h_comm
    have h_Z_cent : Z ≤ Subgroup.centralizer {a} := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      simp only [Set.mem_singleton_iff] at hg
      rw [hg]
      exact (Subgroup.mem_center_iff.mp hz) a
    have h_a_cent : a ∈ Subgroup.centralizer {a} := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      simp only [Set.mem_singleton_iff] at hg
      rw [hg]
    have hcent_top : Subgroup.centralizer {a} = ⊤ := by
      rw [eq_top_iff]
      intro g _
      obtain ⟨m, n, z, hz, hgz⟩ := hG_gen g
      rw [hgz]
      apply Subgroup.mul_mem
      · apply Subgroup.mul_mem
        · exact Subgroup.zpow_mem _ h_a_cent m
        · exact Subgroup.zpow_mem _ h_b_cent n
      · exact h_Z_cent hz
    have ha_in_Z : a ∈ Z := by
      rw [hZ, Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer {a} := by rw [hcent_top]; exact Subgroup.mem_top g
      rw [Subgroup.mem_centralizer_iff] at hg
      exact (hg a rfl).symm
    have h_aZ_eq_one: aZ = 1 := by
      rw [← ha]
      change (↑a : G ⧸ Z) = ↑(1 : G)
      rw [QuotientGroup.eq]
      simp [ha_in_Z]
    exact absurd h_aZ_eq_one haZ_ne

  -- Claim 7: [a, b] is a non-identity element and generates Z

  have hab_comm_ne : ⁅a, b⁆ ≠ 1 := by
    intro h
    apply hab_comm
    rwa [commutatorElement_eq_one_iff_mul_comm] at h

  have hab_in_Z : ⁅a, b⁆ ∈ Z := by
    rw [← h_comm_eq_z, commutator_eq_normalClosure]
    apply Subgroup.subset_normalClosure
    exact @commutator_mem_commutatorSet G _ a b

  have hab_generates_Z : ∀ z ∈ Z, z ∈ Subgroup.zpowers ⁅a, b⁆ := by
    intro z hz
    have hmem := @mem_zpowers_of_prime_card (↥Z) _ p _ h_z_card_eq_p ⟨⁅a, b⁆, hab_in_Z⟩ ⟨z, hz⟩ ?_
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, congr_arg Subtype.val hk⟩
    · intro h
      apply hab_comm_ne
      have := congr_arg Subtype.val h
      simp only [OneMemClass.coe_one] at this
      exact this

  -- Claim 8: a, b have order either p or p^2

  have ha_order_dvd : orderOf a ∣ p ^ 3 := by
    have := orderOf_dvd_natCard a
    rwa [h] at this

  have ha_order_cases : orderOf a = 1 ∨ orderOf a = p ∨ orderOf a = p ^ 2 ∨ orderOf a = p ^ 3 := by
    have := (Nat.dvd_prime_pow hn.out).mp ha_order_dvd
    obtain ⟨i, hi, hia⟩ := this
    interval_cases i <;> simp_all

  have ha_order_ne_one : orderOf a ≠ 1 := by
    intro h
    apply haZ_ne
    rw [← ha]
    have : a = 1 := orderOf_eq_one_iff.mp h
    simp [this]

  have ha_order_ne_three : orderOf a ≠ (p ^ 3) := by
    intro h_order_eq_three
    rw [← h] at h_order_eq_three
    apply Eq.ge at h_order_eq_three
    have h_cyc : IsCyclic G := isCyclic_of_card_le_orderOf a h_order_eq_three
    exact h_na (isMulCommutative_iff.mpr (fun x y => h_cyc.commutative.comm x y))

  have ha_order : orderOf a = p ∨ orderOf a = p ^ 2 := by
    rcases ha_order_cases with h_1 | h_p | h_p2 | h_p3
    · exact absurd h_1 ha_order_ne_one
    · exact Or.inl h_p
    · exact Or.inr h_p2
    · exact absurd h_p3 ha_order_ne_three

  have hb_order_dvd : orderOf b ∣ p ^ 3 := by
    have := orderOf_dvd_natCard b
    rwa [h] at this

  have hb_order_cases : orderOf b = 1 ∨ orderOf b = p ∨ orderOf b = p ^ 2 ∨ orderOf b = p ^ 3 := by
    have hdvd := (Nat.dvd_prime_pow hn.out).mp hb_order_dvd
    obtain ⟨i, hi, hib⟩ := hdvd
    interval_cases i
    · left; simpa using hib
    · right; left; simpa using hib
    · right; right; left; simpa using hib
    · right; right; right; simpa using hib

  have hb_order_ne_one : orderOf b ≠ 1 := by
    intro h
    apply hbZ_ne
    rw [← hb]
    change (↑b : G ⧸ Z) = ↑(1 : G)
    rw [QuotientGroup.eq]
    simp [orderOf_eq_one_iff.mp h]

  have hb_order_ne_three : orderOf b ≠ p ^ 3 := by
    intro h_order_eq_three
    rw [← h] at h_order_eq_three
    apply Eq.ge at h_order_eq_three
    have hcyc : IsCyclic G := isCyclic_of_card_le_orderOf b h_order_eq_three
    exact h_na (isMulCommutative_iff.mpr (fun x y => hcyc.commutative.comm x y))

  have hb_order : orderOf b = p ∨ orderOf b = p ^ 2 := by
    rcases hb_order_cases with h1 | h2 | h3 | h4
    · exact absurd h1 hb_order_ne_one
    · exact Or.inl h2
    · exact Or.inr h3
    · exact absurd h4 hb_order_ne_three

  -- Claim 9: a^p, b^p in Z

  have hCp_exp : ∀ c : CyclicGroup p, c ^ p = 1 := by
    intro c
    haveI : Finite (CyclicGroup p) := by
      rw [show CyclicGroup p = Multiplicative (ZMod p) from rfl]
      exact instFiniteMultiplicative
    haveI : Fintype (CyclicGroup p) := Fintype.ofFinite _
    have h_card : Nat.card (CyclicGroup p) = p := card_cyclicGroup p
    have := @pow_card_eq_one (CyclicGroup p) _ _ c
    rwa [← Nat.card_eq_fintype_card, h_card] at this

  have hCp2_exp : ∀ q : CyclicGroup p × CyclicGroup p, q ^ p = 1 := by
    intro ⟨c, d⟩
    simp [hCp_exp c, hCp_exp d]

  have hquot_exp : ∀ q : G ⧸ Z, q ^ p = 1 := by
    intro q
    have := hCp2_exp (x q)
    rw [← map_pow] at this
    exact x.injective (by rwa [map_one])

  have ha_pow_in_Z : a ^ p ∈ Z := by
    have hmk := hquot_exp (QuotientGroup.mk' Z a)
    rw [← map_pow] at hmk
    change ((a ^ p) : G ⧸ Z) = 1 at hmk
    rw [show (↑a : G ⧸ Z) ^ p = ↑(a ^ p) from (map_pow (QuotientGroup.mk' Z) a p).symm] at hmk
    rw [show (1 : G ⧸ Z) = ↑(1 : G) from by simp] at hmk
    rw [QuotientGroup.eq] at hmk
    simpa using hmk

  have hb_pow_in_Z : b ^ p ∈ Z := by
    have hmk := hquot_exp (QuotientGroup.mk' Z b)
    rw [← map_pow] at hmk
    change (↑b : G ⧸ Z) ^ p = 1 at hmk
    rw [show (↑b : G ⧸ Z) ^ p = ↑(b ^ p) from (map_pow (QuotientGroup.mk' Z) b p).symm] at hmk
    rw [show (1 : G ⧸ Z) = ↑(1 : G) from by simp] at hmk
    rw [QuotientGroup.eq] at hmk
    simpa using hmk

  by_cases hp2 : p = 2
  · left
    constructor
    · exact hp2
    · subst hp2
      rcases ha_order with ha_p | ha_p2 <;> rcases hb_order with hb_p | hb_p2
      · -- Case A: both order 2 → D₄
        left
        have ha2 : orderOf a = 2 := by linarith
        have hb2 : orderOf b = 2 := by linarith
        exact case_A_isom a b ha2 hb2 hab_comm (by linarith)
      · -- Case B: a order 2, b order 4 → D₄
        left
        have hcard : Nat.card G = 8 := by rw [h]; norm_num
        exact case_B_isom b a hb_p2 ha_p (fun h => hab_comm h.symm) hcard
      · -- Case B2: a order 4, b order 2 → D₄
        left
        have hcard : Nat.card G = 8 := by rw [h]; norm_num
        exact case_B_isom a b ha_p2 hb_p hab_comm hcard
      · -- Case C: both order 4 → Q₈
        right
        have hcard : Nat.card G = 8 := by rw [h]; norm_num
        exact case_C_isom a b ha_p2 hb_p2 hab_comm hcard
  · right
    constructor
    · exact hp2
    · rcases ha_order with ha_p | ha_p2 <;> rcases hb_order with hb_p | hb_p2
      · -- Case A odd: both order p → UT₃
        left
        exact case_A_odd_isom p a b ha_p hb_p hab_comm h
      · -- Case B odd: a order p, b order p² → C_{p²} ⋊ C_p
        right
        exact case_B2_odd_isom hp2 b a hb_p2 ha_p (fun h => hab_comm h.symm) h
      · -- Case B2 odd: a order p², b order p → C_{p²} ⋊ C_p
        right
        exact case_B2_odd_isom hp2 a b ha_p2 hb_p hab_comm h
      · -- Case C odd: both order p² → C_{p²} ⋊ C_p
        right
        exact case_C_odd_isom hp2 a b ha_p2 hb_p2 hab_comm h

theorem prime_cubed_and_abelian_classification {p : ℕ} [hn : Fact p.Prime] [IsMulCommutative G]
  (h : Nat.card G = p ^ 3) :
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
      -- Step 1: All elements have order dividing p²
      -- (if some x had order p³ = |G|, it would generate G and make G cyclic)
      have hexp : ∀ x : G, orderOf x ∣ p ^ 2 := by
        intro x
        have hdvd : orderOf x ∣ p ^ 3 := h ▸ orderOf_dvd_natCard x
        rw [Nat.dvd_prime_pow hn.out] at hdvd
        obtain ⟨k, hk3, hxk⟩ := hdvd
        have hk3' : k ≠ 3 := fun hke =>
          hc (isCyclic_of_orderOf_eq_card x (by rw [hxk, hke]; exact h.symm))
        rw [hxk]
        exact Nat.pow_dvd_pow p (by omega)
      -- Step 2: Set up H = ⟨g⟩ and establish its order and normality
      let H : Subgroup G := Subgroup.zpowers g
      have hH : Nat.card H = p ^ 2 := Nat.card_zpowers g ▸ hg
      haveI hHnorm : H.Normal := inferInstance  -- automatic from CommGroup G
      -- Step 3: The quotient G/H has order p
      have hcard_quot : Nat.card (G ⧸ H) = p := by
        rw [← Subgroup.index_eq_card]
        have heq : H.index * Nat.card H = Nat.card G := Subgroup.index_mul_card H
        rw [hH, h] at heq
        have : H.index * p ^ 2 = p * p ^ 2 := by linarith [show p ^ 3 = p * p ^ 2 by ring]
        have : p ≠ 0 := hn.elim.ne_zero
        have : p^2 ≠ 0 := by aesop
        aesop
      -- Step 4: Find t₀ outside H
      obtain ⟨t₀, ht₀⟩ : ∃ t₀ : G, t₀ ∉ H := by
        by_contra hall
        push Not at hall
        rw [← Subgroup.eq_top_iff'] at hall
        rw [← Subgroup.card_eq_iff_eq_top, hH, h] at hall
        have : p ≠ 0 := hn.elim.ne_zero
        have : p ≠ 1 := hn.elim.ne_one
        subst hcard_quot
        simp_all only [Nat.card_zpowers, Nat.card_pos, ne_eq, not_false_eq_true, pow_right_inj₀,
                       Nat.reduceEqDiff, H]
      -- Step 5: t₀^p ∈ H  (every element of the order-p quotient has exponent p)
      have ht₀p_mem : t₀ ^ p ∈ H := by
        have hord : orderOf (QuotientGroup.mk' H t₀) ∣ p :=
          hcard_quot ▸ orderOf_dvd_natCard _
        have hpow : (QuotientGroup.mk' H t₀) ^ p = 1 :=
          orderOf_dvd_iff_pow_eq_one.mp hord
        rw [← map_pow (QuotientGroup.mk' H)] at hpow
        exact (QuotientGroup.eq_one_iff _).mp hpow
      -- Step 6: Extract integer k such that g^k = t₀^p
      obtain ⟨k, hk⟩ : ∃ k : ℤ, g ^ k = t₀ ^ p :=
        Subgroup.mem_zpowers_iff.mp ht₀p_mem
      -- Step 7: p | k  (from t₀^(p²) = 1 and g^k = t₀^p)
      have ht₀sq : t₀ ^ (p ^ 2) = 1 := orderOf_dvd_iff_pow_eq_one.mp (hexp t₀)
      have hgkp : g ^ (k * (p : ℤ)) = 1 := by
        rw [zpow_mul, zpow_natCast, hk]
        calc (t₀ ^ p) ^ p = t₀ ^ (p * p) := by rw [← pow_mul]
          _ = t₀ ^ (p ^ 2) := by rw [← sq]
          _ = 1 := ht₀sq
      have hp2dvd : (p ^ 2 : ℤ) ∣ k * (p : ℤ) := by
        have h := orderOf_dvd_iff_zpow_eq_one.mpr hgkp
        rw [hg] at h; exact_mod_cast h
      have hpdvdk : (p : ℤ) ∣ k := by
        have hp : (p : ℤ) ≠ 0 := by exact_mod_cast hn.out.ne_zero
        exact (mul_dvd_mul_iff_right hp).mp (sq (p : ℤ) ▸ hp2dvd)
      -- Step 8: Construct t = t₀ · g^(-m) of order p, not in H
      obtain ⟨m, hm⟩ := hpdvdk
      let t := t₀ * g ^ (-m)
      have ht_pow : t ^ p = 1 := by
        change (t₀ * g ^ (-m : ℤ)) ^ p = 1
        rw [mul_pow]
        have h2 : (g ^ (-m : ℤ)) ^ p = g ^ (-k : ℤ) := by
          rw [← zpow_natCast (g ^ (-m : ℤ)) p, ← zpow_mul]
          congr 1; rw [neg_mul, mul_comm m (p : ℤ), ← hm]
        rw [h2, ← hk, ← zpow_add, add_neg_cancel, zpow_zero]
      have ht_notH : t ∉ H := by
        change t₀ * g ^ (-m : ℤ) ∉ H
        intro hmem
        apply ht₀
        have hgm : g ^ (m : ℤ) ∈ H := Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩
        have heq : t₀ = t₀ * g ^ (-m : ℤ) * g ^ (m : ℤ) := by
          simp [mul_assoc]
        rw [heq]; exact H.mul_mem hmem hgm
      have ht_ord : orderOf t = p :=
        orderOf_eq_prime ht_pow (fun heq => ht_notH (heq ▸ H.one_mem))
      -- Step 9: Direct product G ≅ H × K ≅ CyclicGroup(p²) × CyclicGroup(p)
      let K : Subgroup G := Subgroup.zpowers t
      have hK : Nat.card K = p := Nat.card_zpowers t ▸ ht_ord
      haveI hKnorm : K.Normal := inferInstance
      have hinf : H ⊓ K = ⊥ := by
        rw [Subgroup.eq_bot_iff_card]
        have hdvdK : Nat.card (H ⊓ K : Subgroup G) ∣ Nat.card K :=
          Subgroup.card_dvd_of_le inf_le_right
        rw [hK] at hdvdK
        rcases Nat.Prime.eq_one_or_self_of_dvd hn.out _ hdvdK with h1 | hp
        · exact h1
        · exfalso
          have hHK_eq_K : (H ⊓ K : Subgroup G) = K :=
            Subgroup.eq_of_le_of_card_ge inf_le_right (Nat.le_of_eq (hp ▸ hK))
          exact ht_notH (hHK_eq_K ▸ inf_le_left <| Subgroup.mem_zpowers t)
      have hsup : H ⊔ K = ⊤ := by
        rw [← Subgroup.coe_eq_univ, Subgroup.normal_mul]
        apply Subgroup.prod_eq_of_inf_eq_bot_and_card hinf
        rw [hH, hK, h]; ring
      exact ⟨(mulEquivProd hHnorm hKnorm hinf hsup).trans
        ((mulEquivOfCyclicCardEq (hH.trans (card_cyclicGroup _).symm)).prodCongr
         (mulEquivOfCyclicCardEq (hK.trans (card_cyclicGroup _).symm)))⟩
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
            simp only [ofMul_mul, LinearEquiv.map_add, Pi.add_apply, toAdd_ofAdd]
            trivial }
      have e_fin3 : (Fin 3 → CyclicGroup p) ≃* CyclicGroup p × CyclicGroup p × CyclicGroup p :=
        { toFun := fun f => (f 0, f 1, f 2)
          invFun := fun ⟨a, b, c⟩ => Fin.cons a (Fin.cons b (fun _ => c))
          left_inv := fun f => funext fun i => by
            fin_cases i <;>
              simp only [Fin.cons_zero, Fin.reduceFinMk]
              <;> trivial
          right_inv := fun ⟨a, b, c⟩ => by
            simp only [Fin.isValue, Fin.cons_zero, Fin.cons_one, Prod.mk.injEq, true_and]
            trivial
          map_mul' := fun f g => rfl }
      exact ⟨e_mul.trans e_fin3⟩

theorem order_p_cubed_classification {p : ℕ} [hn : Fact p.Prime]
    (h : Nat.card G = p ^ 3) :
    (Nonempty (MulEquiv G (CyclicGroup (p^3)))) ∨
    (Nonempty (MulEquiv G (CyclicGroup (p^2) × CyclicGroup p))) ∨
    (Nonempty (MulEquiv G (CyclicGroup p × CyclicGroup p × CyclicGroup p))) ∨
    (p = 2 ∧ Nonempty (MulEquiv G (DihedralGroup 4))) ∨
    (p = 2 ∧ Nonempty (MulEquiv G (QuaternionGroup 2))) ∨
    (p ≠ 2 ∧ Nonempty (MulEquiv G (UT3 p))) ∨
    (p ≠ 2 ∧ Nonempty (MulEquiv G (CyclicGroup (p^2) ⋊[cpSqAction p] CyclicGroup p))) := by
  by_cases hab : IsMulCommutative G
  · haveI := hab
    rcases prime_cubed_and_abelian_classification (G := G) h with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
  · rcases prime_cubed_non_abelian_classification (G := G) hab h with
      ⟨hp2, hD4 | hQ8⟩ | ⟨hp2, hUT3 | hSemi⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hp2, hD4⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp2, hQ8⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp2, hUT3⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hp2, hSemi⟩)))))

theorem order8_classification {G : Type*} [Group G] (h : Nat.card G = 8) :
    (Nonempty (MulEquiv G (CyclicGroup 8))) ∨
    (Nonempty (MulEquiv G (CyclicGroup 4 × CyclicGroup 2))) ∨
    (Nonempty (MulEquiv G (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2))) ∨
    (Nonempty (MulEquiv G (DihedralGroup 4))) ∨
    (Nonempty (MulEquiv G (QuaternionGroup 2))) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have h' : Nat.card G = 2 ^ 3 := by rw [h]; norm_num
  rcases order_p_cubed_classification (G := G) h' with
    h1 | h2 | h3 | ⟨_, h4⟩ | ⟨_, h5⟩ | ⟨h6, _⟩ | ⟨h6, _⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h5)))
  · exact absurd rfl h6
  · exact absurd rfl h6

theorem order_odd_prime_cubed_classification {p : ℕ} [hn : Fact p.Prime] (hp : p ≠ 2)
    (h : Nat.card G = p ^ 3) :
    (Nonempty (MulEquiv G (CyclicGroup (p^3)))) ∨
    (Nonempty (MulEquiv G (CyclicGroup (p^2) × CyclicGroup p))) ∨
    (Nonempty (MulEquiv G (CyclicGroup p × CyclicGroup p × CyclicGroup p))) ∨
    (Nonempty (MulEquiv G (UT3 p))) ∨
    (Nonempty (MulEquiv G (CyclicGroup (p^2) ⋊[cpSqAction p] CyclicGroup p))) := by
  rcases order_p_cubed_classification (G := G) h with
    h1 | h2 | h3 | ⟨h4, _⟩ | ⟨h4, _⟩ | ⟨_, h6⟩ | ⟨_, h7⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact absurd h4 hp
  · exact absurd h4 hp
  · exact Or.inr (Or.inr (Or.inr (Or.inl h6)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h7)))

macro "classify_prime_cubed_odd" p:num h:term : tactic => `(tactic|(
  haveI : Fact (Nat.Prime $p) := ⟨by decide⟩
  exact order_odd_prime_cubed_classification (by decide) ($h |>.trans (by norm_num))))

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
  haveI hv : ValidIndex $p 1 := by decide
  use hv
  exact prime_classification_of_group $h))

macro "classify_prime_sq" p:num h:term : tactic => `(tactic|(
  haveI : Fact (Nat.Prime $p) := ⟨by decide⟩
  obtain (hiso | hiso) := p_squared_classification (p := $p) ($h |>.trans (by decide))
  · exact ⟨1, by decide , hiso⟩
  · exact ⟨2, by decide, hiso⟩))

-- For n = p*q where BOTH cyclic and non-cyclic groups exist (p ∣ q - 1).
-- The non-cyclic SDP in `retrieve (p*q) 1` is built from the same
-- `canonicalCpOnCqAction`, so the bridge is `rfl` (proof irrelevance).
macro "classify_pq" p:num q:num h:term : tactic => `(tactic|(
  haveI : Fact (Nat.Prime $p) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime $q) := ⟨by norm_num⟩
  rcases pq_classification (p := $p) (q := $q) (by norm_num)
      (Eq.trans $h (by norm_num)) with ⟨⟨e⟩⟩ | ⟨hr, ⟨e⟩⟩
  · exact ⟨2, by decide, ⟨e⟩⟩
  · refine ⟨1, by decide, ⟨e.trans ?_⟩⟩
    exact MulEquiv.refl _))

-- For n = p*q where p ∤ q - 1, so only the cyclic group exists.
macro "classify_pq_cyclic" p:num q:num h:term : tactic => `(tactic|(
  haveI : Fact (Nat.Prime $p) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime $q) := ⟨by norm_num⟩
  have ⟨e⟩ : Nonempty (_ ≃* CyclicGroup ($p * $q)) :=
    (pq_classification (p := $p) (q := $q) (by norm_num) (Eq.trans $h (by norm_num))).resolve_right
      (fun ⟨hr, _⟩ => absurd hr (by native_decide))
  exact ⟨1, by decide, ⟨e⟩⟩))

theorem order12_classification {G : Type*} [Group G] (h : Nat.card G = 12) :
    Nonempty (G ≃* retrieve 12 1) ∨
    Nonempty (G ≃* retrieve 12 2) ∨
    Nonempty (G ≃* retrieve 12 3) ∨
    Nonempty (G ≃* retrieve 12 4) ∨
    Nonempty (G ≃* retrieve 12 5) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rcases classification_4q (q := 3) (h_ge_3 := by norm_num)
      (h := h.trans (by norm_num)) with
    h1 | h2 | h3 | ⟨h1mod4, _⟩ | h5 | ⟨_, h6⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact absurd h1mod4 (by decide)
  · exact Or.inr (Or.inr (Or.inr (Or.inl h5)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h6)))

theorem order20_classification {G : Type*} [Group G] (h : Nat.card G = 20) :
    Nonempty (G ≃* retrieve 20 1) ∨
    Nonempty (G ≃* retrieve 20 2) ∨
    Nonempty (G ≃* retrieve 20 3) ∨
    Nonempty (G ≃* retrieve 20 4) ∨
    Nonempty (G ≃* retrieve 20 5) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rcases classification_4q (q := 5) (h_ge_3 := by norm_num)
      (h := h.trans (by norm_num)) with
    h1 | h2 | h3 | ⟨_, h4⟩ | h5 | ⟨h5eq3, _⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h5)))
  · exact absurd h5eq3 (by decide)

theorem order18_classification {G : Type*} [Group G] (h : Nat.card G = 18) :
    Nonempty (G ≃* retrieve 18 1) ∨
    Nonempty (G ≃* retrieve 18 2) ∨
    Nonempty (G ≃* retrieve 18 3) ∨
    Nonempty (G ≃* retrieve 18 4) ∨
    Nonempty (G ≃* retrieve 18 5) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rcases classification_2p2 (p := 3) (h_ge_3 := by norm_num)
      (h := h.trans (by norm_num)) with
    h1 | h2 | h3 | h4 | h5
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h5)))

theorem order28_classification {G : Type*} [Group G] (h : Nat.card G = 28) :
    Nonempty (G ≃* retrieve 28 1) ∨
    Nonempty (G ≃* retrieve 28 2) ∨
    Nonempty (G ≃* retrieve 28 3) ∨
    Nonempty (G ≃* retrieve 28 4) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rcases classification_4q (q := 7) (h_ge_3 := by norm_num)
      (h := h.trans (by norm_num)) with
    h1 | h2 | h3 | ⟨h1mod4, _⟩ | h5 | ⟨h7eq3, _⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact absurd h1mod4 (by decide)
  · exact Or.inr (Or.inr (Or.inr h5))
  · exact absurd h7eq3 (by decide)

/-- A group of order at most `maximumOrder` is isomorphic to some group obtained by `retrieve`. -/
theorem classification [hpos : NeZero n] [hmax : Fact (n <= maximumOrder)] (h : Nat.card G = n) :
  ∃ i : Nat, ∃ hv : ValidIndex n i, Nonempty (MulEquiv G (retrieve n i))
 := by
  have h1 : n ≥ 1 := NeZero.pos n
  have h2 : n ≤ maximumOrder := hmax.out
  interval_cases n

  -- n = 1
  · use 1
    haveI hv : ValidIndex 1 1 := by decide
    use hv
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

  -- n = 2
  · classify_prime 2 h

  -- n = 3
  · classify_prime 3 h

  -- n = 4
  · classify_prime_sq 2 h

  -- n = 5
  · classify_prime 5 h

  -- n = 6 = 2 * 3
  · classify_pq 2 3 h

  -- n = 7
  · classify_prime 7 h

  -- n = 8
  · rcases order8_classification h with h1 | h2 | h3 | h4 | h5
    · exact ⟨1, by decide, h1⟩
    · exact ⟨2, by decide, h2⟩
    · exact ⟨5, by decide, h3⟩
    · exact ⟨3, by decide, h4⟩
    · exact ⟨4, by decide, h5⟩

  -- n = 9
  · classify_prime_sq 3 h

  -- n = 10 = 2 * 5
  · classify_pq 2 5 h

  -- n = 11
  · classify_prime 11 h

  -- n = 12
  · rcases order12_classification h with h1 | h2 | h3 | h4 | h5
    · exact ⟨1, by decide, h1⟩
    · exact ⟨2, by decide, h2⟩
    · exact ⟨3, by decide, h3⟩
    · exact ⟨4, by decide, h4⟩
    · exact ⟨5, by decide, h5⟩

  -- n = 13
  · classify_prime 13 h

  -- n = 14 = 2 * 7
  · classify_pq 2 7 h

  -- n = 15 = 3 * 5  (only cyclic: 3 ∤ 4)
  · classify_pq_cyclic 3 5 h

  -- n = 16
  · sorry

  -- n = 17
  · classify_prime 17 h

  -- n = 18
  · rcases order18_classification h with h1 | h2 | h3 | h4 | h5
    · exact ⟨1, by decide, h1⟩
    · exact ⟨2, by decide, h2⟩
    · exact ⟨3, by decide, h3⟩
    · exact ⟨4, by decide, h4⟩
    · exact ⟨5, by decide, h5⟩

  -- n = 19
  · classify_prime 19 h

  -- n = 20
  · rcases order20_classification h with h1 | h2 | h3 | h4 | h5
    · exact ⟨1, by decide, h1⟩
    · exact ⟨2, by decide, h2⟩
    · exact ⟨3, by decide, h3⟩
    · exact ⟨4, by decide, h4⟩
    · exact ⟨5, by decide, h5⟩

  -- n = 21
  · classify_pq 3 7 h

  -- n = 22
  · classify_pq 2 11 h

  -- n = 23
  · classify_prime 23 h

  -- n = 24
  · sorry

  -- n = 25
  · classify_prime_sq 5 h

  -- n = 26
  · classify_pq 2 13 h

  -- n = 27
  · sorry

  -- n = 28
  · rcases order28_classification h with h1 | h2 | h3 | h4
    · exact ⟨1, by decide, h1⟩
    · exact ⟨2, by decide, h2⟩
    · exact ⟨3, by decide, h3⟩
    · exact ⟨4, by decide, h4⟩

  -- n = 29
  · classify_prime 29 h

  -- n = 30
  · sorry

  -- n = 31
  · classify_prime 31 h
