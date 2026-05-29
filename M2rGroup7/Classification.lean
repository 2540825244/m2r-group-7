import Mathlib.Logic.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Equiv.Basic
import «M2rGroup7».SmallGroupsLibrary
import «M2rGroup7».PqCase
import «M2rGroup7».UT3
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

open scoped commutatorElement

lemma AddSubgroup.closure_singleton_int_one_eq_top : closure ({1} : Set ℤ) = ⊤ := by
  ext
  simp [mem_closure_singleton]

variable (n : ℕ) (G : Type*) [Group G]

lemma isMulCommutative_of_commGroup {M : Type*} [CommGroup M] : IsMulCommutative M :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

lemma isMulCommutative_iff {M : Type*} [Mul M] : IsMulCommutative M ↔ ∀ a b : M, a * b = b * a := by
  grind [IsMulCommutative, Std.Commutative]

lemma isMulCommutative_of_mulEquiv {M N : Type*} [Group M] [Group N] (e : M ≃* N) (h : IsMulCommutative N)
: IsMulCommutative M := by
  exact ⟨⟨fun x y => e.injective (by rw [e.map_mul, e.map_mul]; exact h.is_comm.comm (e x) (e y))⟩⟩

theorem center_eq_top_iff : Subgroup.center G = ⊤ ↔ IsMulCommutative G := by
  simp [Subgroup.eq_top_iff', isMulCommutative_iff, Subgroup.mem_center_iff, eq_comm]

theorem prime_classification [hn : Fact n.Prime] (h : Nat.card G = n) :
(Nonempty (MulEquiv G (CyclicGroup n))) := by
  apply Nonempty.intro
  have h_g_card : Nat.card G = n := h
  have : IsCyclic G := isCyclic_of_prime_card h_g_card
  refine (mulEquivOfCyclicCardEq ?_)
  have h_c_card: Nat.card (CyclicGroup n) = n := card_cyclicGroup n
  rw [h_g_card, h_c_card]

theorem prime_cubed_non_abelian_classification {p : ℕ} [hn : Fact p.Prime]
  (h_na : ¬IsMulCommutative G) (h : Nat.card G = p^3) :
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
        sorry

      | inr hb =>
        exact hb

  -- Claim 3: [G, G] = Z(G)

  have h_quotient_z_abelian : IsMulCommutative (G ⧸ Z) := by
    obtain ⟨e⟩ := h_g_quot_z_is_Cp_x_Cp
    have h_Cp_Cp_comm : CommGroup (CyclicGroup p × CyclicGroup p) := by unfold CyclicGroup; infer_instance
    apply isMulCommutative_of_commGroup at h_Cp_Cp_comm
    sorry

  have h_comm_sub_z : commutator G ≤ Z := by
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp h_quotient_z_abelian.is_comm

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
    simp [gen1]
    intro h
    have : (1 : ZMod p) = 0 := Multiplicative.ofAdd.injective h
    exact absurd this one_ne_zero

  have hgen2_ne : gen2 ≠ 1 := by
    simp [gen2]
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
    simp [gen1, gen2, Prod.ext_iff]
    constructor
    · exact hm.symm
    · exact hn.symm

  have hquot_gen : ∀ q : G ⧸ Z, ∃ m n : ℤ, q = aZ ^ m * bZ ^ n := by
    intro q
    obtain ⟨m, n, hmn⟩ := hprod_gen (x q)
    refine ⟨m, n, ?_⟩
    have := congr_arg x.symm hmn
    simp [MulEquiv.map_mul, aZ, bZ] at this ⊢
    exact this

  -- Claim 5: Z, a, b generate G

  have hG_gen : ∀ g : G, ∃ m n : ℤ, ∃ z ∈ Z, g = a ^ m * b ^ n * z := by
    intro g
    obtain ⟨m, n, hmn⟩ := hquot_gen (QuotientGroup.mk' Z g)
    refine ⟨m, n, ?_⟩
    simp [aZ, bZ] at hmn
    change ↑g = aZ ^ m * bZ ^ n at hmn
    rw [← ha, ← hb] at hmn
    rw [← QuotientGroup.mk_zpow, ← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul] at hmn
    rw [QuotientGroup.eq] at hmn
    exact ⟨(a ^ m * b ^ n)⁻¹ * g, by rw [← Subgroup.inv_mem_iff]; convert hmn using 1; group, by group⟩

  -- Claim 6: a, b do not commute

  have hab_comm : a * b ≠ b * a := by
    intro h_comm
    have h_b_cent : b ∈ Subgroup.centralizer {a} := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      simp at hg
      rw [hg]
      exact h_comm
    have h_Z_cent : Z ≤ Subgroup.centralizer {a} := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      simp at hg
      rw [hg]
      exact (Subgroup.mem_center_iff.mp hz) a
    have h_a_cent : a ∈ Subgroup.centralizer {a} := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      simp at hg
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
      show (↑a : G ⧸ Z) = ↑(1 : G)
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
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, congr_arg Subtype.val hk⟩
    intro h
    apply hab_comm_ne
    have := congr_arg Subtype.val h
    simp at this
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
    have := (Nat.dvd_prime_pow hn.out).mp hb_order_dvd
    obtain ⟨i, hi, hib⟩ := this
    interval_cases i <;> simp_all

  have hb_order_ne_one : orderOf b ≠ 1 := by
    intro h
    apply hbZ_ne
    rw [← hb]
    show (↑b : G ⧸ Z) = ↑(1 : G)
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
      · -- Case A: both order 2
        left
        sorry
      · -- Case B: a order 2, b order 4
        left
        sorry
      · -- Case B2: a order 4, b order 2
        left
        sorry
      · -- Case C: both order 4
        right
        sorry
  · right
    constructor
    · exact hp2
    · rcases ha_order with ha_p | ha_p2 <;> rcases hb_order with hb_p | hb_p2
      · -- Case A odd: both order p
        left
        sorry
      · -- Case B odd: a order p, b order p^2
        right
        sorry
      · -- Case B2 odd: a order p^2, b order p
        right
        sorry
      · -- Case C odd: both order p^2
        right
        sorry

theorem prime_cubed_and_abelian_classification {p : ℕ} [hn : Fact p.Prime] [CommGroup G] (h : Nat.card G = p^3) :
  (Nonempty (MulEquiv G (CyclicGroup (p^3)))) ∨
  (Nonempty (MulEquiv G (CyclicGroup (p^2) × CyclicGroup p))) ∨
  (Nonempty (MulEquiv G (CyclicGroup p × CyclicGroup p × CyclicGroup p)))
  := by
    have : Finite G := by
      apply Nat.finite_of_card_ne_zero
      rw [h]
      have p_ne : p ≠ 0 := Nat.Prime.ne_zero hn.elim
      exact pow_ne_zero 3 p_ne
    have h_finite_cycles := CommGroup.equiv_prod_multiplicative_zmod_of_finite G

    obtain ⟨IndexType, h'⟩ := h_finite_cycles
    obtain ⟨h_index_fin, h''⟩ := h'
    obtain ⟨order_func, h'''⟩ := h''
    obtain ⟨h_cycles_nontrivial, h_prod⟩ := h'''

    -- have : Nat.card G = Nat.card ((i : IndexType) → Multiplicative (ZMod (order_func i))) := sorry

    have order_to_group := fun i : IndexType => Multiplicative (ZMod (order_func i))
    let ProductGroup := ((i : IndexType) → Multiplicative (ZMod (order_func i)))

    have := Cardinal.mk_pi order_to_group

    have : ∀ i : IndexType, Cardinal.mk (order_to_group i) = order_func i := by
      sorry

    have : Cardinal.mk ProductGroup = Cardinal.prod fun i ↦ order_func i := by
      sorry

    -- have := Multiset.map (p^3) Finset.univ

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
