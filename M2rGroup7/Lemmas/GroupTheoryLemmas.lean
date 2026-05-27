import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Logic.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Equiv.Basic
import «M2rGroup7».SmallGroupsLibrary
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Logic.Unique
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
import Mathlib.Data.Finite.Card
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.Nat.Totient
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.GroupTheory.Sylow

/-- A group homomorphism out of a cyclic group is fully determined by
    its value on a generator. -/
lemma monoidHom_eq_of_generator_eq
    {G H : Type*} [Group G] [Group H]
    {f_1 f_2 : G →* H}
    {g : G} (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (h : f_1 g = f_2 g) : f_1 = f_2 := by
    ext x
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    rw [← hl, map_zpow f_1 g l, map_zpow f_2 g l, h]

lemma cyclic_subgroup_of_cyclic_group_is_unique {n d : ℕ} [Group G] [IsCyclic G]
  (h_n_pos : n > 0) (h_ord : Nat.card G = n) (K1 K2 : Subgroup G)
  (h1 : Nat.card K1 = d)
  (h2 : Nat.card K2 = d) :
  K1 = K2 := by
    haveI : Finite G := by
        apply Nat.finite_of_card_ne_zero
        grind
    -- Fix a generator g with orderOf g = n
    obtain ⟨g, hg_spec⟩ := (inferInstance : IsCyclic G).exists_generator
    have hg_order : orderOf g = n := by
        rw [orderOf_eq_card_of_forall_mem_zpowers hg_spec, h_ord]
    have h_d_pos : 0 < d := Nat.pos_of_dvd_of_pos (by grind [Subgroup.card_subgroup_dvd_card]) h_n_pos
    have h_nd_pos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd h_n_pos (by grind [Subgroup.card_subgroup_dvd_card])) h_d_pos
    -- The canonical subgroup of order d is H = zpowers (g^(n/d))
    let g' := g ^ (n / d)
    have h_g'_order : orderOf g' = d := by
        show orderOf (g ^ (n / d)) = d
        have hdvd : d ∣ orderOf g := hg_order.symm ▸ (by grind [Subgroup.card_subgroup_dvd_card])
        have hne  : orderOf g ≠ 0  := hg_order.symm ▸ h_n_pos.ne'
        have := orderOf_pow_orderOf_div hne hdvd
        rwa [hg_order] at this
    let H := Subgroup.zpowers g'
    have h_H_card : Nat.card H = d := (Nat.card_zpowers g').trans h_g'_order

    -- Local helper: any subgroup of order d equals H
    have h_eq (K : Subgroup G) (hK : Nat.card K = d) : K = H := by
        -- Since G = zpowers g, every subgroup satisfies K = zpowers (g^m) for some m
        have hK_le : K ≤ Subgroup.zpowers g := fun _ _ => hg_spec _
        rw [Subgroup.le_zpowers_iff] at hK_le
        obtain ⟨m, hKm⟩ := hK_le
        -- Recover orderOf (g^m) = d from |K| = d
        have h_m_order : orderOf (g ^ m) = d := by
            rw [← Nat.card_zpowers, ← hKm, hK]
        -- Compute gcd(n, m) = n/d using the order formula
        have h_gcd_eq : Nat.gcd n m = n / d := by
            have h_order_eq : n / Nat.gcd n m = d := by
                have := (orderOf_pow g).symm.trans h_m_order; exact hg_order ▸ this
            have h_n_eq : n = Nat.gcd n m * d :=
                calc n = n / Nat.gcd n m * Nat.gcd n m := (Nat.div_mul_cancel (Nat.gcd_dvd_left n m)).symm
                     _ = d * Nat.gcd n m               := by rw [h_order_eq]
                     _ = Nat.gcd n m * d               := mul_comm _ _
            -- n/d = Nat.gcd n m * d / d = Nat.gcd n m (avoid rewriting n inside Nat.gcd)
            calc Nat.gcd n m = Nat.gcd n m * d / d := (Nat.mul_div_cancel _ h_d_pos).symm
                 _           = n / d               := by rw [← h_n_eq]
        -- Write m = (n/d)*j for some j; note g^m = g'^j
        obtain ⟨j, hj⟩ := h_gcd_eq ▸ Nat.gcd_dvd_right n m
        have h_gm_eq : g ^ m = g' ^ j := by
            have hg'_def : g' = g ^ (n / d) := rfl
            rw [hg'_def, ← pow_mul, ← hj]
        -- Show gcd(j, d) = 1 using the gcd formula
        have h_gcd_jd : Nat.gcd j d = 1 := by
            have h_mul : n / d * Nat.gcd d j = n / d :=
                calc n / d * Nat.gcd d j
                    = Nat.gcd (n / d * d) (n / d * j) := (Nat.gcd_mul_left _ _ _).symm
                  _ = Nat.gcd n m                      := by rw [Nat.div_mul_cancel ((by grind [Subgroup.card_subgroup_dvd_card])), ← hj]
                  _ = n / d                            := h_gcd_eq
            have h_eq := mul_left_cancel₀ h_nd_pos.ne' (h_mul.trans (mul_one _).symm)
            rwa [Nat.gcd_comm] at h_eq
        -- K ≤ H: g'^j = g^m ∈ H = zpowers g'
        have hKH : K ≤ H :=
            hKm.symm ▸ h_gm_eq.symm ▸ Subgroup.zpowers_le.mpr (H.pow_mem (Subgroup.mem_zpowers g') j)
        -- H ≤ K: g' ∈ K = zpowers (g'^j) by mem_zpowers_pow_iff (gcd(j, d) = 1)
        have hHK : H ≤ K := by
            apply Subgroup.zpowers_le.mpr
            rw [hKm, h_gm_eq, mem_zpowers_pow_iff, h_g'_order]
            exact h_gcd_jd
        exact le_antisymm hKH hHK

    -- Use the helper to show both subgroups equal H, and apply transitivity
    have hK1 : K1 = H := h_eq K1 h1
    have hK2 : K2 = H := h_eq K2 h2
    exact hK1.trans hK2.symm

lemma aut_of_cyclic_p2 {p : ℕ} [h_p_prime : Fact p.Prime] : Nonempty (MulAut (CyclicGroup (p ^ 2)) ≃* CyclicGroup (p * (p - 1))) := by
    -- Aut(C_(p^2)) ≃* (ZMod (p ^ 2))ˣ
    have h_aut_c_p2_iso_cyclic : MulAut (CyclicGroup (p ^ 2)) ≃* (ZMod (p ^ 2))ˣ := by
        have h_aut := IsCyclic.mulAutMulEquiv (CyclicGroup (p ^ 2))
        rw [card_cyclicGroup (p ^ 2)] at h_aut
        exact h_aut

    -- (ZMod (p ^ 2))ˣ is cyclic
    have h_units_cyclic : IsCyclic (ZMod (p ^ 2))ˣ := by
        by_cases h_p2 : p = 2
        · subst h_p2
          exact ZMod.isCyclic_units_four
        · exact ZMod.isCyclic_units_of_prime_pow p h_p_prime.out h_p2 2

    have h_zmod_unit_order : Nat.card ((ZMod (p ^ 2))ˣ) = (p ^ 2).totient := by
        have := _root_.ZMod.card_units_eq_totient (p ^ 2)
        rw [Nat.card_eq_fintype_card]
        exact this

    have h_p2_totient : (p ^ 2).totient = p * (p - 1) := by
        have := Nat.totient_prime_pow_succ h_p_prime.out 1
        grind

    rw [h_p2_totient] at h_zmod_unit_order

    have h_iso_helper : Multiplicative (ZMod (p * (p - 1))) ≃* (ZMod (p ^ 2))ˣ := by
        have h' := zmodCyclicMulEquiv h_units_cyclic
        rw [h_zmod_unit_order] at h'
        exact h'

    have h_iso : CyclicGroup (p * (p - 1)) ≃* (ZMod (p ^ 2))ˣ := h_iso_helper

    have h_aut_equiv : MulAut (CyclicGroup (p ^ 2)) ≃* CyclicGroup (p * (p - 1)) :=
        h_aut_c_p2_iso_cyclic.trans h_iso.symm

    exact Nonempty.intro h_aut_equiv

-- canonicalAction and classify_Cqn_rtimes_Cpm are in SylowUtils.lean
-- (they use semidirectProduct_iso_iff_range_eq from that file)



/-!
## DihedralGroup 3 has a unique subgroup of order 3

D₃ has order 6 = 3¹·2¹. By Sylow theory the number of Sylow 3-subgroups n₃
satisfies n₃ ∣ 2 and n₃ ≡ 1 (mod 3), forcing n₃ = 1.
-/

/-- The dihedral group D₃ has exactly one Sylow 3-subgroup,
    hence exactly one subgroup of order 3. -/
lemma DihedralGroup3_unique_sylow3 :
    Nat.card (Sylow 3 (DihedralGroup 3)) = 1 := by
  haveI hp3 : Fact (Nat.Prime 3) := ⟨by decide⟩
  haveI hp2 : Fact (Nat.Prime 2) := ⟨by decide⟩
  haveI : Finite (DihedralGroup 3) := inferInstance
  let P : Sylow 3 (DihedralGroup 3) := default
  -- |D₃| = 6
  have h_G : Nat.card (DihedralGroup 3) = 6 := by
    rw [DihedralGroup.nat_card]
  -- |P| = 3^(v₃(6)) = 3^1 = 3
  have h_P : Nat.card ↥(P : Subgroup (DihedralGroup 3)) = 3 := by
    have key := Sylow.card_eq_multiplicity P
    rw [h_G] at key
    have hfac : (6 : ℕ).factorization 3 = 1 := by
      rw [show (6 : ℕ) = 3 ^ 1 * 2 ^ 1 from by norm_num,
          Nat.factorization_mul_of_coprime (by norm_num : Nat.Coprime (3 ^ 1) (2 ^ 1)),
          Finsupp.add_apply, Nat.factorization_pow_self hp3.out]
      simp [hp2.out.factorization, show ¬ (3 : ℕ) = 2 from by decide]
    rw [hfac] at key; simpa using key
  -- index of P = 6 / 3 = 2  (by Lagrange)
  have h_idx : (P : Subgroup (DihedralGroup 3)).index = 2 := by
    have hmul := Subgroup.index_mul_card (P : Subgroup (DihedralGroup 3))
    rw [h_P, h_G] at hmul; linarith
  -- n₃ ∣ 2
  have h_dvd : Nat.card (Sylow 3 (DihedralGroup 3)) ∣ 2 :=
    h_idx ▸ Sylow.card_dvd_index P
  -- n₃ ≡ 1 (mod 3)
  have h_mod : Nat.card (Sylow 3 (DihedralGroup 3)) ≡ 1 [MOD 3] :=
    card_sylow_modEq_one 3 (DihedralGroup 3)
  -- n₃ ∈ {1,2} and n₃ % 3 = 1 ⟹ n₃ = 1
  have h_pos : 0 < Nat.card (Sylow 3 (DihedralGroup 3)) := Nat.card_pos
  have h_le  : Nat.card (Sylow 3 (DihedralGroup 3)) ≤ 2 :=
    Nat.le_of_dvd (by norm_num) h_dvd
  simp only [Nat.ModEq] at h_mod
  omega

/-- Cardinality of the image of a homomorphism f : G -> G' divides gcd(|G|, |G'|) -/
theorem MonoidHom.card_range_dvd_gcd {G G' : Type*} [Group G] [Group G'] (f : G →* G') :
      Nat.card ↥f.range ∣ Nat.gcd (Nat.card G) (Nat.card G') :=
    Nat.dvd_gcd (Subgroup.card_range_dvd f) (Subgroup.card_subgroup_dvd_card f.range)
