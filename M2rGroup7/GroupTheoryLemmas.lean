import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Logic.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Equiv.Basic
import «M2rGroup7».PqCase
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

/-- A group homomorphism out of a cyclic group is fully determined by
    its value on a generator. -/
lemma monoidHom_eq_of_generator_eq
    {G H : Type*} [Group G] [Group H]
    {f_1 f_2 : G →* H}
    {g : G} (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (h : f_1 g = f_2 g) : f_1 = f_2 := by
    ext x
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    rw [← hl, map_zpow f_1 g l, map_zpow f_2 g l, h]

lemma cyclic_subgroup_of_cyclic_group_is_unique {n d : ℕ} (h_d_div_n : d ∣ n) (h_n_pos : n > 0)
    : Nat.card ({K : Subgroup (CyclicGroup n) | Nat.card K = d}) = 1 := by
  let G := CyclicGroup n
  haveI : Finite G := by
    apply Nat.finite_of_card_ne_zero
    rw [card_cyclicGroup n]
    simp_all only [gt_iff_lt, ne_eq]
    apply Aesop.BuiltinRules.not_intro
    intro a
    subst a
    simp_all only [dvd_zero, lt_self_iff_false]
  -- Fix a generator g with orderOf g = n
  obtain ⟨g, hg_spec⟩ := (inferInstance : IsCyclic G).exists_generator
  have hg_order : orderOf g = n := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg_spec, card_cyclicGroup]
  have h_d_pos : 0 < d := Nat.pos_of_dvd_of_pos h_d_div_n h_n_pos
  have h_nd_pos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd h_n_pos h_d_div_n) h_d_pos
  -- The canonical subgroup of order d is H = zpowers (g^(n/d))
  let g' := g ^ (n / d)
  have h_g'_order : orderOf g' = d := by
    show orderOf (g ^ (n / d)) = d
    have hdvd : d ∣ orderOf g := hg_order.symm ▸ h_d_div_n
    have hne  : orderOf g ≠ 0  := hg_order.symm ▸ h_n_pos.ne'
    have := orderOf_pow_orderOf_div hne hdvd
    rwa [hg_order] at this
  let H := Subgroup.zpowers g'
  have h_H_card : Nat.card H = d := (Nat.card_zpowers g').trans h_g'_order
  -- Reduce to: every subgroup of order d equals H
  suffices h : ∀ (L : Subgroup G), Nat.card L = d → L = H by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun ⟨K, hK⟩ ⟨K', hK'⟩ => Subtype.ext ((h K hK).trans (h K' hK').symm)⟩,
           ⟨⟨H, h_H_card⟩⟩⟩
  intro K hK
  -- Since G = zpowers g, every subgroup satisfies K = zpowers (g^m) for some m
  have hK_le : K ≤ Subgroup.zpowers g := fun _ _ => hg_spec _
  rw [Subgroup.le_zpowers_iff] at hK_le
  obtain ⟨m, hKm⟩ := hK_le
  -- Recover orderOf (g^m) = d from |K| = d
  have h_m_order : orderOf (g ^ m) = d := by
    rw [← Nat.card_zpowers, ← hKm]; exact hK
  -- Compute gcd(n, m) = n/d using the order formula
  have h_gcd_eq : Nat.gcd n m = n / d := by
    have h_order_eq : n / Nat.gcd n m = d := by
      have := (orderOf_pow g).symm.trans h_m_order; rwa [hg_order] at this
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
        _ = Nat.gcd n m                      := by rw [Nat.div_mul_cancel h_d_div_n, ← hj]
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

/-- For each r ≤ min(m, d) where d = v_p(q - 1), the canonical action
    φ_r : C_{p^m} →* Aut(C_{q^n}) with image of order p^r.
    Construction: Aut(C_{q^n}) is cyclic of order q^{n-1}(q-1); picking a generator α,
    the element α ^ (|Aut| / p^r) has order exactly p^r. -/
noncomputable def canonicalAction
    (p q n m : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hq_odd : q ≠ 2) (hn : 0 < n)
    (r : ℕ) (hr : r ≤ min m ((q - 1).factorization p)) :
    CyclicGroup (p ^ m) →* MulAut (CyclicGroup (q ^ n)) := by
  sorry

/-- Semidirect products C_{q^n} ⋊ C_{p^m} (q odd prime, p ≠ q) are classified up to
    isomorphism by r ∈ {0, …, min(m, d)} where d = v_p(q - 1), giving min(m, d) + 1
    classes. Every action f belongs to exactly one class, represented by canonicalAction r. -/
theorem classify_Cqn_rtimes_Cpm
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hq_odd : q ≠ 2)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (f : CyclicGroup (p ^ m) →* MulAut (CyclicGroup (q ^ n))) :
    ∃! r : Fin (min m ((q - 1).factorization p) + 1),
      Nonempty (SemidirectProduct (CyclicGroup (q ^ n)) (CyclicGroup (p ^ m)) f ≃*
               SemidirectProduct (CyclicGroup (q ^ n)) (CyclicGroup (p ^ m))
                 (canonicalAction p q n m hpq hq_odd hn ↑r (Nat.lt_succ_iff.mp r.isLt))) := by
  sorry
