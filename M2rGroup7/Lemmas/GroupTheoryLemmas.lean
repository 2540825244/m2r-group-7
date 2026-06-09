import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Logic.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Equiv.Basic
import «M2rGroup7».CyclicGroup
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
import «M2rGroup7».Lemmas.SylowUtils

/-- A group homomorphism out of a cyclic group is fully determined by
    its value on a generator. -/
lemma monoidHom_eq_of_generator_eq
    {G H : Type*} [Group G] [Group H]
    {f_1 f_2 : G →* H}
    {g : G} (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (h : f_1 g = f_2 g) : f_1 = f_2 := by
    ext x
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    rw [← hl, map_zpow f_1 g l, map_zpow f_2 g l, h]

/-- Given a cyclic group and d dividing its order, there exists a unique subgroup of order d. -/
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
    have h_d_pos : 0 < d :=
        Nat.pos_of_dvd_of_pos (by grind [Subgroup.card_subgroup_dvd_card]) h_n_pos
    have h_nd_pos : 0 < n / d :=
        Nat.div_pos (Nat.le_of_dvd h_n_pos (by grind [Subgroup.card_subgroup_dvd_card])) h_d_pos
    -- The canonical subgroup of order d is H = zpowers (g^(n/d))
    let g' := g ^ (n / d)
    have h_g'_order : orderOf g' = d := by
        change orderOf (g ^ (n / d)) = d
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
                calc n = n / Nat.gcd n m * Nat.gcd n m :=
                        (Nat.div_mul_cancel (Nat.gcd_dvd_left n m)).symm
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
                  _ = Nat.gcd n m                      := by
                      rw [Nat.div_mul_cancel ((by grind [Subgroup.card_subgroup_dvd_card])), ← hj]
                  _ = n / d                            := h_gcd_eq
            have h_eq := mul_left_cancel₀ h_nd_pos.ne' (h_mul.trans (mul_one _).symm)
            rwa [Nat.gcd_comm] at h_eq
        -- K ≤ H: g'^j = g^m ∈ H = zpowers g'
        have hKH : K ≤ H :=
            hKm.symm ▸ h_gm_eq.symm ▸
              Subgroup.zpowers_le.mpr (H.pow_mem (Subgroup.mem_zpowers g') j)
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

instance {p : ℕ} [h : Fact p.Prime] {n : ℕ} : NeZero (p ^ n) := by
  have hp : Nat.Prime p := h.out
  exact ⟨(pow_pos hp.pos n).ne'⟩

instance {p : ℕ} [h : Fact p.Prime] : NeZero (p * (p - 1)) := by
  have hp : Nat.Prime p := h.out
  have h2 : 2 ≤ p := hp.two_le
  exact ⟨Nat.mul_ne_zero (by omega) (by omega)⟩

/-- Aut(C_(p^2)) is isomorphic to C_(p * (p - 1)) -/
lemma aut_of_cyclic_p2 {p : ℕ} [h_p_prime : Fact p.Prime] :
    Nonempty (MulAut (CyclicGroup (p ^ 2)) ≃* CyclicGroup (p * (p - 1))) := by
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

/-- For a prime `q`, the automorphism group of `CyclicGroup q` is cyclic. -/
instance isCyclic_mulAut_cyclicGroup_prime {q : ℕ} [Fact q.Prime] :
    IsCyclic (MulAut (CyclicGroup q)) := by
  haveI : IsCyclic (ZMod q)ˣ := ZMod.isCyclic_units_prime (Fact.out : q.Prime)
  have h_iso : MulAut (CyclicGroup q) ≃* (ZMod q)ˣ := by
    have := IsCyclic.mulAutMulEquiv (CyclicGroup q)
    rwa [card_cyclicGroup] at this
  exact isCyclic_of_surjective h_iso.symm.toMonoidHom h_iso.symm.surjective

/-- For a prime `q`, `|Aut(C_q)| = q - 1`. -/
lemma card_mulAut_cyclicGroup_prime {q : ℕ} [hq : Fact q.Prime] :
    Nat.card (MulAut (CyclicGroup q)) = q - 1 := by
  have h_aut_iso : MulAut (CyclicGroup q) ≃* (ZMod q)ˣ := by
    have h := IsCyclic.mulAutMulEquiv (CyclicGroup q)
    rwa [card_cyclicGroup] at h
  rw [Nat.card_congr h_aut_iso.toEquiv, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime hq.out]

-- canonicalAction and classify_Cqn_rtimes_Cpm are in SylowUtils.lean
-- (they use semidirectProduct_iso_iff_range_eq from that file)


/-- Cardinality of the image of a homomorphism f : G -> G' divides gcd(|G|, |G'|) -/
theorem MonoidHom.card_range_dvd_gcd {G G' : Type*} [Group G] [Group G'] (f : G →* G') :
      Nat.card ↥f.range ∣ Nat.gcd (Nat.card G) (Nat.card G') :=
    Nat.dvd_gcd (Subgroup.card_range_dvd f) (Subgroup.card_subgroup_dvd_card f.range)

/-- A group of prime order is isomorphic to the cyclic group of the same order.
This is `prime_classification` from `M2rGroup7.Classification`, kept here under
a distinct name so both modules can coexist in the same build. -/
theorem prime_classification_of_group [hn : Fact n.Prime] [Group G] (h : Nat.card G = n) :
(Nonempty (G ≃* CyclicGroup n)) := by
  apply Nonempty.intro
  have h_g_card : Nat.card G = n := h
  have : IsCyclic G := isCyclic_of_prime_card h_g_card
  refine (mulEquivOfCyclicCardEq ?_)
  have h_c_card: Nat.card (CyclicGroup n) = n := card_cyclicGroup n
  rw [h_g_card, h_c_card]

open scoped Pointwise in
theorem pqr_group_has_normal_subgroup_card_qr {p : ℕ} {q : ℕ} {r : ℕ}
    [Group G] [h_p_prime : Fact p.Prime] [h_q_prime : Fact q.Prime] [h_r_prime : Fact r.Prime]
    (h_p_le_q : p < q) (h_q_le_r : q < r) (h : Nat.card G = p * q * r)
    : ∃ H : Subgroup G, Nat.card H = q * r ∧ H.Normal := by
  haveI hfin : Finite G := Nat.finite_of_card_ne_zero (h ▸
    Nat.mul_ne_zero (Nat.mul_ne_zero h_p_prime.out.ne_zero h_q_prime.out.ne_zero)
      h_r_prime.out.ne_zero)
  have h_p_ne_q : p ≠ q := Nat.ne_of_lt h_p_le_q
  have h_q_ne_r : q ≠ r := Nat.ne_of_lt h_q_le_r
  have h_p_ne_r : p ≠ r := Nat.ne_of_lt (Nat.lt_trans h_p_le_q h_q_le_r)
  -- Cards of Sylow subgroups via Sylow.card_eq_multiplicity + factorization
  have hQ_card : ∀ Q : Sylow q G, Nat.card (Q : Subgroup G) = q := fun Q => by
    rw [Sylow.card_eq_multiplicity, h,
        Nat.factorization_mul (Nat.mul_ne_zero h_p_prime.out.ne_zero h_q_prime.out.ne_zero)
                               h_r_prime.out.ne_zero,
        Nat.factorization_mul h_p_prime.out.ne_zero h_q_prime.out.ne_zero,
        h_p_prime.out.factorization, h_q_prime.out.factorization, h_r_prime.out.factorization]
    simp [Finsupp.add_apply, h_p_ne_q, Ne.symm h_q_ne_r]
  have hR_card : ∀ R : Sylow r G, Nat.card (R : Subgroup G) = r := fun R => by
    rw [Sylow.card_eq_multiplicity, h,
        Nat.factorization_mul (Nat.mul_ne_zero h_p_prime.out.ne_zero h_q_prime.out.ne_zero)
                               h_r_prime.out.ne_zero,
        Nat.factorization_mul h_p_prime.out.ne_zero h_q_prime.out.ne_zero,
        h_p_prime.out.factorization, h_q_prime.out.factorization, h_r_prime.out.factorization]
    simp [Finsupp.add_apply, h_q_ne_r, h_p_ne_r]
  -- Sylow subgroups for different primes are disjoint
  have hQR_disj : ∀ (Q : Sylow q G) (R : Sylow r G), Disjoint (Q : Subgroup G) R :=
    fun Q R => IsPGroup.disjoint_of_ne q r h_q_ne_r _ _ Q.isPGroup' R.isPGroup'
  -- Card of Q ⊔ R when the underlying sets multiply: uses injectivity of mult map
  have card_sup_eq : ∀ (Q : Sylow q G) (R : Sylow r G),
      (↑((Q : Subgroup G) ⊔ (R : Subgroup G)) : Set G)
        = (↑(Q : Subgroup G) : Set G) * (↑(R : Subgroup G) : Set G) →
      Nat.card ((Q : Subgroup G) ⊔ (R : Subgroup G) : Subgroup G) = q * r := fun Q R hmul => by
    let f : ↥(Q : Subgroup G) × ↥(R : Subgroup G) →
        ↥((Q : Subgroup G) ⊔ (R : Subgroup G)) := fun ⟨a, b⟩ =>
      ⟨(a : G) * b, by
        have : (a : G) * (b : G) ∈ (↑(Q : Subgroup G) : Set G) * (↑(R : Subgroup G) : Set G) :=
          Set.mul_mem_mul a.2 b.2
        rwa [← hmul] at this⟩
    have hbij : Function.Bijective f := by
      constructor
      · intro ⟨a, b⟩ ⟨c, d⟩ heq
        exact Subgroup.mul_injective_of_disjoint (hQR_disj Q R) (congr_arg Subtype.val heq)
      · intro ⟨x, hx⟩
        have hx' : x ∈ (↑(Q : Subgroup G) : Set G) * (↑(R : Subgroup G) : Set G) := by
          rwa [← hmul]
        obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx'
        exact ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, Subtype.ext rfl⟩
    calc Nat.card ((Q : Subgroup G) ⊔ (R : Subgroup G) : Subgroup G)
        = Nat.card (↥(Q : Subgroup G) × ↥(R : Subgroup G)) :=
          (Nat.card_congr (Equiv.ofBijective f hbij)).symm
      _ = Nat.card (Q : Subgroup G) * Nat.card (R : Subgroup G) := Nat.card_prod _ _
      _ = q * r := by rw [hQ_card Q, hR_card R]
  -- Index of Q ⊔ R when its card is q * r
  have index_eq_minfac : ∀ (Q : Sylow q G) (R : Sylow r G),
      Nat.card (Q ⊔ R : Subgroup G) = q * r →
      (Q ⊔ R : Subgroup G).index = (Nat.card G).minFac := fun Q R h_card_qr => by
    have h1 : (Q ⊔ R : Subgroup G).index * (q * r) = p * q * r := by
      have := Subgroup.index_mul_card (Q ⊔ R : Subgroup G)
      rw [h_card_qr, h] at this; exact this
    have h_idx : (Q ⊔ R : Subgroup G).index = p :=
      Nat.eq_of_mul_eq_mul_right
        (Nat.mul_pos h_q_prime.out.pos h_r_prime.out.pos)
        (h1.trans (by ring))
    rw [h_idx, h]
    exact (minFac_mul_of_prime_triple h_p_le_q h_q_le_r).symm
  -- Key: one of Sylow q or Sylow r is unique (hence normal)
  rcases pqr_group_has_normal_sylow_qr_subgroup (G := G) h_p_le_q h_q_le_r h with
    hq_unique | hr_unique
  · -- Case: Sylow q-subgroup is unique → normal
    haveI hq_ss : Subsingleton (Sylow q G) := (Nat.card_eq_one_iff_unique.mp hq_unique).1
    obtain ⟨Q⟩ : Nonempty (Sylow q G) := (Nat.card_eq_one_iff_unique.mp hq_unique).2
    obtain ⟨R⟩ : Nonempty (Sylow r G) := inferInstance
    haveI hQ_normal : (Q : Subgroup G).Normal := Sylow.normal_of_subsingleton Q
    have hmul : (↑((Q : Subgroup G) ⊔ (R : Subgroup G)) : Set G)
        = (↑(Q : Subgroup G) : Set G) * (↑(R : Subgroup G) : Set G) :=
      Subgroup.normal_mul (Q : Subgroup G) (R : Subgroup G)
    have h_card_qr := card_sup_eq Q R hmul
    exact ⟨Q ⊔ R, h_card_qr,
      Subgroup.normal_of_index_eq_minFac_card (index_eq_minfac Q R h_card_qr)⟩
  · -- Case: Sylow r-subgroup is unique → normal
    haveI hr_ss : Subsingleton (Sylow r G) := (Nat.card_eq_one_iff_unique.mp hr_unique).1
    obtain ⟨R⟩ : Nonempty (Sylow r G) := (Nat.card_eq_one_iff_unique.mp hr_unique).2
    obtain ⟨Q⟩ : Nonempty (Sylow q G) := inferInstance
    haveI hR_normal : (R : Subgroup G).Normal := Sylow.normal_of_subsingleton R
    have hmul : (↑((Q : Subgroup G) ⊔ (R : Subgroup G)) : Set G)
        = (↑(Q : Subgroup G) : Set G) * (↑(R : Subgroup G) : Set G) :=
      Subgroup.mul_normal (Q : Subgroup G) (R : Subgroup G)
    have h_card_qr := card_sup_eq Q R hmul
    exact ⟨Q ⊔ R, h_card_qr,
      Subgroup.normal_of_index_eq_minFac_card (index_eq_minfac Q R h_card_qr)⟩
