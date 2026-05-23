import Mathlib.Logic.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Equiv.Basic
import «M2rGroup7».SmallGroupsLibrary
import «M2rGroup7».PqCase
import «M2rGroup7».SylowUtils
import «M2rGroup7».GroupTheoryLemmas
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
import Mathlib.Data.Finite.Card
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.Nat.Totient
import Mathlib.SetTheory.Cardinal.Finite

variable (G : Type*) [Group G]

theorem p2q_classification {p : ℕ} {q : ℕ} [h_p_prime : Fact p.Prime] [h_q_prime : Fact q.Prime] (h_p_ne_q : p ≠ q) (h_p_bound : p ≤ 3) (h : Nat.card G = p^2 * q) :
  Nonempty (G ≃* CyclicGroup (p ^ 2 * q)) := by

  let n_p := Nat.card (Sylow p G)
  let n_q := Nat.card (Sylow q G)

  -- G is finite
  haveI : Finite G := by
    apply Nat.finite_of_card_ne_zero
    rw [h]
    have p_ne : p ≠ 0 := Nat.Prime.ne_zero h_p_prime.elim
    have q_ne : q ≠ 0 := Nat.Prime.ne_zero h_q_prime.elim
    simp; tauto

  let P : Sylow p G := default

  -- Order of Sylow p-group is p^2
  have h_p_p2 : Nat.card ↥(P : Subgroup G) = p ^ 2 :=
    sylow_card_eq h_p_ne_q (show Nat.card G = p ^ 2 * q ^ 1 by aesop) P

  -- Index of Sylow p-group is q
  have h_p_idx_q : (↑P : Subgroup G).index = q := by
    simpa using sylow_index_eq h_p_ne_q (show Nat.card G = p ^ 2 * q ^ 1 by aesop) P

  -- n_p divides q
  have h_n_p_div_q : n_p ∣ q := by
    have h_sylow_dvd_p_index := Sylow.card_dvd_index P
    rw [h_p_idx_q] at h_sylow_dvd_p_index
    exact h_sylow_dvd_p_index

  -- n_p is 1 (mod p)
  have h_n_p_one_mod_p : n_p ≡ 1 [MOD p] := by
    change Nat.card (Sylow p G) ≡ 1 [MOD p]
    exact card_sylow_modEq_one p G

  -- Claim 1: n_p = 1 or n_q = 1

  have n_p_or_n_q_one : n_p = 1 ∨ n_q = 1 := by
    rcases lt_trichotomy p q with h_lt | h_eq | h_gt
    · -- case h_lt : p < q

      -- Step 1: n_q can be either 1, p, p^2

      let Q : Sylow q G := default

      -- Order of Sylow q-group is q
      have h_q_q : Nat.card ↥(Q : Subgroup G) = q := by
        have := sylow_card_eq (Ne.symm h_p_ne_q)
          (show Nat.card G = q ^ 1 * p ^ 2 by rw [pow_one, h]; ring) Q
        simpa using this

      -- Index of Sylow q-group is p^2
      have h_q_idx_p2 : (↑Q : Subgroup G).index = p ^ 2 := by
        simpa using sylow_index_eq (Ne.symm h_p_ne_q)
          (show Nat.card G = q ^ 1 * p ^ 2 by rw [pow_one, h]; ring) Q

      -- n_q divides p^2
      have h_n_p_div_q : n_q ∣ p^2 := by
        have h_sylow_dvd_p_index := Sylow.card_dvd_index Q
        rw [h_q_idx_p2] at h_sylow_dvd_p_index
        exact h_sylow_dvd_p_index

      -- n_q is 1, p, or p^2
      have h_n_q_cases : n_q = 1 ∨ n_q = p ∨ n_q = p^2 := by
        obtain ⟨k, hk, hkn⟩ := (Nat.dvd_prime_pow h_p_prime.out).mp h_n_p_div_q
        interval_cases k
        · left;  simpa using hkn
        · right; left;  simpa using hkn
        · right; right; simpa using hkn


      -- Step 2: n_q ≠ p as then q | p−1 contradicting p < q

      -- n_q is 1 (mod q)
      have h_n_p_one_mod_p : n_q ≡ 1 [MOD q] := by
        change Nat.card (Sylow q G) ≡ 1 [MOD q]
        exact card_sylow_modEq_one q G

      -- n_q ≠ p
      have h_n_q_neq_p : n_q ≠ p := by
        intro n_q_eq_p
        rw [n_q_eq_p] at h_n_p_one_mod_p
        unfold Nat.ModEq at h_n_p_one_mod_p
        rw [Nat.mod_eq_of_lt h_lt, Nat.mod_eq_of_lt h_q_prime.out.one_lt] at h_n_p_one_mod_p
        linarith [h_p_prime.out.one_lt]

      -- Step 3: If n_q ≠ 1, then n_q = p^2
      rcases h_n_q_cases with h_nq1 | h_nqp | h_nqp2
      · -- n_q = 1, done
        right; exact h_nq1
      · -- n_q = p, impossible
        exact absurd h_nqp h_n_q_neq_p
      · -- n_q = p^2

        -- Step 4: p^2 Sylow q-subgroup are trivially intersecting, so contribute p²(q−1) elements of order q

        -- Step 5: Remaining p² elements form one Sylow p-subgroup, so n_p = 1

        -- =========================================================
        -- BEGIN PROOF OF STEPS 4 & 5 (counting argument, n_p = 1)
        -- =========================================================

        left
        haveI hFinG : Fintype G := Fintype.ofFinite G
        haveI hDecEq : DecidableEq G := Classical.decEq G

        -- Helper: build a Finset G from a Subgroup G
        let toFset : ∀ H : Subgroup G, Finset G := fun H =>
          letI : Fintype ↥H := Fintype.ofFinite _
          (H : Set G).toFinset

        have mem_toFset : ∀ (H : Subgroup G) (x : G), x ∈ toFset H ↔ x ∈ H := fun H x => by
          letI : Fintype ↥H := Fintype.ofFinite _
          change x ∈ (H : Set G).toFinset ↔ x ∈ H
          simp [Set.mem_toFinset, SetLike.mem_coe]

        have toFset_card : ∀ H : Subgroup G, (toFset H).card = Nat.card ↥H := fun H => by
          letI : Fintype ↥H := Fintype.ofFinite _
          aesop

        -- All Sylow q-subgroups have order q
        have h_sylow_q_card : ∀ Q' : Sylow q G, Nat.card ↥(Q' : Subgroup G) = q := fun Q' => by
          have := sylow_card_eq (Ne.symm h_p_ne_q)
            (show Nat.card G = q ^ 1 * p ^ 2 by rw [pow_one, h]; ring) Q'
          simpa using this

        -- Any Sylow p-subgroup has order p^2
        have h_p_p2_gen : ∀ P' : Sylow p G, Nat.card ↥(P' : Subgroup G) = p ^ 2 := fun P' =>
          sylow_card_eq h_p_ne_q (show Nat.card G = p ^ 2 * q ^ 1 by aesop) P'

        -- Distinct Sylow q-subgroups intersect trivially
        have h_Qdisj : ∀ Q₁ Q₂ : Sylow q G, Q₁ ≠ Q₂ → Disjoint (Q₁ : Subgroup G) Q₂ := by
          intro Q₁ Q₂ hne
          rw [disjoint_iff]
          have hdvd : Nat.card ↥((Q₁ : Subgroup G) ⊓ Q₂) ∣ q := by
            calc Nat.card ↥((Q₁ : Subgroup G) ⊓ Q₂)
                ∣ Nat.card ↥(Q₁ : Subgroup G) := Subgroup.card_dvd_of_le inf_le_left
              _ = q := h_sylow_q_card Q₁
          rcases h_q_prime.out.eq_one_or_self_of_dvd _ hdvd with h1 | hq
          · exact Subgroup.card_eq_one.mp h1
          · exfalso; apply hne; apply Sylow.ext
            have hce1 : Nat.card ↥((Q₁ : Subgroup G) ⊓ Q₂) = Nat.card ↥(Q₁ : Subgroup G) :=
              hq.trans (h_sylow_q_card Q₁).symm
            have hce2 : Nat.card ↥((Q₁ : Subgroup G) ⊓ Q₂) = Nat.card ↥(Q₂ : Subgroup G) :=
              hq.trans (h_sylow_q_card Q₂).symm
            -- subgroupOf preserves Nat.card (via injective subtype map)
            have h_sgOf_card : ∀ (H K : Subgroup G), H ≤ K →
                Nat.card ↥(H.subgroupOf K) = Nat.card ↥H := fun H K hle => by
              calc Nat.card ↥(H.subgroupOf K)
                  = Nat.card ↥((H.subgroupOf K).map K.subtype) :=
                      (Subgroup.card_map_of_injective Subtype.coe_injective).symm
                _ = Nat.card ↥H := by rw [Subgroup.map_subgroupOf_eq_of_le hle]
            -- map K.subtype ⊤ = K (the image of ⊤ under the inclusion is K itself)
            have map_top_subtype : ∀ K : Subgroup G,
                Subgroup.map K.subtype (⊤ : Subgroup ↥K) = K := fun K => by
              ext x; simp only [Subgroup.mem_map, Subgroup.mem_top, true_and]
              exact ⟨fun ⟨y, hy⟩ => hy ▸ y.prop, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
            have heq1 : (Q₁ : Subgroup G) ⊓ Q₂ = Q₁ := by
              haveI : Finite ↥((Q₁ ⊓ Q₂ : Subgroup G).subgroupOf Q₁) := inferInstance
              have htop := (Subgroup.card_eq_iff_eq_top _).mp
                ((h_sgOf_card _ Q₁ inf_le_left).trans hce1)
              have hmb := Subgroup.map_subgroupOf_eq_of_le
                (inf_le_left (a := (Q₁ : Subgroup G)) (b := Q₂))
              rw [htop] at hmb
              exact (map_top_subtype Q₁ ▸ hmb).symm
            have heq2 : (Q₁ : Subgroup G) ⊓ Q₂ = Q₂ := by
              haveI : Finite ↥((Q₁ ⊓ Q₂ : Subgroup G).subgroupOf Q₂) := inferInstance
              have htop := (Subgroup.card_eq_iff_eq_top _).mp
                ((h_sgOf_card _ Q₂ inf_le_right).trans hce2)
              have hmb := Subgroup.map_subgroupOf_eq_of_le
                (inf_le_right (a := (Q₁ : Subgroup G)) (b := Q₂))
              rw [htop] at hmb
              exact (map_top_subtype Q₂ ▸ hmb).symm
            exact heq1.symm.trans heq2

        -- A Sylow p-subgroup and a Sylow q-subgroup always intersect trivially (different primes)
        have h_PQdisj : ∀ (P' : Sylow p G) (Q' : Sylow q G), Disjoint (P' : Subgroup G) Q' :=
          fun P' Q' => IsPGroup.disjoint_of_ne p q h_p_ne_q _ _ P'.isPGroup' Q'.isPGroup'

        -- Non-identity elements of any Sylow p-subgroup are absent from every Sylow q-subgroup
        have h_P_avoid_Q : ∀ (P' : Sylow p G) x, x ∈ (P' : Subgroup G) → x ≠ 1 →
            ∀ Q' : Sylow q G, x ∉ (Q' : Subgroup G) := fun P' x hxP hx1 Q' hxQ =>
          hx1 (Subgroup.mem_bot.mp ((disjoint_iff.mp (h_PQdisj P' Q'))
            ▸ Subgroup.mem_inf.mpr ⟨hxP, hxQ⟩))

        -- U = union of all Sylow q-subgroups (as a Finset)
        let U : Finset G := Finset.univ.biUnion (fun Q' : Sylow q G => toFset Q')

        -- Non-identity parts of distinct Sylow q-subgroups are pairwise disjoint
        have h_ne_pdisj : Set.PairwiseDisjoint ↑(Finset.univ : Finset (Sylow q G))
            (fun Q' : Sylow q G => toFset Q' \ {(1 : G)}) := by
          intro Q₁ _ Q₂ _ hne
          simp only [Function.onFun]
          rw [Finset.disjoint_left]
          rintro x hx1 hx2
          simp only [Finset.mem_sdiff, mem_toFset, Finset.mem_singleton] at hx1 hx2
          exact hx1.2 (Subgroup.mem_bot.mp ((disjoint_iff.mp (h_Qdisj Q₁ Q₂ hne))
            ▸ Subgroup.mem_inf.mpr ⟨hx1.1, hx2.1⟩))

        -- The biUnion of non-identity parts has cardinality n_q * (q - 1)
        have h_ne_card : (Finset.univ.biUnion (fun Q' : Sylow q G =>
            toFset Q' \ {(1 : G)})).card = n_q * (q - 1) := by
          rw [Finset.card_biUnion h_ne_pdisj]
          have h_each : ∀ Q' : Sylow q G, (toFset Q' \ {(1 : G)}).card = q - 1 := fun Q' => by
            have hmem : (1 : G) ∈ toFset Q' := (mem_toFset _ _).mpr (Q' : Subgroup G).one_mem
            rw [Finset.card_sdiff, Finset.inter_comm, Finset.inter_singleton_of_mem hmem,
                Finset.card_singleton, toFset_card, h_sylow_q_card]
          simp only [h_each, Finset.sum_const, Finset.card_univ, smul_eq_mul,
                      ← Nat.card_eq_fintype_card]
          rfl

        -- U decomposes as {1} ∪ (non-identity parts)
        have hU_split : U = {(1 : G)} ∪ Finset.univ.biUnion (fun Q' : Sylow q G =>
            toFset Q' \ {(1 : G)}) := by
          ext x
          simp only [U, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union,
                      Finset.mem_singleton, Finset.mem_sdiff, mem_toFset]
          constructor
          · rintro ⟨Q', hxQ'⟩
            rcases eq_or_ne x 1 with rfl | hx1
            · left; rfl
            · right; exact ⟨Q', hxQ', hx1⟩
          · rintro (rfl | ⟨Q', hxQ', _⟩)
            · exact ⟨Q, (Q : Subgroup G).one_mem⟩
            · exact ⟨Q', hxQ'⟩

        have hU_split_disj : Disjoint {(1 : G)} (Finset.univ.biUnion (fun Q' : Sylow q G =>
            toFset Q' \ {(1 : G)})) := by
          simp only [Finset.disjoint_left, Finset.mem_singleton, Finset.mem_biUnion,
                      Finset.mem_univ, true_and, Finset.mem_sdiff, mem_toFset]
          rintro _ rfl ⟨Q', _, h1⟩; exact h1 rfl

        -- |U| = 1 + n_q * (q - 1)
        have hUcard : U.card = 1 + n_q * (q - 1) := by
          rw [hU_split, Finset.card_union_of_disjoint hU_split_disj, Finset.card_singleton,
              h_ne_card]

        -- |univ \ U| = p^2 - 1  (the "remaining" elements)
        have hTcard : (Finset.univ \ U).card = p ^ 2 - 1 := by
          have hsum : (Finset.univ \ U).card + U.card = Fintype.card G := by
            have h1 := @Finset.card_sdiff_add_card_inter G _ Finset.univ U
            simp only [Finset.univ_inter] at h1
            linarith [Finset.card_univ (α := G)]
          have hU' : U.card = 1 + p ^ 2 * (q - 1) := h_nqp2 ▸ hUcard
          rw [← Nat.card_eq_fintype_card, h, hU'] at hsum
          have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ h_p_prime.out.pos
          rcases q with _ | k
          · exact absurd h_q_prime.out.pos (by omega)
          · simp only [Nat.succ_sub_one] at hsum
            have hring : p ^ 2 * (k + 1) = p ^ 2 * k + p ^ 2 := by ring
            omega

        -- Non-identity elements of any Sylow p-subgroup lie outside U
        have hPin_T : ∀ P' : Sylow p G, toFset P' \ {(1 : G)} ⊆ Finset.univ \ U := fun P' x => by
          simp only [Finset.mem_sdiff, mem_toFset, Finset.mem_singleton, Finset.mem_univ,
                      true_and, U, Finset.mem_biUnion]
          rintro ⟨hxP, hx1⟩ ⟨Q', hxQ⟩
          exact h_P_avoid_Q P' x hxP hx1 Q' hxQ

        -- Each Sylow p-subgroup contributes exactly p^2 - 1 non-identity elements
        have hPcard : ∀ P' : Sylow p G, (toFset P' \ {(1 : G)}).card = p ^ 2 - 1 := fun P' => by
          have hmem : (1 : G) ∈ toFset P' := (mem_toFset _ _).mpr (P' : Subgroup G).one_mem
          rw [Finset.card_sdiff, Finset.inter_comm, Finset.inter_singleton_of_mem hmem,
              Finset.card_singleton, toFset_card, h_p_p2_gen]

        -- The non-identity part of every Sylow p-subgroup equals univ \ U exactly
        have hPeqT : ∀ P' : Sylow p G, toFset P' \ {(1 : G)} = Finset.univ \ U :=
          fun P' => (Finset.subset_iff_eq_of_card_le
            (le_of_eq (hTcard.trans (hPcard P').symm))).mp (hPin_T P')

        -- Hence all Sylow p-subgroups coincide → Subsingleton → n_p = 1
        haveI hSubsing : Subsingleton (Sylow p G) := by
          refine ⟨fun P₁ P₂ => ?_⟩
          apply Sylow.ext; apply Subgroup.ext; intro x
          rcases eq_or_ne x 1 with rfl | hx1
          · simp
          · have h_neq : toFset P₁ \ {(1 : G)} = toFset P₂ \ {(1 : G)} :=
              (hPeqT P₁).trans (hPeqT P₂).symm
            have key := Finset.ext_iff.mp h_neq x
            simp only [Finset.mem_sdiff, mem_toFset, Finset.mem_singleton, hx1,
                        not_false_eq_true, and_true] at key
            exact key

        exact Nat.card_eq_one_iff_unique.mpr ⟨hSubsing, ⟨P⟩⟩

        -- =========================================================
        -- END PROOF OF STEPS 4 & 5
        -- =========================================================
    · -- case h_eq : p = q  (impossible since p ≠ q)
      trivial
    · -- case h_gt : q < p

      -- Step 1: Only divisor of q that's ≡ 1 (mod p) is 1. So n_p = 1.
      left
      rcases h_q_prime.out.eq_one_or_self_of_dvd n_p h_n_p_div_q with h | h
      · exact h
      · exfalso
        have hmod := h_n_p_one_mod_p
        rw [h] at hmod
        unfold Nat.ModEq at hmod
        rw [Nat.mod_eq_of_lt h_gt, Nat.mod_eq_of_lt h_p_prime.out.one_lt] at hmod
        linarith [h_q_prime.out.one_lt]

  rcases n_p_or_n_q_one with h_np1 | h_nq1
  · -- case h_np1 : n_p = 1
    haveI : Subsingleton (Sylow p G) :=
      (Nat.card_eq_one_iff_unique.mp h_np1).1

    have : P.Normal := by
      exact Sylow.normal_of_subsingleton P

    -- P is normal
    haveI hPnormal : (↑P : Subgroup G).Normal := Sylow.normal_of_subsingleton P

    obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime (N := (↑P : Subgroup G)) (by
      rw [h_p_p2, h_p_idx_q]
      exact (h_p_prime.out.coprime_iff_not_dvd.mpr (fun h => absurd (h_q_prime.out.eq_one_or_self_of_dvd p h)
        (by rintro (h1 | h2); exact h_p_prime.out.one_lt.ne' h1; exact h_p_ne_q h2))).pow_left 2)

    -- Isomorphism G ≃* P ⋊ K
    have h_iso_g_p_k := SemidirectProduct.mulEquivSubgroup hK

    have h_p_iso : Nonempty (P ≃* CyclicGroup (p ^ 2)) ∨ Nonempty (P ≃* CyclicGroup p × CyclicGroup p) :=
      p_squared_classification h_p_p2

    rcases h_p_iso with h_p_iso_p2 | h_p_iso_p_p
    · -- case h_p_iso_p2 : Nonempty (P ≃* CyclicGroup (p ^ 2))

      -- Step 1: Aut(P) ≃* C_(p(p-1))

      have h_aut_P : MulAut P ≃* CyclicGroup (p * (p - 1)) :=
        (MulAut.congr h_p_iso_p2.some).trans (Classical.choice aut_of_cyclic_p2)

      -- Step 2: If q divides p - 1 then there is exactly one subgroup of order q of C_p(p-1) otherwise zero

      let SubgroupsOfOrderQ :=
          {K : Subgroup (CyclicGroup (p * (p - 1))) | Nat.card K = q}

      by_cases h_q_dvd : q ∣ p - 1
      · -- case h_q_dvd : q ∣ p - 1

        -- The set of subgroups of CyclicGroup (p * (p - 1)) of order q

        -- There is exactly one such subgroup
        have h_unique_subgroup :
            Nat.card SubgroupsOfOrderQ = 1 := by
              have h_p_div : q ∣ p * (p - 1) := by
                exact dvd_mul_of_dvd_right h_q_dvd p

              have h_n_pos : p * (p - 1) > 0 := by
                have := Nat.Prime.one_lt h_p_prime.elim
                have := Nat.Prime.pos h_p_prime.elim
                aesop

              exact cyclic_subgroup_of_cyclic_group_is_unique h_p_div h_n_pos

        -- There are only two homomorphisms from C_q to C_(p(p-1))
        -- One is trivial homomorphism, and other one is where f(g) is non-identity where g is generator of C_q
        -- This is because image is subgroup of order q of C_(p(p-1)) and there is exactly one such subgroup

        -- ─────────────────────────────────────────────────────────────────────────
        -- Classifying G when P ≅ C_{p²} and q ∣ p − 1
        -- Two possibilities: G ≅ C_{p²q} (trivial action) or C_{p²} ⋊ C_q (nontrivial)
        -- ─────────────────────────────────────────────────────────────────────────

        -- Step 1: K has order q
        have hK_card : Nat.card ↥K = q := by
          have h1 : Nat.card G = Nat.card ↥(↑P : Subgroup G) * Nat.card ↥K := by
            have heq := Nat.card_congr h_iso_g_p_k.toEquiv
            rw [SemidirectProduct.card] at heq
            exact heq.symm
          rw [h_p_p2, h] at h1
          exact (Nat.eq_of_mul_eq_mul_left (pow_pos h_p_prime.out.pos 2) h1).symm

        -- Step 2: K is cyclic (order q is prime)
        haveI hK_cyclic : IsCyclic ↥K := isCyclic_of_prime_card hK_card

        -- Step 3: Concrete isomorphisms for the two pieces
        have eK : ↥K ≃* CyclicGroup q :=
          mulEquivOfCyclicCardEq (hK_card.trans (card_cyclicGroup q).symm)
        let eP : ↥(↑P : Subgroup G) ≃* CyclicGroup (p ^ 2) := Classical.choice h_p_iso_p2

        -- Step 4: Name the conjugation action φ : K → Aut(P) from the semidirect product
        let φ : ↥K →* MulAut ↥(↑P : Subgroup G) :=
          (↑P : Subgroup G).normalizerMonoidHom.comp
            (Subgroup.inclusion (by simp [Subgroup.normalizer_eq_top]))

        -- Step 5: Obtain a generator g of K (K is cyclic so one exists)
        obtain ⟨g, hg⟩ := hK_cyclic.exists_generator
        -- hg : ∀ x : ↥K, x ∈ zpowers g

        -- Case split: where does φ send the generator g?
        -- φ is determined by φ(g) since g generates all of K.
        by_cases h_triv : φ g = 1

        · -- ── Trivial action: φ(g) = 1, so φ = 1, so G ≅ P × K ≅ C_{p²q} ────
          -- Every element of K is a power of g, so φ = 1 on all of K.
          -- The semidirect product with trivial action is a direct product.
          -- C_{p²} × C_q ≅ C_{p²q} because gcd(p², q) = 1 (p ≠ q, both prime).
          have h_homo_triv : φ = 1 := by
            have h_phi_1_same_on_g : φ g = ((1 : K →* MulAut P) g) := h_triv
            exact monoidHom_eq_of_generator_eq hg h_phi_1_same_on_g
          have h_iso_almost_direct : P ⋊[1] ↥K ≃* G := by
            rw [← h_homo_triv]
            exact h_iso_g_p_k
          have h_direct : P ⋊[1] ↥K ≃* P × K := SemidirectProduct.mulEquivProd
          have := (h_direct.symm.trans h_iso_almost_direct).symm
          have h_1 := this.trans (eP.prodCongr eK)
          have h_2 : CyclicGroup (p ^ 2) × CyclicGroup q ≃* CyclicGroup (p ^ 2 * q) := by apply?
          exact Nonempty.intro (h_1.trans h_2)

        · -- ── Nontrivial action: φ(g) ≠ 1, so G ≅ C_{p²} ⋊ C_q ───────────────
          -- h_unique_subgroup gives a unique subgroup of order q in Aut(C_{p²}),
          -- so all nontrivial actions are equivalent up to isomorphism.

          sorry

        -- ─────────────────────────────────────────────────────────────────────────
      · -- case h_q_dvd : q ∤ p - 1
        have h_no_subgroup_helper : ∀ K : Subgroup (CyclicGroup (p * (p - 1))), Nat.card ↥K ≠ q := by
          intro K hK
          apply h_q_dvd
          have hq_dvd_prod : q ∣ p * (p - 1) := by
            have hLag := Subgroup.card_subgroup_dvd_card K
            simp only [card_cyclicGroup] at hLag
            rwa [hK] at hLag
          have hcop : Nat.Coprime q p :=
            h_q_prime.out.coprime_iff_not_dvd.mpr
              (fun hdvd => h_p_ne_q
                ((h_p_prime.out.eq_one_or_self_of_dvd q hdvd).resolve_left
                  h_q_prime.out.one_lt.ne').symm)
          exact hcop.dvd_of_dvd_mul_left hq_dvd_prod

        have h_no_subgroup :  Nat.card SubgroupsOfOrderQ = 0 := by aesop

        sorry

    · -- case h_p_iso_p_p : Nonempty (P ≃* CyclicGroup p × CyclicGroup p)
      sorry
  · -- case h_nq1 : n_q = 1
    sorry
