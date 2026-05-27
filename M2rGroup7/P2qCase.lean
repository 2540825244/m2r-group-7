import Mathlib.Logic.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Equiv.Basic
import «M2rGroup7».SmallGroupsLibrary
import «M2rGroup7».PqCase
import «M2rGroup7».Lemmas.SylowUtils
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

/-- The canonical non-trivial action φ₀ : C_q →* Aut(C_{p²}),
    sending the generator of C_q to the element of order q in Aut(C_{p²}). -/
noncomputable def canonicalP2QAction (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (h_div : q ∣ p * (p - 1)) : CyclicGroup q →* MulAut (CyclicGroup (p ^ 2)) :=
  let e := Classical.choice aut_of_cyclic_p2
  let target : MulAut (CyclicGroup (p ^ 2)) :=
    e.symm ((Multiplicative.ofAdd 1 : CyclicGroup (p * (p - 1))) ^ (p * (p - 1) / q))
  monoidHomOfForallMemZpowers
    (g := (Multiplicative.ofAdd 1 : CyclicGroup q))
    (fun x => by sorry)  -- every element of C_q is a zpow of the generator
    (g' := target)
    (by sorry)           -- orderOf target ∣ q

/-- The unique (up to isomorphism) non-trivial semidirect product C_{p²} ⋊ C_q,
    arising when q ∣ p(p-1). -/
noncomputable def P2QSemidirectProduct (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (h_div : q ∣ p * (p - 1)) : Type _ :=
  SemidirectProduct (CyclicGroup (p ^ 2)) (CyclicGroup q) (canonicalP2QAction p q h_div)

theorem p2q_classification {p : ℕ} {q : ℕ} [h_p_prime : Fact p.Prime] [h_q_prime : Fact q.Prime] (h_p_ne_q : p ≠ q) (h_p_bound : p ≤ 3) (h : Nat.card G = p^2 * q) :
  Nonempty (G ≃* CyclicGroup (p ^ 2 * q)) := by

  let n_p := Nat.card (Sylow p G)
  let n_q := Nat.card (Sylow q G)

  have n_p_or_n_q_one : n_p = 1 ∨ n_q = 1 := p2q_group_has_normal_sylow_subgroup G h_p_ne_q h

  -- G is finite
  haveI : Finite G := by
    apply Nat.finite_of_card_ne_zero
    rw [h]
    have p_ne : p ≠ 0 := Nat.Prime.ne_zero h_p_prime.elim
    have q_ne : q ≠ 0 := Nat.Prime.ne_zero h_q_prime.elim
    simp; tauto

  let P : Sylow p G := default

  -- Order of Sylow p-group is p^2
  have h_p_p2 : ∀ P : Sylow p G, Nat.card ↥(P : Subgroup G) = p ^ 2 := by
    intro P
    exact sylow_card_eq h_p_ne_q (show Nat.card G = p ^ 2 * q ^ 1 by aesop) P

  -- Index of Sylow p-group is q
  have h_p_idx_q : ∀ P : Sylow p G, (↑P : Subgroup G).index = q := by
    intro P
    simpa using sylow_index_eq h_p_ne_q (show Nat.card G = p ^ 2 * q ^ 1 by aesop) P

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
      p_squared_classification (h_p_p2 P)

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

theorem classification_4q {q : ℕ} [h_q_prime : Fact q.Prime] [Group G] (h_ge_3 : q > 3) (h_3_mod_4 : q ≡ 1 [MOD 4]) (h : Nat.card G = 4 * q) : True := by

  -- G is finite
  haveI : Finite G := by
    apply Nat.finite_of_card_ne_zero
    rw [h]
    have q_ne : q ≠ 0 := Nat.Prime.ne_zero h_q_prime.elim
    simp; tauto

  let n_2 := Nat.card (Sylow 2 G)
  let n_q := Nat.card (Sylow q G)

  have n_2_or_n_q_one : n_2 = 1 ∨ n_q = 1 := p2q_group_has_normal_sylow_subgroup G (by aesop) h

  rcases n_2_or_n_q_one with h_n2_1 | h_nq_1
  · -- case h_np1 : n_p = 1
    let P : Sylow 2 G := default
    -- lemma start
    haveI : Subsingleton (Sylow 2 G) :=
      (Nat.card_eq_one_iff_unique.mp h_n2_1).1

    have : P.Normal := by
      exact Sylow.normal_of_subsingleton P

    -- P is normal
    haveI hPnormal : (↑P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
    -- lemma end

    have h_p_p2 : Nat.card ↥(P : Subgroup G) = 4 := by
      exact sylow_card_eq (by aesop) (show Nat.card G = 2 ^ 2 * q ^ 1 by aesop) P

    -- Index of Sylow p-group is q
    have h_p_idx_q : ∀ P : Sylow 2 G, (↑P : Subgroup G).index = q := by
      intro P
      simpa using sylow_index_eq (by aesop) (show Nat.card G = 2 ^ 2 * q ^ 1 by aesop) P

    obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime (N := (↑P : Subgroup G)) (by
    rw [h_p_p2, h_p_idx_q]
    have h_p_ne_q : 2 ≠ q := by aesop
    exact (h_q_prime.out.coprime_iff_not_dvd.mpr (fun h => absurd (h_q_prime.out.eq_one_or_self_of_dvd 2 h)
      (by rintro (h1 | h2); exact h_q_prime.out.one_lt.ne' h1; exact h_p_ne_q h2))).pow_left 2)

    -- Isomorphism G ≃* P ⋊ K
    have h_iso_g_p_k := SemidirectProduct.mulEquivSubgroup hK

    --
    let φ : ↥K →* MulAut ↥(↑P : Subgroup G) :=
        (↑P : Subgroup G).normalizerMonoidHom.comp
          (Subgroup.inclusion (by simp [Subgroup.normalizer_eq_top]))

    -- Step 1: K has order q
    have hK_card : Nat.card ↥K = q := by
      have h1 : Nat.card G = Nat.card ↥(↑P : Subgroup G) * Nat.card ↥K := by
        have heq := Nat.card_congr h_iso_g_p_k.toEquiv
        rw [SemidirectProduct.card] at heq
        exact heq.symm
      rw [h_p_p2, h] at h1
      exact (Nat.eq_of_mul_eq_mul_left (pow_pos h_q_prime.out.pos 2) h1).symm

    -- Step 2: K is cyclic (order q is prime)
    haveI hK_cyclic : IsCyclic ↥K := isCyclic_of_prime_card hK_card

    -- Step 3: Concrete isomorphisms
    have eK : ↥K ≃* CyclicGroup q :=
      mulEquivOfCyclicCardEq (hK_card.trans (card_cyclicGroup q).symm)
    --

    -- P is isomorphic to C_2 x C_2 or C_4
    haveI : Fact (Nat.Prime 2) := by decide
    rcases (p_squared_classification (p := 2) h_p_p2) with h_c4 | h_c2_c2
    · -- case h_c4 : h_c4 : Nonempty (↥↑P ≃* CyclicGroup 4)
      simp at h_c4

      -- Aut(P) is isomorphic to C_(2(2-1)) = C_2
      have h_aut_P : MulAut P ≃* CyclicGroup 2 :=
        (MulAut.congr h_c4.some).trans (Classical.choice (aut_of_cyclic_p2 (p := 2)))

      have h_range_1_or_q : (Nat.card φ.range) = 1 ∨ (Nat.card φ.range) = q := by sorry

      rcases h_range_1_or_q with h_range_1 | h_range_q
      · sorry -- trivial homomorphism, giving C_{4q}
      · sorry -- non trivial homomorphism, giving C_{}


  · -- case h_np1 : n_p = 1
