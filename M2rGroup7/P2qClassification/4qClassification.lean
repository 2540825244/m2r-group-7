import Mathlib
import «M2rGroup7».Lemmas.SylowUtils
import «M2rGroup7».Lemmas.LinearAlgebraUtils
import «M2rGroup7».Lemmas.GroupTheoryLemmas
import «M2rGroup7».Lemmas.ClassificationUtils
import «M2rGroup7».Lemmas.HomomorphismUtils

theorem classification_4q {q : ℕ} [h_q_prime : Fact q.Prime] [Group G] (h_ge_3 : q > 3) (h_3_mod_4 : q ≡ 3 [MOD 4]) (h : Nat.card G = 4 * q)
 : Nonempty (G ≃* CyclicGroup (4 * q)) := by

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
      exact ((by norm_num : (2 : ℕ).Prime).coprime_of_ne h_q_prime.out (by omega)).pow_left 2)

    -- Isomorphism G ≃* P ⋊ K
    have h_iso_g_p_k := SemidirectProduct.mulEquivSubgroup hK

    -- Homomorphism from K to MulAut(P)
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
      grind

    -- Step 2: K is cyclic (order q is prime)
    haveI hK_cyclic : IsCyclic ↥K := isCyclic_of_prime_card hK_card

    -- Step 3: K ≃* C_q
    have eK : ↥K ≃* CyclicGroup q :=
      mulEquivOfCyclicCardEq (hK_card.trans (card_cyclicGroup q).symm)
    --

    -- P is isomorphic to C_2 x C_2 or C_4
    haveI : Fact (Nat.Prime 2) := by decide
    rcases (p_squared_classification (p := 2) h_p_p2) with h_c4 | h_c2_c2
    · -- case h_c4 : Nonempty (↥↑P ≃* CyclicGroup 4)
      simp at h_c4

      -- Aut(P) is isomorphic to C_(2(2-1)) ≃* C_2
      have h_aut_P : MulAut P ≃* CyclicGroup 2 :=
        (MulAut.congr h_c4.some).trans (Classical.choice (aut_of_cyclic_p2 (p := 2)))

      have h_aut_card : Nat.card (MulAut ↥(↑P : Subgroup G)) = 2 :=
        (Nat.card_congr h_aut_P.toEquiv).trans (card_cyclicGroup 2)

      have h_phi_triv : φ = 1 :=
        eq_one_of_coprime_card (by rw [hK_card, h_aut_card];
          exact h_q_prime.out.coprime_of_ne (by norm_num) (by omega))
      refine ⟨?_⟩
      -- Directly construct ↥↑P ⋊[φ] ↥K ≃* ↥↑P × ↥K using φ = 1 element-wise
      have hφ1 : ∀ (k : ↥K) (n : ↥P), φ k n = n := fun k n => by
        have : φ k = 1 := DFunLike.congr_fun h_phi_triv k; simp [this]
      have h_sdp_prod : P ⋊[φ] ↥K ≃* P × ↥K := {
        toFun    := fun x => (x.left, x.right)
        invFun   := fun p => ⟨p.1, p.2⟩
        left_inv := fun x => SemidirectProduct.ext rfl rfl
        right_inv := fun _ => rfl
        map_mul' := fun x y => Prod.ext
          (by simp [SemidirectProduct.mul_left, hφ1])
          (by simp [SemidirectProduct.mul_right]) }
      -- gcd(2, q) = 1 since q is an odd prime
      have h2q : Nat.Coprime 2 q :=
        (by norm_num : (2 : ℕ).Prime).coprime_of_ne h_q_prime.out (by omega)
      -- CyclicGroup 4 × CyclicGroup q is cyclic since gcd(4, q) = 1
      haveI : IsCyclic (CyclicGroup 4 × CyclicGroup q) :=
        Group.isCyclic_prod_iff.mpr ⟨inferInstance, inferInstance,
          by rw [card_cyclicGroup, card_cyclicGroup]; exact h2q.pow_left 2⟩
      have h_card : Nat.card (CyclicGroup 4 × CyclicGroup q) = Nat.card (CyclicGroup (4 * q)) := by
        simp [Nat.card_prod, card_cyclicGroup]
      -- G ≃* ↥↑P ⋊[φ] ↥K ≃* ↥↑P × ↥K ≃* C₄ × Cq ≃* C_{4q}
      exact h_iso_g_p_k.symm.trans
        (h_sdp_prod.trans
          ((h_c4.some.prodCongr eK).trans (mulEquivOfCyclicCardEq h_card)))
--------
    · -- case h_c2_c2 : Nonempty (↥↑P ≃* CyclicGroup 2 × CyclicGroup 2)
      -- Aut(P) ≃* Aut(C_2 x C_2) ≃* GL_2(F_2) ≃* D_3
      have h_aut_dih : Nonempty (MulAut P ≃* DihedralGroup 3) := by
        obtain ⟨e1⟩ := h_c2_c2
        obtain ⟨e2⟩ := aut_of_CpCp 2
        exact ⟨((MulAut.congr e1).trans e2).trans GL2F2_isoS3⟩

      have h_dih_3_card : Nat.card (DihedralGroup 3) = 6 := by aesop
      have h_mul_aut_p_card : Nat.card (MulAut P) = 6 :=
        h_aut_dih.elim fun e => (Nat.card_congr e.toEquiv).trans h_dih_3_card

      have h_phi_triv : φ = 1 :=
        eq_one_of_coprime_card (by
          rw [hK_card, h_mul_aut_p_card]
          have h_cop2 : Nat.Coprime q 2 := h_q_prime.out.coprime_of_ne (by norm_num) (by omega)
          have h_cop3 : Nat.Coprime q 3 := h_q_prime.out.coprime_of_ne (by norm_num) (by omega)
          simpa using h_cop2.mul_right h_cop3)
      sorry
  · -- case h_nq_1 : n_q = 1
    sorry

theorem classify_Cqn_rtimes_Cpm_
    {p q r : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hq_odd : q ≠ 2)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (f : CyclicGroup (p ^ m) →* MulAut (CyclicGroup (q ^ n)))
    (h : Nat.card f.range = p ^ r)
    (hr : r ≤ min m ((q - 1).factorization p)) :
      Nonempty (SemidirectProduct (CyclicGroup (q ^ n)) (CyclicGroup (p ^ m)) f ≃*
               SemidirectProduct (CyclicGroup (q ^ n)) (CyclicGroup (p ^ m))
                 (canonicalAction p q n m hpq hq_odd hn r hr)) := by
  apply semidirectProduct_iso_if_range_eq hp (card_cyclicGroup _)
  have h_aut_iso : MulAut (CyclicGroup (q ^ n)) ≃* (ZMod (q ^ n))ˣ := by
    have h' := IsCyclic.mulAutMulEquiv (CyclicGroup (q ^ n))
    rwa [card_cyclicGroup] at h'
  haveI : Finite (MulAut (CyclicGroup (q ^ n))) :=
    Finite.of_equiv _ h_aut_iso.toEquiv.symm
  haveI : IsCyclic (MulAut (CyclicGroup (q ^ n))) :=
    (MulEquiv.isCyclic h_aut_iso).mpr (ZMod.isCyclic_units_of_prime_pow q hq.out hq_odd n)
  exact cyclic_subgroup_of_cyclic_group_is_unique
    Nat.card_pos rfl f.range _ h
    (canonicalAction_range_card p q n m r hpq hq_odd hn hr)
