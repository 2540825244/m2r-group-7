import Mathlib
import «M2rGroup7».Lemmas.SylowUtils
import «M2rGroup7».Lemmas.LinearAlgebraUtils
import «M2rGroup7».Lemmas.GroupTheoryLemmas
import «M2rGroup7».Lemmas.ClassificationUtils
import «M2rGroup7».Lemmas.HomomorphismUtils
import «M2rGroup7».Lemmas.NumberTheoryUtils
import «M2rGroup7».P2qClassification.CycPGroupClassification

/-- The cyclic group identification `CyclicGroup q ≃* CyclicGroup (q^1)`. -/
private noncomputable def _cyclicGroup_pow_one_equiv
    {q : ℕ} [hq : Fact q.Prime] : CyclicGroup q ≃* CyclicGroup (q ^ 1) :=
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  haveI : NeZero (q ^ 1) := ⟨by simp [pow_one]; exact hq.out.ne_zero⟩
  mulEquivOfCyclicCardEq (by simp [card_cyclicGroup, pow_one])

/-- The canonical nontrivial action `C_4 →* Aut(C_q)` for q ≡ 3 (mod 4), q > 3.
    This is `canonicalAction 2 q 1 2 _ _ _ 1 _`, post-composed with
    `MulAut.congr` of the cyclic-group identification `CyclicGroup q ≃ CyclicGroup (q^1)`.
    Its image has order `2^1 = 2`, the unique order-2 subgroup of the cyclic group
    `Aut(C_q)` of order q − 1. -/
noncomputable def canonicalC4OnCqAction
    {q : ℕ} [hq : Fact q.Prime] (h_q_gt_3 : q > 3) :
    CyclicGroup 4 →* MulAut (CyclicGroup q) :=
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  ((MulAut.congr (_cyclicGroup_pow_one_equiv (q := q))).symm.toMonoidHom).comp
    (canonicalAction 2 q 1 2 (by omega) (by omega) Nat.one_pos 1
      (one_le_min_two_factorization_two h_q_gt_3))

/-- For q prime, q > 3, q ≡ 3 (mod 4), any nontrivial homomorphism
    `f : C_4 →* Aut(C_q)` has range of order `2^1 = 2`: the range divides both
    `|C_4| = 4` and `|Aut(C_q)| = q - 1`, and `gcd(4, q - 1) = 2`. -/
private lemma natCard_range_eq_two_of_nontrivial_C4_action
    {q : ℕ} [hq : Fact q.Prime] (h_q_gt_3 : q > 3) (h_3_mod_4 : q ≡ 3 [MOD 4])
    (f : CyclicGroup 4 →* MulAut (CyclicGroup q)) (hf : f ≠ 1) :
    Nat.card f.range = 2 ^ 1 := by
  have h_aut_card : Nat.card (MulAut (CyclicGroup q)) = q - 1 := by
    have h_aut_iso : MulAut (CyclicGroup q) ≃* (ZMod q)ˣ := by
      have h := IsCyclic.mulAutMulEquiv (CyclicGroup q)
      rwa [card_cyclicGroup] at h
    rw [Nat.card_congr h_aut_iso.toEquiv, Nat.card_eq_fintype_card,
        ZMod.card_units_eq_totient, Nat.totient_prime hq.out]
  have h_dvd_4 : Nat.card f.range ∣ 4 := by
    have h := Subgroup.card_range_dvd f
    rwa [card_cyclicGroup] at h
  have h_dvd_qm1 : Nat.card f.range ∣ q - 1 := by
    rw [← h_aut_card]
    exact Subgroup.card_subgroup_dvd_card f.range
  have h_gcd : Nat.gcd 4 (q - 1) = 2 := gcd_four_of_prime_three_mod_four h_3_mod_4
  have h_dvd_2 : Nat.card f.range ∣ 2 := by
    rw [← h_gcd]; exact Nat.dvd_gcd h_dvd_4 h_dvd_qm1
  -- f ≠ 1, hence range ≠ ⊥, hence |range| > 1.
  have h_card_pos : 0 < Nat.card f.range := Nat.card_pos
  have h_range_ne_bot : f.range ≠ ⊥ := fun h => hf (MonoidHom.range_eq_bot_iff.mp h)
  have h_card_gt_1 : 1 < Nat.card f.range := by
    by_contra h_not
    push_neg at h_not
    have h_card_one : Nat.card f.range = 1 := by omega
    have h_range_bot : f.range = ⊥ :=
      (Subgroup.eq_bot_iff_card f.range).mpr h_card_one
    exact h_range_ne_bot h_range_bot
  -- Combine: card divides 2 and is > 1, so = 2 = 2^1.
  have h_le_2 : Nat.card f.range ≤ 2 := Nat.le_of_dvd (by norm_num) h_dvd_2
  interval_cases (Nat.card f.range)
  rfl

/-- The range of `canonicalC4OnCqAction` has cardinality 2: composing
    `canonicalAction 2 q 1 2 _ _ _ 1 _` (range card `2^1`) with an iso of
    `MulAut`s preserves range cardinality. -/
private lemma canonicalC4OnCqAction_range_card
    {q : ℕ} [hq : Fact q.Prime] (h_q_gt_3 : q > 3) :
    Nat.card (canonicalC4OnCqAction h_q_gt_3).range = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  show Nat.card
      ((((MulAut.congr (_cyclicGroup_pow_one_equiv (q := q))).symm.toMonoidHom).comp
        (canonicalAction 2 q 1 2 (by omega) (by omega) Nat.one_pos 1
          (one_le_min_two_factorization_two h_q_gt_3))).range) = 2
  rw [MonoidHom.range_comp,
      Subgroup.card_map_of_injective
        (MulAut.congr (_cyclicGroup_pow_one_equiv (q := q))).symm.injective]
  have := canonicalAction_range_card 2 q 1 2 1
    (by omega : (2 : ℕ) ≠ q) (by omega : q ≠ 2) Nat.one_pos
    (one_le_min_two_factorization_two h_q_gt_3)
  simpa using this

/-- The canonical semidirect product C_{q^1} ⋊_{canonicalAction 1} C_{2^2} is isomorphic
    to C_q ⋊_{canonicalC4OnCqAction} C_4. This is the back-bridge needed when applying
    classify_sdp in the 4q classification. -/
private noncomputable def canonicalAction_one_iso_canonicalC4OnCqAction
    {q : ℕ} [hq : Fact q.Prime] (h_ge_3 : q > 3) :
    SemidirectProduct (CyclicGroup (q ^ 1)) (CyclicGroup (2 ^ 2))
      (canonicalAction 2 q 1 2 (by omega) (by omega) Nat.one_pos 1
        (one_le_min_two_factorization_two h_ge_3)) ≃*
    SemidirectProduct (CyclicGroup q) (CyclicGroup 4) (canonicalC4OnCqAction h_ge_3) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let pq_iso : CyclicGroup q ≃* CyclicGroup (q ^ 1) := _cyclicGroup_pow_one_equiv
  have h_action_eq :
      (MulAut.congr pq_iso).toMonoidHom.comp
          ((canonicalC4OnCqAction h_ge_3).comp (MulEquiv.refl (CyclicGroup 4)).symm) =
        canonicalAction 2 q 1 2 (by omega) (by omega) Nat.one_pos 1
          (one_le_min_two_factorization_two h_ge_3) := by
    refine MonoidHom.ext fun k => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.refl_symm]
    change (MulAut.congr pq_iso) (canonicalC4OnCqAction h_ge_3 k) = _
    simp only [canonicalC4OnCqAction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact MulEquiv.apply_symm_apply (MulAut.congr pq_iso) _
  exact (h_action_eq ▸ SemidirectProduct.congr'
    (φ₁ := canonicalC4OnCqAction h_ge_3) (fn := pq_iso) (fg := MulEquiv.refl _)).symm

theorem classification_4q {q : ℕ} [h_q_prime : Fact q.Prime] [Group G] (h_ge_3 : q > 3) (h_3_mod_4 : q ≡ 3 [MOD 4]) (h : Nat.card G = 4 * q)
 : Nonempty (G ≃* CyclicGroup (4 * q))
   ∨ Nonempty (G ≃* CyclicGroup 2 × CyclicGroup 2 × CyclicGroup q)
   ∨ Nonempty (G ≃* SemidirectProduct (CyclicGroup q) (CyclicGroup 4) (canonicalC4OnCqAction h_ge_3)) := by

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

    -- Enough to synthesize instance of type class (↑P).Normal
    -- for Subgroup.exists_right_complement'_of_coprime
    haveI : Subsingleton (Sylow 2 G) :=
      (Nat.card_eq_one_iff_unique.mp h_n2_1).1

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

    -- Could be a lemma
    -- Step 1: K has order q
    have hK_card : Nat.card ↥K = q := by
      have h1 : Nat.card G = Nat.card ↥(↑P : Subgroup G) * Nat.card ↥K := by
        have heq := Nat.card_congr h_iso_g_p_k.toEquiv
        rw [SemidirectProduct.card] at heq
        exact heq.symm
      rw [h_p_p2, h] at h1
      grind

    -- Step 2: K ≃* C_q
    have eK : ↥K ≃* CyclicGroup q :=
      Classical.choice (prime_classification (n := q) hK_card)

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
        eq_one_of_coprime_card (by
          rw [hK_card, h_aut_card]
          exact h_q_prime.out.coprime_of_ne (by norm_num : (2 : ℕ).Prime) (by omega))
      have : Nonempty (G ≃* CyclicGroup (4 * q)) := by
        refine ⟨?_⟩
        have h_sdp_prod : P ⋊[φ] ↥K ≃* P × ↥K :=
          SemidirectProduct.mulEquivOfTrivialAction h_phi_triv
        have h4q : Nat.Coprime 4 q :=
          ((by norm_num : (2 : ℕ).Prime).coprime_of_ne h_q_prime.out (by omega)).pow_left 2
        -- G ≃* ↥↑P ⋊[φ] ↥K ≃* ↥↑P × ↥K ≃* C₄ × Cq ≃* C_{4q}
        exact h_iso_g_p_k.symm.trans
          (h_sdp_prod.trans
            ((h_c4.some.prodCongr eK).trans (CyclicGroup.prodMulEquiv h4q)))
      tauto
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

      have : Nonempty (G ≃* CyclicGroup 2 × CyclicGroup 2 × CyclicGroup q) := by
        refine ⟨?_⟩
        have h_sdp_prod : P ⋊[φ] ↥K ≃* P × ↥K :=
          SemidirectProduct.mulEquivOfTrivialAction h_phi_triv

        have h4q : Nat.Coprime 4 q :=
          ((by norm_num : (2 : ℕ).Prime).coprime_of_ne h_q_prime.out (by omega)).pow_left 2
        -- G ≃* ↥↑P ⋊[φ] ↥K ≃* ↥↑P × ↥K ≃* C_2 × C ≃* C_{4q}
        exact h_iso_g_p_k.symm.trans
          (h_sdp_prod.trans
            ((h_c2_c2.some.prodCongr eK).trans MulEquiv.prodAssoc))
      tauto
  · -- case h_nq_1 : n_q = 1
    let Q : Sylow q G := default

    -- Enough to synthesize instance of type class (↑Q).Normal
    -- for Subgroup.exists_right_complement'_of_coprime
    haveI : Subsingleton (Sylow q G) :=
      (Nat.card_eq_one_iff_unique.mp h_nq_1).1

    have h_Q_card : Nat.card ↥(Q : Subgroup G) = q := by
      have := sylow_card_eq (Ne.symm (by aesop : (2 : ℕ) ≠ q))
        (show Nat.card G = q ^ 1 * 2 ^ 2 by rw [pow_one, h]; ring) Q
      simpa using this

    -- Index of Sylow q-group is 4
    have h_Q_idx_4 : ∀ Q : Sylow q G, (↑Q : Subgroup G).index = 4 := by
      intro Q
      have := sylow_index_eq (Ne.symm (by aesop : (2 : ℕ) ≠ q))
        (show Nat.card G = q ^ 1 * 2 ^ 2 by rw [pow_one, h]; ring) Q
      simpa using this

    obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime (N := (↑Q : Subgroup G)) (by
      rw [h_Q_card, h_Q_idx_4]
      exact (h_q_prime.out.coprime_of_ne (by norm_num : (2 : ℕ).Prime) (by omega)).pow_right 2)

    -- Isomorphism G ≃* Q ⋊ K
    have h_iso_g_q_k := SemidirectProduct.mulEquivSubgroup hK

    -- Homomorphism from K to MulAut(Q)
    let φ : ↥K →* MulAut ↥(↑Q : Subgroup G) :=
        (↑Q : Subgroup G).normalizerMonoidHom.comp
          (Subgroup.inclusion (by simp [Subgroup.normalizer_eq_top]))

    -- Step 1: K has order 4
    have hK_card : Nat.card ↥K = 4 := by
      have h1 : Nat.card G = Nat.card ↥(↑Q : Subgroup G) * Nat.card ↥K := by
        have heq := Nat.card_congr h_iso_g_q_k.toEquiv
        rw [SemidirectProduct.card] at heq
        exact heq.symm
      rw [h_Q_card, h] at h1
      have hq_pos : 0 < q := h_q_prime.out.pos
      have heq2 : q * 4 = q * Nat.card ↥K := by linarith
      exact (Nat.eq_of_mul_eq_mul_left hq_pos heq2).symm

    -- Step 2: Q ≃* C_q
    have eQ : ↥(↑Q : Subgroup G) ≃* CyclicGroup q :=
      Classical.choice (prime_classification (n := q) h_Q_card)

    -- K is isomorphic to C_4 or C_2 x C_2
    haveI : Fact (Nat.Prime 2) := by decide
    rcases (p_squared_classification (p := 2) hK_card) with h_K_C4 | h_K_C2C2
    · -- case h_K_C4 : Nonempty (↥K ≃* CyclicGroup 4)
      simp only [Nat.reducePow] at h_K_C4
      haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
      haveI : IsCyclic ↥(↑Q : Subgroup G) := (MulEquiv.isCyclic eQ).mpr inferInstance
      haveI : IsCyclic ↥K := (MulEquiv.isCyclic h_K_C4.some).mpr inferInstance
      -- Apply classify_sdp directly to Q ⋊_φ K
      obtain ⟨r, hr_iso, _⟩ :=
        classify_sdp (p := 2) (q := q) (by omega) (by omega) 2 1
          (by norm_num) (by norm_num)
          (hN := h_Q_card.trans (pow_one q).symm)
          (hK := hK_card.trans (by norm_num : (4 : ℕ) = 2 ^ 2))
          φ
      -- (q - 1).factorization 2 = 1 since q ≡ 3 (mod 4)
      have h_vp_eq_1 : (q - 1).factorization 2 = 1 :=
        factorization_two_of_prime_three_mod_four h_3_mod_4
      have h_r01 : r.val = 0 ∨ r.val = 1 := by
        have h := r.isLt
        have : min 2 ((q - 1).factorization 2) = 1 := by simp [h_vp_eq_1]
        omega
      have h4q : Nat.Coprime 4 q :=
        ((by norm_num : (2 : ℕ).Prime).coprime_of_ne h_q_prime.out (by omega)).pow_left 2
      cases h_r01 with
      | inl hr0 =>
        -- r = 0: canonicalAction 0 is trivial → G ≃* C_{4q}
        obtain ⟨e⟩ := hr_iso
        have h_trivial :
            canonicalAction 2 q 1 2 (by omega) (by omega) Nat.one_pos r.val
              (Nat.lt_succ_iff.mp r.isLt) = 1 :=
          eq_one_of_range_card_one (by
            have := canonicalAction_range_card 2 q 1 2 r.val (by omega) (by omega) Nat.one_pos
              (Nat.lt_succ_iff.mp r.isLt)
            rw [this, hr0, pow_zero])
        have : Nonempty (G ≃* CyclicGroup (4 * q)) :=
          ⟨h_iso_g_q_k.symm.trans (e.trans
            ((SemidirectProduct.mulEquivOfTrivialAction h_trivial).trans
              (show CyclicGroup (q ^ 1) × CyclicGroup (2 ^ 2) ≃* CyclicGroup (4 * q) from
                ((_cyclicGroup_pow_one_equiv (q := q)).symm.prodCongr
                    (MulEquiv.refl (CyclicGroup (2 ^ 2)))).trans
                  (MulEquiv.prodComm.trans
                    (CyclicGroup.prodMulEquiv (m := 2 ^ 2) (n := q) (by simpa using h4q))))))⟩
        tauto
      | inr hr1 =>
        -- r = 1: G ≃* C_q ⋊_{canonicalC4OnCqAction} C_4
        obtain ⟨e⟩ := hr_iso
        have : Nonempty (G ≃* SemidirectProduct (CyclicGroup q) (CyclicGroup 4)
                (canonicalC4OnCqAction h_ge_3)) :=
          ⟨h_iso_g_q_k.symm.trans (e.trans
            (show SemidirectProduct (CyclicGroup (q ^ 1)) (CyclicGroup (2 ^ 2))
                    (canonicalAction 2 q 1 2 (by omega) (by omega) Nat.one_pos r.val
                      (Nat.lt_succ_iff.mp r.isLt)) ≃*
                  SemidirectProduct (CyclicGroup q) (CyclicGroup 4) (canonicalC4OnCqAction h_ge_3) by
              obtain ⟨rv, rlt⟩ := r
              simp only [Fin.val_mk] at hr1 ⊢
              subst hr1
              exact canonicalAction_one_iso_canonicalC4OnCqAction h_ge_3))⟩
        tauto
    · -- case h_K_C2C2 : Nonempty (↥K ≃* CyclicGroup 2 × CyclicGroup 2)
      by_cases h_phi_triv : φ = 1
      · -- φ trivial: G ≃* Q × K ≃* C_q × (C_2 × C_2) ≃* (C_2 × C_2) × C_q ≃* C_2 × C_2 × C_q
        have : Nonempty (G ≃* CyclicGroup 2 × CyclicGroup 2 × CyclicGroup q) := by
          refine ⟨?_⟩
          have h_sdp_prod : Q ⋊[φ] ↥K ≃* Q × ↥K :=
            SemidirectProduct.mulEquivOfTrivialAction h_phi_triv
          -- G ≃* ↥↑Q ⋊[φ] ↥K ≃* ↥↑Q × ↥K ≃* C_q × (C_2 × C_2) ≃* (C_2 × C_2) × C_q ≃* C_2 × C_2 × C_q
          exact h_iso_g_q_k.symm.trans
            (h_sdp_prod.trans
              ((eQ.prodCongr h_K_C2C2.some).trans
                (MulEquiv.prodComm.trans MulEquiv.prodAssoc)))
        tauto
      · -- φ nontrivial: transport to φ' : C_2 × C_2 →* Aut(C_q), show |Im(φ')| = 2
        -- (|Im| | gcd(4, q-1) = 2 and |Im| > 1 since φ' ≠ 1), then WIP
        let eK := h_K_C2C2.some
        let φ' : CyclicGroup 2 × CyclicGroup 2 →* MulAut (CyclicGroup q) :=
          ((MulAut.congr eQ).toMonoidHom).comp (φ.comp eK.symm.toMonoidHom)
        have h_sdp_congr :
            ↥(↑Q : Subgroup G) ⋊[φ] ↥K ≃*
              SemidirectProduct (CyclicGroup q) (CyclicGroup 2 × CyclicGroup 2) φ' :=
          SemidirectProduct.congr' (φ₁ := φ) (fn := eQ) (fg := eK)
        -- φ' ≠ 1 since φ ≠ 1
        have hφ'_ne : φ' ≠ 1 := by
          intro h_eq
          apply h_phi_triv
          refine MonoidHom.ext fun k => ?_
          have h1 : φ' (eK k) = 1 := by rw [h_eq]; simp
          have h2 : φ' (eK k) = (MulAut.congr eQ) (φ k) := by
            show ((MulAut.congr eQ).toMonoidHom).comp (φ.comp eK.symm.toMonoidHom) (eK k) = _
            simp [MulEquiv.symm_apply_apply]
          rw [h2] at h1
          exact (MulEquiv.map_eq_one_iff (MulAut.congr eQ)).mp h1
        -- |Aut(C_q)| = q - 1
        have h_aut_card : Nat.card (MulAut (CyclicGroup q)) = q - 1 := by
          have h_aut_iso : MulAut (CyclicGroup q) ≃* (ZMod q)ˣ := by
            have h := IsCyclic.mulAutMulEquiv (CyclicGroup q)
            rwa [card_cyclicGroup] at h
          rw [Nat.card_congr h_aut_iso.toEquiv, Nat.card_eq_fintype_card,
              ZMod.card_units_eq_totient, Nat.totient_prime h_q_prime.out]
        -- |Im(φ')| | gcd(|C_2 × C_2|, |Aut(C_q)|) = gcd(4, q-1) = 2
        have h_range_dvd_2 : Nat.card φ'.range ∣ 2 :=
          calc Nat.card φ'.range
              ∣ Nat.gcd (Nat.card (CyclicGroup 2 × CyclicGroup 2))
                         (Nat.card (MulAut (CyclicGroup q))) :=
                MonoidHom.card_range_dvd_gcd φ'
            _ = Nat.gcd 4 (q - 1) := by
                have h1 : Nat.card (CyclicGroup 2 × CyclicGroup 2) = 4 := by
                  rw [Nat.card_prod, card_cyclicGroup]
                rw [h1]; rw [h_aut_card]
            _ = 2 := gcd_four_of_prime_three_mod_four h_3_mod_4
        -- |Im(φ')| = 2 (since > 1 as φ' ≠ 1, and ≤ 2 from above)
        have h_range_card : Nat.card φ'.range = 2 := by
          have h_pos : 0 < Nat.card φ'.range := Nat.card_pos
          have h_ne_1 : Nat.card φ'.range ≠ 1 :=
            fun h => hφ'_ne (eq_one_of_range_card_one h)
          have h_le_2 : Nat.card φ'.range ≤ 2 :=
            Nat.le_of_dvd (by norm_num) h_range_dvd_2
          omega
        -- WIP: this is the nontrivial C_q ⋊ (C_2 × C_2) case; the required
        -- isomorphism lemmas (semidirectProduct_CpCp_iso and its dependencies)
        -- have outstanding sorries and are left for future work.
        sorry
