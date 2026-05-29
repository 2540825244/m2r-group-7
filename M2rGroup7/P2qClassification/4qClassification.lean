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
  haveI : NeZero (q ^ 1) := ⟨by rw [pow_one]; exact hq.out.ne_zero⟩
  mulEquivOfCyclicCardEq (by simp only [card_cyclicGroup, pow_one])

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

/-- The canonical action `C_4 →* Aut(C_q)` of image order 4, for q ≡ 1 (mod 4), q > 3.
    This is `canonicalAction 2 q 1 2 _ _ _ 2 _`, post-composed with the cyclic-group
    identification `CyclicGroup q ≃ CyclicGroup (q^1)`. Its image is the unique subgroup
    of order 4 in `Aut(C_q)` (which exists precisely because 4 ∣ q − 1). -/
noncomputable def canonicalC4OnCqAction_r2
    {q : ℕ} [hq : Fact q.Prime] (h_1_mod_4 : q ≡ 1 [MOD 4]) :
    CyclicGroup 4 →* MulAut (CyclicGroup q) :=
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  ((MulAut.congr (_cyclicGroup_pow_one_equiv (q := q))).symm.toMonoidHom).comp
    (canonicalAction 2 q 1 2 (by omega) (by omega) Nat.one_pos 2
      (two_le_min_two_factorization_two_of_one_mod_four h_1_mod_4))

/-- The canonical nontrivial action `C_2 × C_2 →* Aut(C_q)` for q > 3 prime.
    This is `canonicalAction 2 q 1 1 _ _ _ 1 _` (image of order `2^1 = 2`), bridged
    from `CyclicGroup (q^1)` to `CyclicGroup q`, precomposed with projection to the
    first factor. Used as the canonical reference action for the
    `C_q ⋊ (C_2 × C_2)` case (`Dih_q × C_2`). -/
noncomputable def canonicalC2C2OnCqAction
    {q : ℕ} [hq : Fact q.Prime] (h_q_gt_3 : q > 3) :
    CyclicGroup 2 × CyclicGroup 2 →* MulAut (CyclicGroup q) :=
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  (((MulAut.congr (_cyclicGroup_pow_one_equiv (q := q))).symm.toMonoidHom).comp
      (canonicalAction 2 q 1 1 (by omega) (by omega) Nat.one_pos 1
        (by have := one_le_min_two_factorization_two h_q_gt_3; omega))).comp
    (MonoidHom.fst (CyclicGroup 2) (CyclicGroup 2))

/-- The canonical semidirect product `C_{q^1} ⋊_{canonicalAction 1} C_{2^2}` is isomorphic
    to `C_q ⋊_{canonicalC4OnCqAction} C_4`.

    The "back bridge": `classify_sdp` (and `classify_Cqn_rtimes_Cpm`) is stated in terms of
    `CyclicGroup (q^n)` and `CyclicGroup (p^m)`, while the conclusion of `classification_4q`
    is in terms of `CyclicGroup q` and `CyclicGroup 4`. The `q ↔ q^1` direction is the
    structural mismatch (`CyclicGroup q` and `CyclicGroup (q^1)` are not definitionally equal),
    so a `MulEquiv` is genuinely needed; the `4 ↔ 2^2` direction is definitional. -/
private noncomputable def canonicalAction_one_iso_canonicalC4OnCqAction
    {q : ℕ} [hq : Fact q.Prime] (h_ge_3 : q > 3) :
    SemidirectProduct (CyclicGroup (q ^ 1)) (CyclicGroup (2 ^ 2))
      (canonicalAction 2 q 1 2 (by omega) (by omega) Nat.one_pos 1
        (one_le_min_two_factorization_two h_ge_3)) ≃*
    SemidirectProduct (CyclicGroup q) (CyclicGroup 4) (canonicalC4OnCqAction h_ge_3) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  -- After transporting via `pq_iso : C_q ≃* C_(q^1)`, the action `canonicalC4OnCqAction`
  -- unfolds (definitionally) to `canonicalAction r=1`, by `MulEquiv.apply_symm_apply`.
  have h_action_eq :
      (MulAut.congr (_cyclicGroup_pow_one_equiv (q := q))).toMonoidHom.comp
          ((canonicalC4OnCqAction h_ge_3).comp (MulEquiv.refl (CyclicGroup 4)).symm) =
        canonicalAction 2 q 1 2 (by omega) (by omega) Nat.one_pos 1
          (one_le_min_two_factorization_two h_ge_3) := by
    ext k
    simp [canonicalC4OnCqAction]
  exact (h_action_eq ▸ SemidirectProduct.congr'
    (φ₁ := canonicalC4OnCqAction h_ge_3)
    (fn := _cyclicGroup_pow_one_equiv (q := q)) (fg := MulEquiv.refl _)).symm

/-- Back bridge for r = 2: `C_{q^1} ⋊ C_{2^2}` with canonical r = 2 action is isomorphic to
    `C_q ⋊ C_4` with `canonicalC4OnCqAction_r2`. Same shape as the r = 1 bridge. -/
private noncomputable def canonicalAction_two_iso_canonicalC4OnCqAction_r2
    {q : ℕ} [hq : Fact q.Prime] (h_1_mod_4 : q ≡ 1 [MOD 4]) :
    SemidirectProduct (CyclicGroup (q ^ 1)) (CyclicGroup (2 ^ 2))
      (canonicalAction 2 q 1 2 (by omega) (by omega) Nat.one_pos 2
        (two_le_min_two_factorization_two_of_one_mod_four h_1_mod_4)) ≃*
    SemidirectProduct (CyclicGroup q) (CyclicGroup 4)
      (canonicalC4OnCqAction_r2 h_1_mod_4) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h_action_eq :
      (MulAut.congr (_cyclicGroup_pow_one_equiv (q := q))).toMonoidHom.comp
          ((canonicalC4OnCqAction_r2 h_1_mod_4).comp (MulEquiv.refl (CyclicGroup 4)).symm) =
        canonicalAction 2 q 1 2 (by omega) (by omega) Nat.one_pos 2
          (two_le_min_two_factorization_two_of_one_mod_four h_1_mod_4) := by
    ext k
    simp [canonicalC4OnCqAction_r2]
  exact (h_action_eq ▸ SemidirectProduct.congr'
    (φ₁ := canonicalC4OnCqAction_r2 h_1_mod_4)
    (fn := _cyclicGroup_pow_one_equiv (q := q)) (fg := MulEquiv.refl _)).symm

/-- Classification of groups `G` of order `4q` for q > 3 prime. There are at most
    five isomorphism classes:
    1. The cyclic group `C_{4q}`.
    2. The abelian non-cyclic group `C_2 × C_2 × C_q`.
    3. The semidirect product `C_q ⋊ C_4` with the canonical action of image order 2.
    4. (Only when q ≡ 1 mod 4) The semidirect product `C_q ⋊ C_4` with the canonical
       action of image order 4.
    5. The semidirect product `C_q ⋊ (C_2 × C_2)` with the canonical nontrivial action. -/
theorem classification_4q {q : ℕ} [h_q_prime : Fact q.Prime] [Group G]
    (h_ge_3 : q > 3) (h : Nat.card G = 4 * q)
    : Nonempty (G ≃* CyclicGroup (4 * q))
      ∨ Nonempty (G ≃* CyclicGroup 2 × CyclicGroup 2 × CyclicGroup q)
      ∨ Nonempty (G ≃* SemidirectProduct (CyclicGroup q) (CyclicGroup 4)
                         (canonicalC4OnCqAction h_ge_3))
      ∨ (∃ h_1_mod_4 : q ≡ 1 [MOD 4],
            Nonempty (G ≃* SemidirectProduct (CyclicGroup q) (CyclicGroup 4)
                            (canonicalC4OnCqAction_r2 h_1_mod_4)))
      ∨ Nonempty (G ≃* SemidirectProduct (CyclicGroup q) (CyclicGroup 2 × CyclicGroup 2)
                         (canonicalC2C2OnCqAction h_ge_3)) := by

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
      -- r.val ∈ {0, 1, 2} (since min 2 _ ≤ 2 always)
      have h_r012 : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 := by
        have h := r.isLt
        have h_min_le : min 2 ((q - 1).factorization 2) ≤ 2 := min_le_left _ _
        omega
      have h4q : Nat.Coprime 4 q :=
        ((by norm_num : (2 : ℕ).Prime).coprime_of_ne h_q_prime.out (by omega)).pow_left 2
      rcases h_r012 with hr0 | hr1 | hr2
      · -- r = 0: canonicalAction 0 is trivial → G ≃* C_{4q}
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
      · -- r = 1: G ≃* C_q ⋊_{canonicalC4OnCqAction} C_4
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
      · -- r = 2: forces q ≡ 1 (mod 4), and G ≃* C_q ⋊_{canonicalC4OnCqAction_r2} C_4
        -- Derive q ≡ 1 [MOD 4] from 2 ≤ (q-1).factorization 2.
        have h_vp_ge_2 : 2 ≤ (q - 1).factorization 2 := by
          have h := Nat.lt_succ_iff.mp r.isLt
          have h_min_le_vp : min 2 ((q - 1).factorization 2) ≤ (q - 1).factorization 2 :=
            min_le_right _ _
          omega
        have h_qm1_ne : q - 1 ≠ 0 := by have := h_q_prime.out.one_lt; omega
        have h_4_dvd : (4 : ℕ) ∣ q - 1 := by
          have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two h_qm1_ne).mpr h_vp_ge_2
          simpa [show (2 : ℕ) ^ 2 = 4 by norm_num] using this
        have h_1_mod_4 : q ≡ 1 [MOD 4] := by
          have hq_pos : 0 < q := h_q_prime.out.pos
          unfold Nat.ModEq
          omega
        obtain ⟨e⟩ := hr_iso
        have : Nonempty (G ≃* SemidirectProduct (CyclicGroup q) (CyclicGroup 4)
                (canonicalC4OnCqAction_r2 h_1_mod_4)) :=
          ⟨h_iso_g_q_k.symm.trans (e.trans
            (show SemidirectProduct (CyclicGroup (q ^ 1)) (CyclicGroup (2 ^ 2))
                    (canonicalAction 2 q 1 2 (by omega) (by omega) Nat.one_pos r.val
                      (Nat.lt_succ_iff.mp r.isLt)) ≃*
                  SemidirectProduct (CyclicGroup q) (CyclicGroup 4)
                    (canonicalC4OnCqAction_r2 h_1_mod_4) by
              obtain ⟨rv, rlt⟩ := r
              simp only [Fin.val_mk] at hr2 ⊢
              subst hr2
              exact canonicalAction_two_iso_canonicalC4OnCqAction_r2 h_1_mod_4))⟩
        -- The 4th disjunct is `∃ h_1_mod_4, Nonempty ...`
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h_1_mod_4, this⟩)))
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
        -- |Im(φ')| ∣ 2: every element of φ'.range has order ≤ 2 (since C_2 × C_2
        -- has exponent 2), and φ'.range is cyclic (subgroup of cyclic Aut(C_q)).
        have h_range_dvd_2 : Nat.card φ'.range ∣ 2 := range_card_dvd_two_of_C2C2_hom φ'
        -- |Im(φ')| = 2 (since > 1 as φ' ≠ 1, and ≤ 2 from above)
        have h_range_card : Nat.card φ'.range = 2 := by
          have h_pos : 0 < Nat.card φ'.range := Nat.card_pos
          have h_ne_1 : Nat.card φ'.range ≠ 1 :=
            fun h => hφ'_ne (eq_one_of_range_card_one h)
          have h_le_2 : Nat.card φ'.range ≤ 2 :=
            Nat.le_of_dvd (by norm_num) h_range_dvd_2
          omega
        -- Nontrivial C_q ⋊ (C_2 × C_2): transport to the canonical reference action
        -- via `semidirectProduct_CpCp_iso` (which uses α = 1 in the conjugacy condition).
        have h_canon_range :
            Nat.card (canonicalC2C2OnCqAction (q := q) h_ge_3).range = 2 := by
          haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
          set f_inner := canonicalAction 2 q 1 1 (by omega) (by omega) Nat.one_pos 1
            (by have := one_le_min_two_factorization_two h_ge_3; omega) with hf_inner
          have h_inner_range : Nat.card f_inner.range = 2 := by
            simpa using canonicalAction_range_card 2 q 1 1 1 (by omega) (by omega) Nat.one_pos
              (by have := one_le_min_two_factorization_two h_ge_3; omega)
          -- Post-composition with the MulEquiv `(MulAut.congr _).symm` preserves the range cardinality.
          set e_aut := (MulAut.congr (_cyclicGroup_pow_one_equiv (q := q))).symm with he_aut
          have h_card_congr :
              Nat.card (e_aut.toMonoidHom.comp f_inner).range = 2 := by
            rw [MonoidHom.range_comp]
            rw [Nat.card_congr
              (Subgroup.equivMapOfInjective f_inner.range e_aut.toMonoidHom
                e_aut.injective).symm.toEquiv]
            exact h_inner_range
          -- Precomposition with the surjective `MonoidHom.fst` also preserves the range.
          have h_fst_surj :
              Function.Surjective (MonoidHom.fst (CyclicGroup 2) (CyclicGroup 2)) :=
            fun x => ⟨(x, 1), rfl⟩
          show Nat.card ((e_aut.toMonoidHom.comp f_inner).comp
              (MonoidHom.fst (CyclicGroup 2) (CyclicGroup 2))).range = 2
          rw [MonoidHom.range_comp]
          simpa using h_card_congr
        have h_canon_ne : canonicalC2C2OnCqAction (q := q) h_ge_3 ≠ 1 := by
          intro hc
          have := h_canon_range
          rw [hc] at this
          simp at this
        obtain ⟨e_canon_to_phi'⟩ :=
          semidirectProduct_CpCp_iso (p := 2) (q := q)
            (two_dvd_prime_sub_one (by omega : q ≠ 2))
            (canonicalC2C2OnCqAction h_ge_3) φ'
            h_canon_ne hφ'_ne h_canon_range h_range_card
        have : Nonempty (G ≃* SemidirectProduct (CyclicGroup q) (CyclicGroup 2 × CyclicGroup 2)
                                 (canonicalC2C2OnCqAction h_ge_3)) :=
          ⟨h_iso_g_q_k.symm.trans (h_sdp_congr.trans e_canon_to_phi'.symm)⟩
        tauto
