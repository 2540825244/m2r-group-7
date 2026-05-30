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

/-- Shared core for the canonical `C_4 →* Aut(C_q)` actions, parametrised by image-order
    exponent `r`. -/
private noncomputable def _canonicalC4OnCqAction
    {q : ℕ} [hq : Fact q.Prime] (h_q_ne_2 : q ≠ 2)
    (r : ℕ) (hr : r ≤ min 2 ((q - 1).factorization 2)) :
    CyclicGroup 4 →* MulAut (CyclicGroup q) :=
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  ((MulAut.congr (_cyclicGroup_pow_one_equiv (q := q))).symm.toMonoidHom).comp
    (canonicalAction 2 q 1 2 (by omega) h_q_ne_2 Nat.one_pos r hr)

/-- The canonical nontrivial action `C_4 →* Aut(C_q)` for q odd prime (image order 2). -/
noncomputable def canonicalC4OnCqAction
    {q : ℕ} [hq : Fact q.Prime] (h_q_ne_2 : q ≠ 2) :
    CyclicGroup 4 →* MulAut (CyclicGroup q) :=
  _canonicalC4OnCqAction h_q_ne_2 1 (one_le_min_two_factorization_two h_q_ne_2)

/-- The canonical action `C_4 →* Aut(C_q)` of image order 4, for q ≡ 1 (mod 4), q > 3. -/
noncomputable def canonicalC4OnCqAction_r2
    {q : ℕ} [hq : Fact q.Prime] (h_1_mod_4 : q ≡ 1 [MOD 4]) :
    CyclicGroup 4 →* MulAut (CyclicGroup q) :=
  _canonicalC4OnCqAction (by simp only [Nat.ModEq] at h_1_mod_4; omega) 2
    (two_le_min_two_factorization_two_of_one_mod_four h_1_mod_4)

/-- The canonical nontrivial action `C_2 × C_2 →* Aut(C_q)` for q odd prime.
    This is `canonicalAction 2 q 1 1 _ _ _ 1 _` (image of order `2^1 = 2`), bridged
    from `CyclicGroup (q^1)` to `CyclicGroup q`, precomposed with projection to the
    first factor. Used as the canonical reference action for the
    `C_q ⋊ (C_2 × C_2)` case (`Dih_q × C_2`). -/
noncomputable def canonicalC2C2OnCqAction
    {q : ℕ} [hq : Fact q.Prime] (h_q_ne_2 : q ≠ 2) :
    CyclicGroup 2 × CyclicGroup 2 →* MulAut (CyclicGroup q) :=
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  (((MulAut.congr (_cyclicGroup_pow_one_equiv (q := q))).symm.toMonoidHom).comp
      (canonicalAction 2 q 1 1 (by omega) h_q_ne_2 Nat.one_pos 1
        (by have := one_le_min_two_factorization_two h_q_ne_2; omega))).comp
    (MonoidHom.fst (CyclicGroup 2) (CyclicGroup 2))

/-- Shared bridge: `C_{q^1} ⋊_{canonicalAction r} C_{2^2} ≃* C_q ⋊_{_canonicalC4OnCqAction r} C_4`.
    Factors out the common proof for `r = 1` and `r = 2`. -/
private noncomputable def _canonicalAction_r_iso_C4OnCqAction
    {q : ℕ} [hq : Fact q.Prime] (h_q_ne_2 : q ≠ 2)
    {r : ℕ} (hr : r ≤ min 2 ((q - 1).factorization 2)) :
    SemidirectProduct (CyclicGroup (q ^ 1)) (CyclicGroup (2 ^ 2))
      (canonicalAction 2 q 1 2 (by omega) h_q_ne_2 Nat.one_pos r hr) ≃*
    SemidirectProduct (CyclicGroup q) (CyclicGroup 4)
      (_canonicalC4OnCqAction h_q_ne_2 r hr) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h_action_eq :
      (MulAut.congr (_cyclicGroup_pow_one_equiv (q := q))).toMonoidHom.comp
          ((_canonicalC4OnCqAction h_q_ne_2 r hr).comp (MulEquiv.refl (CyclicGroup 4)).symm) =
        canonicalAction 2 q 1 2 (by omega) h_q_ne_2 Nat.one_pos r hr := by
    ext k
    simp [_canonicalC4OnCqAction]
  exact (h_action_eq ▸ SemidirectProduct.congr'
    (φ₁ := _canonicalC4OnCqAction h_q_ne_2 r hr)
    (fn := _cyclicGroup_pow_one_equiv (q := q)) (fg := MulEquiv.refl _)).symm

private noncomputable def canonicalAction_one_iso_canonicalC4OnCqAction
    {q : ℕ} [hq : Fact q.Prime] (h_q_ne_2 : q ≠ 2) :
    SemidirectProduct (CyclicGroup (q ^ 1)) (CyclicGroup (2 ^ 2))
      (canonicalAction 2 q 1 2 (by omega) h_q_ne_2 Nat.one_pos 1
        (one_le_min_two_factorization_two h_q_ne_2)) ≃*
    SemidirectProduct (CyclicGroup q) (CyclicGroup 4) (canonicalC4OnCqAction h_q_ne_2) :=
  _canonicalAction_r_iso_C4OnCqAction h_q_ne_2 (one_le_min_two_factorization_two h_q_ne_2)

private noncomputable def canonicalAction_two_iso_canonicalC4OnCqAction_r2
    {q : ℕ} [hq : Fact q.Prime] (h_1_mod_4 : q ≡ 1 [MOD 4]) :
    SemidirectProduct (CyclicGroup (q ^ 1)) (CyclicGroup (2 ^ 2))
      (canonicalAction 2 q 1 2 (by simp only [Nat.ModEq] at h_1_mod_4; omega)
          (by simp only [Nat.ModEq] at h_1_mod_4; omega) Nat.one_pos 2
        (two_le_min_two_factorization_two_of_one_mod_four h_1_mod_4)) ≃*
    SemidirectProduct (CyclicGroup q) (CyclicGroup 4)
      (canonicalC4OnCqAction_r2 h_1_mod_4) :=
  _canonicalAction_r_iso_C4OnCqAction (by simp only [Nat.ModEq] at h_1_mod_4; omega)
    (two_le_min_two_factorization_two_of_one_mod_four h_1_mod_4)

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
                         (canonicalC4OnCqAction (by omega : q ≠ 2)))
      ∨ (∃ h_1_mod_4 : q ≡ 1 [MOD 4],
            Nonempty (G ≃* SemidirectProduct (CyclicGroup q) (CyclicGroup 4)
                            (canonicalC4OnCqAction_r2 h_1_mod_4)))
      ∨ Nonempty (G ≃* SemidirectProduct (CyclicGroup q) (CyclicGroup 2 × CyclicGroup 2)
                         (canonicalC2C2OnCqAction (by omega : q ≠ 2))) := by

  -- G is finite
  haveI : Finite G := by
    apply Nat.finite_of_card_ne_zero
    rw [h]
    have q_ne : q ≠ 0 := Nat.Prime.ne_zero h_q_prime.elim
    simp; tauto

  let n_2 := Nat.card (Sylow 2 G)
  let n_q := Nat.card (Sylow q G)

  have n_2_or_n_q_one : n_2 = 1 ∨ n_q = 1 := p2q_group_has_normal_sylow_subgroup G (by aesop) h

  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rcases n_2_or_n_q_one with h_n2_1 | h_nq_1
  · -- case h_np1 : n_p = 1
    let P : Sylow 2 G := default

    -- Enough to synthesize instance of type class (↑P).Normal
    -- for Subgroup.exists_right_complement'_of_coprime
    haveI : Subsingleton (Sylow 2 G) :=
      (Nat.card_eq_one_iff_unique.mp h_n2_1).1

    have h_card_form : Nat.card G = 2 ^ 2 * q ^ 1 := by aesop
    have h_p_p2 : Nat.card ↥(P : Subgroup G) = 4 := by
      exact sylow_card_eq (by aesop) h_card_form P

    -- Index of Sylow p-group is q
    have h_p_idx_q : ∀ P : Sylow 2 G, (↑P : Subgroup G).index = q := by
      intro P
      simpa using sylow_index_eq (by aesop) h_card_form P

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
    have h4q : Nat.Coprime 4 q :=
      ((by norm_num : (2 : ℕ).Prime).coprime_of_ne h_q_prime.out (by omega)).pow_left 2
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

    have h_card_form : Nat.card G = q ^ 1 * 2 ^ 2 := by rw [pow_one, h]; ring
    have h_Q_card : Nat.card ↥(Q : Subgroup G) = q := by
      have := sylow_card_eq (Ne.symm (by aesop : (2 : ℕ) ≠ q)) h_card_form Q
      simpa using this

    -- Index of Sylow q-group is 4
    have h_Q_idx_4 : ∀ Q : Sylow q G, (↑Q : Subgroup G).index = 4 := by
      intro Q
      have := sylow_index_eq (Ne.symm (by aesop : (2 : ℕ) ≠ q)) h_card_form Q
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
    rcases (p_squared_classification (p := 2) hK_card) with h_K_C4 | h_K_C2C2
    · -- case h_K_C4 : Nonempty (↥K ≃* CyclicGroup 4)
      simp only [Nat.reducePow] at h_K_C4
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
                (canonicalC4OnCqAction (by omega : q ≠ 2))) :=
          ⟨h_iso_g_q_k.symm.trans (e.trans
            (show SemidirectProduct (CyclicGroup (q ^ 1)) (CyclicGroup (2 ^ 2))
                    (canonicalAction 2 q 1 2 (by omega) (by omega) Nat.one_pos r.val
                      (Nat.lt_succ_iff.mp r.isLt)) ≃*
                  SemidirectProduct (CyclicGroup q) (CyclicGroup 4)
                    (canonicalC4OnCqAction (by omega : q ≠ 2)) by
              obtain ⟨rv, rlt⟩ := r
              simp only [Fin.val_mk] at hr1 ⊢
              subst hr1
              exact canonicalAction_one_iso_canonicalC4OnCqAction (by omega : q ≠ 2)))⟩
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
            Nat.card (canonicalC2C2OnCqAction (q := q) (by omega : q ≠ 2)).range = 2 := by
          set f_inner := canonicalAction 2 q 1 1 (by omega) (by omega) Nat.one_pos 1
            (by have := one_le_min_two_factorization_two (by omega : q ≠ 2); omega) with hf_inner
          have h_inner_range : Nat.card f_inner.range = 2 := by
            simpa using canonicalAction_range_card 2 q 1 1 1 (by omega) (by omega) Nat.one_pos
              (by have := one_le_min_two_factorization_two (by omega : q ≠ 2); omega)
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
        have h_canon_ne : canonicalC2C2OnCqAction (q := q) (by omega : q ≠ 2) ≠ 1 := by
          intro hc
          have := h_canon_range
          rw [hc] at this
          simp at this
        obtain ⟨e_canon_to_phi'⟩ :=
          semidirectProduct_CpCp_iso (p := 2) (q := q)
            (two_dvd_prime_sub_one (by omega : q ≠ 2))
            (canonicalC2C2OnCqAction (by omega : q ≠ 2)) φ'
            h_canon_ne hφ'_ne h_canon_range h_range_card
        have : Nonempty (G ≃* SemidirectProduct (CyclicGroup q) (CyclicGroup 2 × CyclicGroup 2)
                                 (canonicalC2C2OnCqAction (by omega : q ≠ 2))) :=
          ⟨h_iso_g_q_k.symm.trans (h_sdp_congr.trans e_canon_to_phi'.symm)⟩
        tauto

/-! ## The q = 3 case: groups of order 12

When `q = 3`, the proof of `classification_4q` no longer applies directly because
`gcd(q, |Aut(C_2 × C_2)|) = gcd(3, 6) = 3`, so the action of the Sylow `q`-subgroup
on a `C_2 × C_2` Sylow `2`-subgroup can be non-trivial. This yields a sixth
isomorphism class: `(C_2 × C_2) ⋊ C_3 ≃ A_4`. -/

private instance instFactPrimeThree : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The order-3 cyclic shift automorphism `(x, y) ↦ (x * y, x)` of
    `CyclicGroup 2 × CyclicGroup 2`. Together with its square and the identity
    this generates the unique Sylow-3 subgroup (= `A_3`) of
    `MulAut (CyclicGroup 2 × CyclicGroup 2) ≃ S_3`. -/
noncomputable def c2c2OrderThreeAut :
    MulAut (CyclicGroup 2 × CyclicGroup 2) where
  toFun p := (p.1 * p.2, p.1)
  invFun p := (p.2, p.1 * p.2)
  left_inv := by
    rintro ⟨x, y⟩
    have hx2 : x * x = 1 := by
      have h := pow_card_eq_one' (G := CyclicGroup 2) (x := x)
      rwa [card_cyclicGroup, sq] at h
    refine Prod.ext rfl ?_
    show (x * y) * x = y
    rw [mul_assoc, mul_comm y x, ← mul_assoc, hx2, one_mul]
  right_inv := by
    rintro ⟨x, y⟩
    have hy2 : y * y = 1 := by
      have h := pow_card_eq_one' (G := CyclicGroup 2) (x := y)
      rwa [card_cyclicGroup, sq] at h
    refine Prod.ext ?_ rfl
    show y * (x * y) = x
    rw [mul_comm y (x * y), mul_assoc, hy2, mul_one]
  map_mul' := by
    rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩
    refine Prod.ext ?_ rfl
    show (x₁ * x₂) * (y₁ * y₂) = (x₁ * y₁) * (x₂ * y₂)
    rw [mul_mul_mul_comm]

/-- `c2c2OrderThreeAut` has order 3. -/
lemma orderOf_c2c2OrderThreeAut : orderOf c2c2OrderThreeAut = 3 := by
  haveI : Fact (Nat.Prime 3) := instFactPrimeThree
  have hsq : ∀ x : CyclicGroup 2, x * x = 1 := fun x => by
    have h := pow_card_eq_one' (G := CyclicGroup 2) (x := x)
    rwa [card_cyclicGroup, sq] at h
  refine orderOf_eq_prime ?_ ?_
  · have hpow : c2c2OrderThreeAut ^ 3 =
        c2c2OrderThreeAut * c2c2OrderThreeAut * c2c2OrderThreeAut := by
      rw [pow_succ, pow_succ, pow_one]
    rw [hpow]
    ext ⟨x, y⟩
    · rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.one_apply]
      change ((x * y) * x) * (x * y) = x
      rw [mul_assoc (x * y) x (x * y), ← mul_assoc x x y, hsq x, one_mul,
          mul_assoc, hsq y, mul_one]
    · rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.one_apply]
      change (x * y) * x = y
      rw [mul_assoc, mul_comm y x, ← mul_assoc, hsq x, one_mul]
  · obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := CyclicGroup 2)
    have hg_ne : g ≠ 1 := by
      intro h
      have htop : (⊤ : Subgroup (CyclicGroup 2)) = ⊥ := by
        rw [← (Subgroup.eq_top_iff' _).mpr hg, h, Subgroup.zpowers_one_eq_bot]
      have h2 : Nat.card (CyclicGroup 2) = 1 := by
        rw [← Subgroup.card_top, htop, Subgroup.card_bot]
      rw [card_cyclicGroup] at h2
      norm_num at h2
    intro h
    have happ : c2c2OrderThreeAut (g, 1) = (1 : MulAut _) (g, 1) := by rw [h]
    rw [MulAut.one_apply] at happ
    have hcompute : c2c2OrderThreeAut (g, 1) = (g * 1, g) := rfl
    rw [hcompute, mul_one] at happ
    have hg_eq_1 : g = 1 := (Prod.mk.injEq _ _ _ _).mp happ |>.2
    exact hg_ne hg_eq_1

/-- The canonical action `C_3 →* MulAut(C_2 × C_2)` of image order 3, sending a
    generator of `C_3` to `c2c2OrderThreeAut`. Used as the canonical reference
    action for the `A_4 ≃ (C_2 × C_2) ⋊ C_3` case in the order-12 classification. -/
noncomputable def canonicalC3OnC2C2Action :
    CyclicGroup 3 →* MulAut (CyclicGroup 2 × CyclicGroup 2) :=
  (MonoidHom.exists_of_generator_and_image
    (IsCyclic.exists_generator (α := CyclicGroup 3)).choose_spec
    (by rw [orderOf_c2c2OrderThreeAut, card_cyclicGroup])).choose

/-- The canonical action sends the chosen generator of `C_3` to
    `c2c2OrderThreeAut`. -/
lemma canonicalC3OnC2C2Action_generator :
    canonicalC3OnC2C2Action (IsCyclic.exists_generator (α := CyclicGroup 3)).choose
      = c2c2OrderThreeAut :=
  (MonoidHom.exists_of_generator_and_image
    (IsCyclic.exists_generator (α := CyclicGroup 3)).choose_spec
    (by rw [orderOf_c2c2OrderThreeAut, card_cyclicGroup])).choose_spec

/-- `canonicalC3OnC2C2Action` has image of cardinality 3. -/
lemma canonicalC3OnC2C2Action_range_card :
    Nat.card canonicalC3OnC2C2Action.range = 3 := by
  have hg : ∀ x : CyclicGroup 3,
      x ∈ Subgroup.zpowers (IsCyclic.exists_generator (α := CyclicGroup 3)).choose :=
    (IsCyclic.exists_generator (α := CyclicGroup 3)).choose_spec
  have hrange : canonicalC3OnC2C2Action.range = Subgroup.zpowers c2c2OrderThreeAut := by
    rw [MonoidHom.range_eq_map, ← (Subgroup.eq_top_iff' _).mpr hg,
        MonoidHom.map_zpowers, canonicalC3OnC2C2Action_generator]
  rw [hrange, Nat.card_zpowers, orderOf_c2c2OrderThreeAut]

/-- Any two non-trivial homomorphisms `C_3 → MulAut(C_2 × C_2)` whose images both
    have order 3 give isomorphic semidirect products. The key fact is that the
    target `Aut(C_2 × C_2) ≃ S_3` has a unique subgroup of order 3 (the Sylow-3
    subgroup is normal, namely `A_3`). -/
theorem semidirectProduct_C3_on_C2C2_iso
    (f_1 f_2 : CyclicGroup 3 →* MulAut (CyclicGroup 2 × CyclicGroup 2))
    (hf1_range : Nat.card f_1.range = 3) (hf2_range : Nat.card f_2.range = 3) :
    Nonempty (SemidirectProduct (CyclicGroup 2 × CyclicGroup 2) (CyclicGroup 3) f_1 ≃*
              SemidirectProduct (CyclicGroup 2 × CyclicGroup 2) (CyclicGroup 3) f_2) := by
  haveI : Fact (Nat.Prime 3) := instFactPrimeThree
  -- Aut(C_2 × C_2) ≃ S_3 has order 6.
  have h_aut_dih : Nonempty (MulAut (CyclicGroup 2 × CyclicGroup 2) ≃* DihedralGroup 3) := by
    obtain ⟨e2⟩ := aut_of_CpCp 2
    exact ⟨e2.trans GL2F2_isoS3⟩
  have h_dih_3_card : Nat.card (DihedralGroup 3) = 6 := by aesop
  have h_aut_card : Nat.card (MulAut (CyclicGroup 2 × CyclicGroup 2)) = 6 :=
    h_aut_dih.elim fun e => (Nat.card_congr e.toEquiv).trans h_dih_3_card
  haveI : Finite (MulAut (CyclicGroup 2 × CyclicGroup 2)) :=
    Nat.finite_of_card_ne_zero (by rw [h_aut_card]; norm_num)
  -- Build the two Sylow 3-subgroups for f_1.range and f_2.range.
  have h_fact_eq : ((Nat.card (MulAut (CyclicGroup 2 × CyclicGroup 2))).factorization 3) = 1 := by
    rw [h_aut_card]
    have h_sq : Squarefree (6 : ℕ) := by
      rw [show (6 : ℕ) = 2 * 3 from rfl]
      exact (Nat.squarefree_mul_iff.mpr ⟨by norm_num, Nat.prime_two.squarefree,
        Nat.prime_three.squarefree⟩)
    exact Nat.factorization_eq_one_of_squarefree h_sq (by norm_num) (by norm_num)
  let S1 : Sylow 3 (MulAut (CyclicGroup 2 × CyclicGroup 2)) :=
    Sylow.ofCard f_1.range (by rw [hf1_range, h_fact_eq, pow_one])
  let S2 : Sylow 3 (MulAut (CyclicGroup 2 × CyclicGroup 2)) :=
    Sylow.ofCard f_2.range (by rw [hf2_range, h_fact_eq, pow_one])
  -- The number of Sylow 3-subgroups of a group of order 6 is 1.
  have h_sylow_subsingleton :
      Subsingleton (Sylow 3 (MulAut (CyclicGroup 2 × CyclicGroup 2))) := by
    have h_card_eq_one :
        Nat.card (Sylow 3 (MulAut (CyclicGroup 2 × CyclicGroup 2))) = 1 := by
      have h_dvd : Nat.card (Sylow 3 (MulAut (CyclicGroup 2 × CyclicGroup 2))) ∣
          (S1 : Subgroup (MulAut (CyclicGroup 2 × CyclicGroup 2))).index :=
        Sylow.card_dvd_index S1
      have h_idx : (S1 : Subgroup (MulAut (CyclicGroup 2 × CyclicGroup 2))).index = 2 := by
        have h_mul : (S1 : Subgroup (MulAut (CyclicGroup 2 × CyclicGroup 2))).index *
            Nat.card (S1 : Subgroup (MulAut (CyclicGroup 2 × CyclicGroup 2))) =
            Nat.card (MulAut (CyclicGroup 2 × CyclicGroup 2)) :=
          Subgroup.index_mul_card _
        have h_S1_card : Nat.card (S1 : Subgroup (MulAut (CyclicGroup 2 × CyclicGroup 2))) = 3 := by
          change Nat.card f_1.range = 3
          exact hf1_range
        rw [h_aut_card, h_S1_card] at h_mul
        omega
      rw [h_idx] at h_dvd
      have h_mod : Nat.card (Sylow 3 (MulAut (CyclicGroup 2 × CyclicGroup 2))) ≡ 1 [MOD 3] :=
        card_sylow_modEq_one 3 _
      have h_le : Nat.card (Sylow 3 (MulAut (CyclicGroup 2 × CyclicGroup 2))) ≤ 2 :=
        Nat.le_of_dvd (by norm_num) h_dvd
      have h_pos : 0 < Nat.card (Sylow 3 (MulAut (CyclicGroup 2 × CyclicGroup 2))) :=
        Nat.card_pos
      unfold Nat.ModEq at h_mod
      omega
    exact (Nat.card_eq_one_iff_unique.mp h_card_eq_one).1
  -- f_1.range = f_2.range via Sylow uniqueness.
  have h_range_eq : f_1.range = f_2.range := by
    have h_S_eq : S1 = S2 := Subsingleton.elim _ _
    have h_coe :
        (S1 : Subgroup (MulAut (CyclicGroup 2 × CyclicGroup 2))) =
          (S2 : Subgroup (MulAut (CyclicGroup 2 × CyclicGroup 2))) := by
      rw [h_S_eq]
    -- (S1 : Subgroup _) = f_1.range and (S2 : Subgroup _) = f_2.range by Sylow.coe_ofCard
    have h_S1 :
        (S1 : Subgroup (MulAut (CyclicGroup 2 × CyclicGroup 2))) = f_1.range :=
      Sylow.coe_ofCard f_1.range _
    have h_S2 :
        (S2 : Subgroup (MulAut (CyclicGroup 2 × CyclicGroup 2))) = f_2.range :=
      Sylow.coe_ofCard f_2.range _
    rw [← h_S1, ← h_S2]; exact h_coe
  exact semidirectProduct_iso_if_range_eq instFactPrimeThree
    (by rw [card_cyclicGroup, pow_one]) f_1 f_2 h_range_eq

/-- Classification of groups `G` of order 12 (= 4 · 3). There are exactly five
    isomorphism classes:
    1. The cyclic group `C_12`.
    2. The abelian non-cyclic group `C_2 × C_2 × C_3`.
    3. The semidirect product `C_3 ⋊ C_4` (= the dicyclic group `Dic_3`).
    4. The semidirect product `C_3 ⋊ (C_2 × C_2)` (= the dihedral group `D_6`).
    5. The semidirect product `(C_2 × C_2) ⋊ C_3` (= the alternating group `A_4`). -/
theorem classification_12 [Group G] (h : Nat.card G = 12) :
    Nonempty (G ≃* CyclicGroup 12)
    ∨ Nonempty (G ≃* CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 3)
    ∨ Nonempty (G ≃* SemidirectProduct (CyclicGroup 3) (CyclicGroup 4)
                       (canonicalC4OnCqAction (by norm_num : (3 : ℕ) ≠ 2)))
    ∨ Nonempty (G ≃* SemidirectProduct (CyclicGroup 3) (CyclicGroup 2 × CyclicGroup 2)
                       (canonicalC2C2OnCqAction (by norm_num : (3 : ℕ) ≠ 2)))
    ∨ Nonempty (G ≃* SemidirectProduct (CyclicGroup 2 × CyclicGroup 2) (CyclicGroup 3)
                       canonicalC3OnC2C2Action) := by
  haveI : Fact (Nat.Prime 3) := instFactPrimeThree
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  -- G is finite
  haveI : Finite G := by
    apply Nat.finite_of_card_ne_zero
    rw [h]; norm_num

  have h12 : Nat.card G = 2 ^ 2 * 3 := by rw [h]; norm_num

  let n_2 := Nat.card (Sylow 2 G)
  let n_3 := Nat.card (Sylow 3 G)

  have n_2_or_n_3_one : n_2 = 1 ∨ n_3 = 1 :=
    p2q_group_has_normal_sylow_subgroup G (by norm_num) h12

  rcases n_2_or_n_3_one with h_n2_1 | h_n3_1
  · -- Case A: n_2 = 1, Sylow 2-subgroup is normal
    let P : Sylow 2 G := default
    haveI : Subsingleton (Sylow 2 G) :=
      (Nat.card_eq_one_iff_unique.mp h_n2_1).1

    have h_card_form : Nat.card G = 2 ^ 2 * 3 ^ 1 := by rw [h]; norm_num
    have h_p_p2 : Nat.card ↥(P : Subgroup G) = 4 :=
      sylow_card_eq (by norm_num) h_card_form P

    have h_p_idx_q : ∀ P : Sylow 2 G, (↑P : Subgroup G).index = 3 := by
      intro P
      simpa using sylow_index_eq (by norm_num) h_card_form P

    obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime (N := (↑P : Subgroup G)) (by
      rw [h_p_p2, h_p_idx_q]
      decide)

    have h_iso_g_p_k := SemidirectProduct.mulEquivSubgroup hK

    let φ : ↥K →* MulAut ↥(↑P : Subgroup G) :=
        (↑P : Subgroup G).normalizerMonoidHom.comp
          (Subgroup.inclusion (by simp [Subgroup.normalizer_eq_top]))

    have hK_card : Nat.card ↥K = 3 := by
      have h1 : Nat.card G = Nat.card ↥(↑P : Subgroup G) * Nat.card ↥K := by
        have heq := Nat.card_congr h_iso_g_p_k.toEquiv
        rw [SemidirectProduct.card] at heq
        exact heq.symm
      rw [h_p_p2, h] at h1
      omega

    have eK : ↥K ≃* CyclicGroup 3 :=
      Classical.choice (prime_classification (n := 3) hK_card)

    have h4q : Nat.Coprime 4 3 := by decide

    rcases (p_squared_classification (p := 2) h_p_p2) with h_c4 | h_c2_c2
    · -- Subcase A1: P ≃ C_4. Then Aut(P) ≃ C_2, and φ is trivial (gcd(3,2)=1).
      simp at h_c4
      have h_aut_P : MulAut P ≃* CyclicGroup 2 :=
        (MulAut.congr h_c4.some).trans (Classical.choice (aut_of_cyclic_p2 (p := 2)))
      have h_aut_card : Nat.card (MulAut ↥(↑P : Subgroup G)) = 2 :=
        (Nat.card_congr h_aut_P.toEquiv).trans (card_cyclicGroup 2)
      have h_phi_triv : φ = 1 :=
        eq_one_of_coprime_card (by rw [hK_card, h_aut_card]; decide)
      have : Nonempty (G ≃* CyclicGroup 12) := by
        refine ⟨?_⟩
        have h_sdp_prod : P ⋊[φ] ↥K ≃* P × ↥K :=
          SemidirectProduct.mulEquivOfTrivialAction h_phi_triv
        have h_12 : CyclicGroup (4 * 3) ≃* CyclicGroup 12 :=
          mulEquivOfCyclicCardEq (by simp only [card_cyclicGroup])
        exact h_iso_g_p_k.symm.trans
          (h_sdp_prod.trans
            ((h_c4.some.prodCongr eK).trans
              ((CyclicGroup.prodMulEquiv h4q).trans h_12)))
      tauto
    · -- Subcase A2: P ≃ C_2 × C_2. Aut(P) has order 6; here φ may be non-trivial.
      have h_aut_dih : Nonempty (MulAut P ≃* DihedralGroup 3) := by
        obtain ⟨e1⟩ := h_c2_c2
        obtain ⟨e2⟩ := aut_of_CpCp 2
        exact ⟨((MulAut.congr e1).trans e2).trans GL2F2_isoS3⟩
      have h_dih_3_card : Nat.card (DihedralGroup 3) = 6 := by aesop
      have h_mul_aut_p_card : Nat.card (MulAut P) = 6 :=
        h_aut_dih.elim fun e => (Nat.card_congr e.toEquiv).trans h_dih_3_card
      by_cases h_phi_triv : φ = 1
      · -- Trivial action: G ≃ P × K ≃ (C_2 × C_2) × C_3 ≃ C_2 × C_2 × C_3.
        have : Nonempty (G ≃* CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 3) := by
          refine ⟨?_⟩
          have h_sdp_prod : P ⋊[φ] ↥K ≃* P × ↥K :=
            SemidirectProduct.mulEquivOfTrivialAction h_phi_triv
          exact h_iso_g_p_k.symm.trans
            (h_sdp_prod.trans
              ((h_c2_c2.some.prodCongr eK).trans MulEquiv.prodAssoc))
        tauto
      · -- Non-trivial action: transport to canonicalC3OnC2C2Action and produce A_4.
        let eP := h_c2_c2.some
        let φ' : CyclicGroup 3 →* MulAut (CyclicGroup 2 × CyclicGroup 2) :=
          ((MulAut.congr eP).toMonoidHom).comp (φ.comp eK.symm.toMonoidHom)
        have h_sdp_congr :
            ↥(↑P : Subgroup G) ⋊[φ] ↥K ≃*
              SemidirectProduct (CyclicGroup 2 × CyclicGroup 2) (CyclicGroup 3) φ' :=
          SemidirectProduct.congr' (φ₁ := φ) (fn := eP) (fg := eK)
        -- φ' ≠ 1 since φ ≠ 1.
        have hφ'_ne : φ' ≠ 1 := by
          intro h_eq
          apply h_phi_triv
          refine MonoidHom.ext fun k => ?_
          have h1 : φ' (eK k) = 1 := by rw [h_eq]; simp
          have h2 : φ' (eK k) = (MulAut.congr eP) (φ k) := by
            show ((MulAut.congr eP).toMonoidHom).comp (φ.comp eK.symm.toMonoidHom) (eK k) = _
            simp [MulEquiv.symm_apply_apply]
          rw [h2] at h1
          exact (MulEquiv.map_eq_one_iff (MulAut.congr eP)).mp h1
        -- |Im(φ')| divides 3 = |CyclicGroup 3|, |Im(φ')| ≠ 1, so |Im(φ')| = 3.
        have h_range_dvd_3 : Nat.card φ'.range ∣ 3 := by
          have h := Subgroup.card_range_dvd φ'
          rw [card_cyclicGroup] at h
          exact h
        have h_range_card : Nat.card φ'.range = 3 := by
          have h_ne_1 : Nat.card φ'.range ≠ 1 :=
            fun h => hφ'_ne (eq_one_of_range_card_one h)
          have h_pos : 0 < Nat.card φ'.range := Nat.card_pos
          -- divisors of 3 are 1 and 3
          have h3_prime : Nat.Prime 3 := by norm_num
          rcases (Nat.dvd_prime h3_prime).mp h_range_dvd_3 with h1 | h3
          · exact absurd h1 h_ne_1
          · exact h3
        -- Apply semidirectProduct_C3_on_C2C2_iso.
        obtain ⟨e_phi'_to_canon⟩ :=
          semidirectProduct_C3_on_C2C2_iso φ' canonicalC3OnC2C2Action
            h_range_card canonicalC3OnC2C2Action_range_card
        have : Nonempty (G ≃* SemidirectProduct (CyclicGroup 2 × CyclicGroup 2)
                                  (CyclicGroup 3) canonicalC3OnC2C2Action) :=
          ⟨h_iso_g_p_k.symm.trans (h_sdp_congr.trans e_phi'_to_canon)⟩
        tauto
  · -- Case B: n_3 = 1, Sylow 3-subgroup is normal.
    let Q : Sylow 3 G := default
    haveI : Subsingleton (Sylow 3 G) :=
      (Nat.card_eq_one_iff_unique.mp h_n3_1).1

    have h_card_form : Nat.card G = 3 ^ 1 * 2 ^ 2 := by rw [h]; ring
    have h_Q_card : Nat.card ↥(Q : Subgroup G) = 3 := by
      have := sylow_card_eq (by norm_num : (3 : ℕ) ≠ 2) h_card_form Q
      simpa using this

    have h_Q_idx_4 : ∀ Q : Sylow 3 G, (↑Q : Subgroup G).index = 4 := by
      intro Q
      have := sylow_index_eq (by norm_num : (3 : ℕ) ≠ 2) h_card_form Q
      simpa using this

    obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime (N := (↑Q : Subgroup G)) (by
      rw [h_Q_card, h_Q_idx_4]
      decide)

    have h_iso_g_q_k := SemidirectProduct.mulEquivSubgroup hK

    let φ : ↥K →* MulAut ↥(↑Q : Subgroup G) :=
        (↑Q : Subgroup G).normalizerMonoidHom.comp
          (Subgroup.inclusion (by simp [Subgroup.normalizer_eq_top]))

    have hK_card : Nat.card ↥K = 4 := by
      have h1 : Nat.card G = Nat.card ↥(↑Q : Subgroup G) * Nat.card ↥K := by
        have heq := Nat.card_congr h_iso_g_q_k.toEquiv
        rw [SemidirectProduct.card] at heq
        exact heq.symm
      rw [h_Q_card, h] at h1
      omega

    have eQ : ↥(↑Q : Subgroup G) ≃* CyclicGroup 3 :=
      Classical.choice (prime_classification (n := 3) h_Q_card)

    rcases (p_squared_classification (p := 2) hK_card) with h_K_C4 | h_K_C2C2
    · -- Subcase B1: K ≃ C_4. Use classify_sdp. Here r ∈ {0, 1} only.
      simp only [Nat.reducePow] at h_K_C4
      haveI : IsCyclic ↥(↑Q : Subgroup G) := (MulEquiv.isCyclic eQ).mpr inferInstance
      haveI : IsCyclic ↥K := (MulEquiv.isCyclic h_K_C4.some).mpr inferInstance
      obtain ⟨r, hr_iso, _⟩ :=
        classify_sdp (p := 2) (q := 3) (by norm_num) (by norm_num) 2 1
          (by norm_num) (by norm_num)
          (hN := h_Q_card.trans (pow_one 3).symm)
          (hK := hK_card.trans (by norm_num : (4 : ℕ) = 2 ^ 2))
          φ
      -- For q = 3, (3-1).factorization 2 = 1, so min 2 1 = 1, hence r.val ∈ {0, 1}.
      have h_fact : ((3 - 1 : ℕ).factorization 2) = 1 := by
        show ((2 : ℕ).factorization 2) = 1
        rw [Nat.Prime.factorization_self (by norm_num : Nat.Prime 2)]
      have h_r01 : r.val = 0 ∨ r.val = 1 := by
        have h := r.isLt
        have h_min : min 2 ((3 - 1 : ℕ).factorization 2) = 1 := by rw [h_fact]; rfl
        omega
      have h4q : Nat.Coprime 4 3 := by decide
      rcases h_r01 with hr0 | hr1
      · -- r = 0: trivial action → G ≃ C_12.
        obtain ⟨e⟩ := hr_iso
        have h_trivial :
            canonicalAction 2 3 1 2 (by norm_num) (by norm_num) Nat.one_pos r.val
              (Nat.lt_succ_iff.mp r.isLt) = 1 :=
          eq_one_of_range_card_one (by
            have := canonicalAction_range_card 2 3 1 2 r.val (by norm_num) (by norm_num)
              Nat.one_pos (Nat.lt_succ_iff.mp r.isLt)
            rw [this, hr0, pow_zero])
        have h_12 : CyclicGroup (2 ^ 2 * 3) ≃* CyclicGroup 12 :=
          mulEquivOfCyclicCardEq (by simp only [card_cyclicGroup]; norm_num)
        have : Nonempty (G ≃* CyclicGroup 12) :=
          ⟨h_iso_g_q_k.symm.trans (e.trans
            ((SemidirectProduct.mulEquivOfTrivialAction h_trivial).trans
              (show CyclicGroup (3 ^ 1) × CyclicGroup (2 ^ 2) ≃* CyclicGroup 12 from
                ((_cyclicGroup_pow_one_equiv (q := 3)).symm.prodCongr
                    (MulEquiv.refl (CyclicGroup (2 ^ 2)))).trans
                  (MulEquiv.prodComm.trans
                    ((CyclicGroup.prodMulEquiv (m := 2 ^ 2) (n := 3)
                      (by simpa using h4q)).trans h_12)))))⟩
        tauto
      · -- r = 1: G ≃ C_3 ⋊_{canonicalC4OnCqAction} C_4.
        obtain ⟨e⟩ := hr_iso
        have : Nonempty (G ≃* SemidirectProduct (CyclicGroup 3) (CyclicGroup 4)
                (canonicalC4OnCqAction (by norm_num : (3 : ℕ) ≠ 2))) :=
          ⟨h_iso_g_q_k.symm.trans (e.trans
            (show SemidirectProduct (CyclicGroup (3 ^ 1)) (CyclicGroup (2 ^ 2))
                    (canonicalAction 2 3 1 2 (by norm_num) (by norm_num) Nat.one_pos r.val
                      (Nat.lt_succ_iff.mp r.isLt)) ≃*
                  SemidirectProduct (CyclicGroup 3) (CyclicGroup 4)
                    (canonicalC4OnCqAction (by norm_num : (3 : ℕ) ≠ 2)) by
              obtain ⟨rv, rlt⟩ := r
              simp only [Fin.val_mk] at hr1 ⊢
              subst hr1
              exact canonicalAction_one_iso_canonicalC4OnCqAction (by norm_num : (3 : ℕ) ≠ 2)))⟩
        tauto
    · -- Subcase B2: K ≃ C_2 × C_2.
      by_cases h_phi_triv : φ = 1
      · -- Trivial action: G ≃ C_2 × C_2 × C_3.
        have : Nonempty (G ≃* CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 3) := by
          refine ⟨?_⟩
          have h_sdp_prod : Q ⋊[φ] ↥K ≃* Q × ↥K :=
            SemidirectProduct.mulEquivOfTrivialAction h_phi_triv
          exact h_iso_g_q_k.symm.trans
            (h_sdp_prod.trans
              ((eQ.prodCongr h_K_C2C2.some).trans
                (MulEquiv.prodComm.trans MulEquiv.prodAssoc)))
        tauto
      · -- Non-trivial action: transport to canonicalC2C2OnCqAction (the dihedral case).
        let eK := h_K_C2C2.some
        let φ' : CyclicGroup 2 × CyclicGroup 2 →* MulAut (CyclicGroup 3) :=
          ((MulAut.congr eQ).toMonoidHom).comp (φ.comp eK.symm.toMonoidHom)
        have h_sdp_congr :
            ↥(↑Q : Subgroup G) ⋊[φ] ↥K ≃*
              SemidirectProduct (CyclicGroup 3) (CyclicGroup 2 × CyclicGroup 2) φ' :=
          SemidirectProduct.congr' (φ₁ := φ) (fn := eQ) (fg := eK)
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
        have h_range_dvd_2 : Nat.card φ'.range ∣ 2 := range_card_dvd_two_of_C2C2_hom φ'
        have h_range_card : Nat.card φ'.range = 2 := by
          have h_pos : 0 < Nat.card φ'.range := Nat.card_pos
          have h_ne_1 : Nat.card φ'.range ≠ 1 :=
            fun h => hφ'_ne (eq_one_of_range_card_one h)
          have h_le_2 : Nat.card φ'.range ≤ 2 :=
            Nat.le_of_dvd (by norm_num) h_range_dvd_2
          omega
        have h_canon_range :
            Nat.card (canonicalC2C2OnCqAction (q := 3) (by norm_num : (3 : ℕ) ≠ 2)).range = 2 := by
          set f_inner := canonicalAction 2 3 1 1 (by norm_num) (by norm_num) Nat.one_pos 1
            (by have := one_le_min_two_factorization_two (by norm_num : (3 : ℕ) ≠ 2); omega)
            with hf_inner
          have h_inner_range : Nat.card f_inner.range = 2 := by
            simpa using canonicalAction_range_card 2 3 1 1 1 (by norm_num) (by norm_num)
              Nat.one_pos
              (by have := one_le_min_two_factorization_two (by norm_num : (3 : ℕ) ≠ 2); omega)
          set e_aut := (MulAut.congr (_cyclicGroup_pow_one_equiv (q := 3))).symm with he_aut
          have h_card_congr :
              Nat.card (e_aut.toMonoidHom.comp f_inner).range = 2 := by
            rw [MonoidHom.range_comp]
            rw [Nat.card_congr
              (Subgroup.equivMapOfInjective f_inner.range e_aut.toMonoidHom
                e_aut.injective).symm.toEquiv]
            exact h_inner_range
          have h_fst_surj :
              Function.Surjective (MonoidHom.fst (CyclicGroup 2) (CyclicGroup 2)) :=
            fun x => ⟨(x, 1), rfl⟩
          show Nat.card ((e_aut.toMonoidHom.comp f_inner).comp
              (MonoidHom.fst (CyclicGroup 2) (CyclicGroup 2))).range = 2
          rw [MonoidHom.range_comp]
          simpa using h_card_congr
        have h_canon_ne : canonicalC2C2OnCqAction (q := 3) (by norm_num : (3 : ℕ) ≠ 2) ≠ 1 := by
          intro hc
          have := h_canon_range
          rw [hc] at this
          simp at this
        obtain ⟨e_canon_to_phi'⟩ :=
          semidirectProduct_CpCp_iso (p := 2) (q := 3)
            (two_dvd_prime_sub_one (by norm_num : (3 : ℕ) ≠ 2))
            (canonicalC2C2OnCqAction (by norm_num : (3 : ℕ) ≠ 2)) φ'
            h_canon_ne hφ'_ne h_canon_range h_range_card
        have : Nonempty (G ≃* SemidirectProduct (CyclicGroup 3) (CyclicGroup 2 × CyclicGroup 2)
                                 (canonicalC2C2OnCqAction (by norm_num : (3 : ℕ) ≠ 2))) :=
          ⟨h_iso_g_q_k.symm.trans (h_sdp_congr.trans e_canon_to_phi'.symm)⟩
        tauto
