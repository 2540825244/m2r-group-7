import Mathlib
import «M2rGroup7».Lemmas.SylowUtils
import «M2rGroup7».Lemmas.LinearAlgebraUtils
import «M2rGroup7».Lemmas.GroupTheoryLemmas
import «M2rGroup7».Lemmas.ClassificationUtils
import «M2rGroup7».Lemmas.HomomorphismUtils
import «M2rGroup7».Lemmas.NumberTheoryUtils
import «M2rGroup7».P2qClassification.CycPGroupClassification

/-- Auxiliary: the witness `1 ≤ min 2 ((q - 1).factorization 2)` for q prime, q > 3. -/
private lemma _hr_canonicalC4OnCqAction
    {q : ℕ} [hq : Fact q.Prime] (h_q_gt_3 : q > 3) :
    1 ≤ min 2 ((q - 1).factorization 2) := by
  have h_qm1_ne : q - 1 ≠ 0 := by have := hq.out.one_lt; omega
  have h_dvd : 2 ∣ q - 1 := by
    have hq_odd : Odd q := hq.out.odd_of_ne_two (by omega)
    obtain ⟨k, rfl⟩ := hq_odd; omega
  refine Nat.le_min.mpr ⟨one_le_two, ?_⟩
  rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two h_qm1_ne]
  simpa using h_dvd

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
      (_hr_canonicalC4OnCqAction h_q_gt_3))

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
  have h_mod : (q - 1) % 4 = 2 := by
    have h1 : q % 4 = 3 := h_3_mod_4
    have h2 : q > 0 := hq.out.pos
    omega
  -- gcd(4, q-1) = 2 since (q-1) % 4 = 2.
  have h_gcd : Nat.gcd 4 (q - 1) = 2 := by
    have h2_dvd_gcd : 2 ∣ Nat.gcd 4 (q - 1) :=
      Nat.dvd_gcd (by norm_num) (by omega)
    have h_gcd_dvd_4 : Nat.gcd 4 (q - 1) ∣ 4 := Nat.gcd_dvd_left _ _
    have h_not_4_dvd : ¬ (4 ∣ q - 1) := by
      intro h_dvd; rw [Nat.dvd_iff_mod_eq_zero] at h_dvd; omega
    have h_gcd_dvd_qm1 : Nat.gcd 4 (q - 1) ∣ q - 1 := Nat.gcd_dvd_right _ _
    have h_pos : 0 < Nat.gcd 4 (q - 1) :=
      Nat.gcd_pos_of_pos_left _ (by norm_num)
    have h_le : Nat.gcd 4 (q - 1) ≤ 4 := Nat.le_of_dvd (by norm_num) h_gcd_dvd_4
    interval_cases Nat.gcd 4 (q - 1) <;> first
      | rfl
      | (exfalso; exact absurd h_gcd_dvd_4 (by decide))
      | (exfalso; exact h_not_4_dvd h_gcd_dvd_qm1)
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
      (Subgroup.eq_bot_iff_card).mpr h_card_one
    exact h_range_ne_bot h_range_bot
  -- Combine: card divides 2 and is > 1, so = 2 = 2^1.
  have h_le_2 : Nat.card f.range ≤ 2 := Nat.le_of_dvd (by norm_num) h_dvd_2
  interval_cases (Nat.card f.range)
  rfl

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
      simp at h_K_C4
      by_cases h_phi_triv : φ = 1
      · -- φ trivial: G ≃* Q × K ≃* C_q × C_4 ≃* C_4 × C_q ≃* C_{4q}
        have : Nonempty (G ≃* CyclicGroup (4 * q)) := by
          refine ⟨?_⟩
          have h_sdp_prod : Q ⋊[φ] ↥K ≃* Q × ↥K :=
            SemidirectProduct.mulEquivOfTrivialAction h_phi_triv
          have h4q : Nat.Coprime 4 q :=
            ((by norm_num : (2 : ℕ).Prime).coprime_of_ne h_q_prime.out (by omega)).pow_left 2
          -- G ≃* ↥↑Q ⋊[φ] ↥K ≃* ↥↑Q × ↥K ≃* C_q × C_4 ≃* C_4 × C_q ≃* C_{4q}
          exact h_iso_g_q_k.symm.trans
            (h_sdp_prod.trans
              ((eQ.prodCongr h_K_C4.some).trans
                (MulEquiv.prodComm.trans (CyclicGroup.prodMulEquiv h4q))))
        tauto
      · -- φ nontrivial: transport φ to f : C_4 →* Aut(C_q) and apply
        -- classify_Cqn_rtimes_Cpm_exists with p=2, m=2, n=1, r=1.
        let eK := h_K_C4.some
        let f : CyclicGroup 4 →* MulAut (CyclicGroup q) :=
          ((MulAut.congr eQ).toMonoidHom).comp (φ.comp eK.symm.toMonoidHom)
        have h_sdp_congr :
            (Q : Subgroup G) ⋊[φ] ↥K ≃*
              SemidirectProduct (CyclicGroup q) (CyclicGroup 4) f :=
          SemidirectProduct.congr' (φ₁ := φ) (fn := eQ) (fg := eK)
        have hf_ne : f ≠ 1 := by
          intro h_eq
          apply h_phi_triv
          ext k
          have h1 : f (eK k) = 1 := by rw [h_eq]; rfl
          have h2 : f (eK k) = (MulAut.congr eQ) (φ k) := by
            show ((MulAut.congr eQ).toMonoidHom).comp (φ.comp eK.symm.toMonoidHom) (eK k) = _
            simp [MulEquiv.symm_apply_apply]
          rw [h2] at h1
          have h3 : φ k = 1 := (MulEquiv.map_eq_one_iff (MulAut.congr eQ)).mp h1
          simpa using h3
        have hf_range :=
          natCard_range_eq_two_of_nontrivial_C4_action h_ge_3 h_3_mod_4 f hf_ne
        haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
        have h_qm1_ne : q - 1 ≠ 0 := by have := h_q_prime.out.one_lt; omega
        have h_dvd : 2 ∣ q - 1 := by
          have hq_odd : Odd q := h_q_prime.out.odd_of_ne_two (by omega)
          obtain ⟨k, rfl⟩ := hq_odd; omega
        have hr : 1 ≤ min 2 ((q - 1).factorization 2) := by
          refine Nat.le_min.mpr ⟨one_le_two, ?_⟩
          rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two h_qm1_ne]
          simpa using h_dvd
        -- Transport f from `CyclicGroup 4 →* MulAut (CyclicGroup q)` to the
        -- `q^1` form needed by classify_Cqn_rtimes_Cpm_exists.
        have h_iso_canon :
            Nonempty (SemidirectProduct (CyclicGroup q) (CyclicGroup 4) f ≃*
              SemidirectProduct (CyclicGroup q) (CyclicGroup 4)
                (canonicalC4OnCqAction h_ge_3)) := by
          have := classify_Cqn_rtimes_Cpm_exists (p := 2) (q := q) (r := 1)
            (by omega : (2 : ℕ) ≠ q) (by omega : q ≠ 2) (m := 2) (n := 1)
            (by norm_num : (0 : ℕ) < 2) Nat.one_pos
            (show CyclicGroup (2 ^ 2) →* MulAut (CyclicGroup (q ^ 1)) from by
              rw [show (2 : ℕ) ^ 2 = 4 from by norm_num,
                  show q ^ 1 = q from pow_one q]
              exact f)
            (by
              rw [show (2 : ℕ) ^ 2 = 4 from by norm_num,
                  show q ^ 1 = q from pow_one q]
              exact hf_range)
            hr
          -- Translate this back through the same equalities.
          show Nonempty (SemidirectProduct (CyclicGroup q) (CyclicGroup 4) f ≃*
              SemidirectProduct (CyclicGroup q) (CyclicGroup 4)
                (canonicalC4OnCqAction h_ge_3))
          unfold canonicalC4OnCqAction
          -- `this` is the corresponding iso with q^1 / 2^2; both equalities are
          -- definitional after the rewrites inside.
          convert this using 2 <;> simp [pow_one]
        have : Nonempty (G ≃* SemidirectProduct (CyclicGroup q) (CyclicGroup 4)
                  (canonicalC4OnCqAction h_ge_3)) :=
          ⟨h_iso_g_q_k.trans (h_sdp_congr.trans h_iso_canon.some)⟩
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
      · -- φ nontrivial: yields a semidirect product C_q ⋊ (C_2 × C_2) with
        -- nontrivial action (the 4th class in the classification of order 4q).
        -- This case is left for future work — adding the 4th disjunct and
        -- closing this branch requires a separate (C_2 × C_2)-flavoured helper.
        sorry



