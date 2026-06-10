import Mathlib
import «M2rGroup7».Lemmas.SylowUtils
import «M2rGroup7».Lemmas.LinearAlgebraUtils
import «M2rGroup7».Lemmas.GroupTheoryLemmas
import «M2rGroup7».Lemmas.ClassificationUtils
import «M2rGroup7».Lemmas.HomomorphismUtils
import «M2rGroup7».Lemmas.NumberTheoryUtils
import «M2rGroup7».P2qClassification.CycPGroupClassification
import «M2rGroup7».CyclicGroup

/-- Canonical non-trivial action C_q →* Aut(C_{p^2}), image of order q.
    Exists when q ∣ p - 1, encoded by `hr : 1 ≤ min 1 ((p - 1).factorization q)`. -/
noncomputable def canonicalCqOnCp2Action
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hp2 : p ≠ 2)
    (hr : 1 ≤ min 1 ((p - 1).factorization q)) :
    CyclicGroup q →* MulAut (CyclicGroup (p ^ 2)) :=
  sdpCanonicalAction (p := q) (q := p) hp2
    1 2 (by norm_num)
    (by rw [card_cyclicGroup])
    (by rw [card_cyclicGroup, pow_one])
    1 hr

theorem classification_p2q {q : ℕ} [h_p_prime : Fact p.Prime] [h_q_prime : Fact q.Prime] [Group G]
    (h_p_ne_q : p ≠ q) (h : Nat.card G = p ^ 2 * q)
    : Nonempty (G ≃* CyclicGroup (p ^ 2 * q))
      ∨ Nonempty (G ≃* CyclicGroup p × CyclicGroup p × CyclicGroup q)
      ∨ (∃ (hp2 : p ≠ 2) (hr : 1 ≤ min 1 ((p - 1).factorization q)),
          Nonempty (G ≃* SemidirectProduct (CyclicGroup (p ^ 2)) (CyclicGroup q)
                           (canonicalCqOnCp2Action hp2 hr))) := by
  -- G is finite
  haveI : Finite G := by
    apply Nat.finite_of_card_ne_zero
    rw [h]
    have q_ne : q ≠ 0 := Nat.Prime.ne_zero h_q_prime.elim
    exact mul_ne_zero (pow_ne_zero 2 (Nat.Prime.ne_zero h_p_prime.elim)) q_ne
  let n_p := Nat.card (Sylow p G)
  let n_q := Nat.card (Sylow q G)
  have n_p_or_n_q_one : n_p = 1 ∨ n_q = 1 := p2q_group_has_normal_sylow_subgroup G (by aesop) h
  rcases n_p_or_n_q_one with h_np_1 | h_nq_1
  · -- case h_np_1 : n_p = 1
    let P : Sylow p G := default
    -- Enough to synthesize instance of type class (↑P).Normal
    -- for Subgroup.exists_right_complement'_of_coprime
    haveI : Subsingleton (Sylow p G) :=
      (Nat.card_eq_one_iff_unique.mp h_np_1).1
    have h_card_form : Nat.card G = p ^ 2 * q ^ 1 := by aesop
    have h_p_p2 : Nat.card ↥(P : Subgroup G) = p ^ 2 := by
      exact sylow_card_eq (by aesop) h_card_form P
    -- Index of Sylow p-group is q
    have h_p_idx_q : ∀ P : Sylow p G, (↑P : Subgroup G).index = q := by
      intro P
      simpa using sylow_index_eq (by aesop) h_card_form P
    haveI := (h_p_prime.out.coprime_of_ne h_q_prime.out h_p_ne_q).pow_left 2
    obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime (N := (↑P : Subgroup G)) (by
      rw [h_p_p2, h_p_idx_q]
      exact (h_p_prime.out.coprime_of_ne h_q_prime.out h_p_ne_q).pow_left 2)
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
      exact (Nat.eq_of_mul_eq_mul_left (pow_pos h_p_prime.out.pos 2) h1).symm
    -- Step 2: K ≃* C_q
    have eK : ↥K ≃* CyclicGroup q :=
      Classical.choice (prime_classification_of_group (n := q) hK_card)
    -- P is isomorphic to C_p x C_p or C_p^2
    rcases p_squared_classification (p := p) h_p_p2 with h_c_p2 | h_cp_cp
    · -- h_c_p2 : Nonempty (P ≃* CyclicGroup (p ^ 2))
      -- If p ≠ 2, we can apply semi direct product classification

      rcases eq_or_ne p 2 with rfl | hp_ne_2
      · -- Case 1: p = 2
        simp only [Nat.reducePow] at h_c_p2
        have h_aut_card : Nat.card (MulAut ↥(↑P : Subgroup G)) = 2 :=
          (Nat.card_congr ((MulAut.congr h_c_p2.some).trans
            (Classical.choice (aut_of_cyclic_p2 (p := 2)))).toEquiv).trans (card_cyclicGroup 2)
        have h_phi_triv : φ = 1 := eq_one_of_coprime_card (by
          rw [hK_card, h_aut_card]
          exact h_q_prime.out.coprime_of_ne (by norm_num : (2 : ℕ).Prime) (by omega))
        have h4q : Nat.Coprime 4 q :=
          ((by norm_num : (2 : ℕ).Prime).coprime_of_ne h_q_prime.out (by omega)).pow_left 2
        have : G ≃* CyclicGroup (4 * q) := h_iso_g_p_k.symm.trans
          ((SemidirectProduct.mulEquivOfTrivialAction h_phi_triv).trans
            ((h_c_p2.some.prodCongr eK).trans (CyclicGroup.prodMulEquiv h4q)))
        tauto
      · -- Case 2 : hp_ne_2 : p ≠ 2
        -- Transport φ to concrete cyclic groups
        let eP := h_c_p2.some
        let φ' : CyclicGroup q →* MulAut (CyclicGroup (p ^ 2)) :=
          (MulAut.congr eP).toMonoidHom.comp (φ.comp eK.symm.toMonoidHom)
        have h_bridge : ↥(↑P : Subgroup G) ⋊[φ] ↥K ≃*
            SemidirectProduct (CyclicGroup (p ^ 2)) (CyclicGroup q) φ' :=
          SemidirectProduct.congr' (φ₁ := φ) (fn := eP) (fg := eK)
        -- classify_sdp: C_q acts on C_{p^2}; in sdpCanonicalAction variables p↔q, q↔p, m=1, n=2
        obtain ⟨⟨rval, hrlt⟩, hr_iso, _⟩ :=
          classify_sdp (p := q) (q := p) (Ne.symm h_p_ne_q) hp_ne_2
            1 2 (by norm_num)
            (hN := by rw [card_cyclicGroup (p ^ 2)])
            (hK := by rw [card_cyclicGroup q, pow_one])
            φ'
        have h_rval_le_1 : rval ≤ 1 := by
          have h_min_le : min 1 ((p - 1).factorization q) ≤ 1 := min_le_left _ _
          omega
        interval_cases rval
        · -- r = 0: trivial action → G ≃* C_{p^2 * q}
          obtain ⟨e⟩ := hr_iso
          have h_triv :
              sdpCanonicalAction (p := q) (q := p) hp_ne_2
                1 2 (by norm_num)
                (hN := by rw [card_cyclicGroup (p ^ 2)])
                (hK := by rw [card_cyclicGroup q, pow_one])
                0 (by simp) = 1 :=
            eq_one_of_range_card_one (by
              rw [sdpCanonicalAction_range_card (p := q) (q := p), pow_zero])
          have h_cop : Nat.Coprime (p ^ 2) q :=
            (h_p_prime.out.coprime_of_ne h_q_prime.out h_p_ne_q).pow_left 2
          have : G ≃* CyclicGroup (p ^ 2 * q) := h_iso_g_p_k.symm.trans (h_bridge.trans (e.trans
            ((SemidirectProduct.mulEquivOfTrivialAction h_triv).trans
              (CyclicGroup.prodMulEquiv h_cop))))
          tauto
        · -- r = 1: non-trivial action → G ≃* C_{p^2} ⋊ C_q (exists only when q ∣ p - 1)
          obtain ⟨e⟩ := hr_iso
          have hr_cond : 1 ≤ min 1 ((p - 1).factorization q) := by omega
          have : G ≃* SemidirectProduct (CyclicGroup (p ^ 2)) (CyclicGroup q)
                           (canonicalCqOnCp2Action hp_ne_2 hr_cond) :=
            h_iso_g_p_k.symm.trans (h_bridge.trans e)
          tauto

    · -- h_cp_cp : Nonempty (P ≃* CyclicGroup p × CyclicGroup p)
      sorry
  · -- case h_nq_1 : n_q = 1
    let Q : Sylow q G := default
    haveI : Subsingleton (Sylow q G) := (Nat.card_eq_one_iff_unique.mp h_nq_1).1
    have h_card_form : Nat.card G = q ^ 1 * p ^ 2 := by rw [pow_one, h]; ring
    have h_Q_card : Nat.card ↥(Q : Subgroup G) = q := by
      simpa using sylow_card_eq (Ne.symm (by aesop)) h_card_form Q
    have h_Q_idx_4 : ∀ Q : Sylow q G, (↑Q : Subgroup G).index = p ^ 2 := fun Q => by
      simpa using sylow_index_eq (Ne.symm (by aesop)) h_card_form Q
    have : q.Coprime (p ^ 2) := by sorry
    obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime (N := (↑Q : Subgroup G)) (by
      rw [h_Q_card, h_Q_idx_4]
      tauto)
    have h_iso_g_q_k := SemidirectProduct.mulEquivSubgroup hK
    let φ : ↥K →* MulAut ↥(↑Q : Subgroup G) :=
      (↑Q : Subgroup G).normalizerMonoidHom.comp
        (Subgroup.inclusion (by simp [Subgroup.normalizer_eq_top]))
    have hK_card : Nat.card ↥K = p ^ 2 := by
      have h1 : Nat.card G = Nat.card ↥(↑Q : Subgroup G) * Nat.card ↥K := by
        have heq := Nat.card_congr h_iso_g_q_k.toEquiv
        rw [SemidirectProduct.card] at heq; exact heq.symm
      rw [h_Q_card, h] at h1
      exact (Nat.eq_of_mul_eq_mul_left h_q_prime.out.pos (by linarith)).symm
    have eQ : ↥(↑Q : Subgroup G) ≃* CyclicGroup q :=
      Classical.choice (prime_classification_of_group (n := q) h_Q_card)
    rcases (p_squared_classification (p := p) hK_card) with h_K_C4 | h_K_C2C2
    · sorry
    · sorry
