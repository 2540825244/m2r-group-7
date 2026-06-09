import Mathlib
import «M2rGroup7».Lemmas.SylowUtils
import «M2rGroup7».Lemmas.LinearAlgebraUtils
import «M2rGroup7».Lemmas.GroupTheoryLemmas
import «M2rGroup7».Lemmas.ClassificationUtils
import «M2rGroup7».Lemmas.HomomorphismUtils
import «M2rGroup7».Lemmas.NumberTheoryUtils
import «M2rGroup7».P2qClassification.CycPGroupClassification

/-- Canonical nontrivial action `C_2 →* Aut(C_{p^2})`, image of order 2. -/
def canonicalC2OnCp2Action {p : ℕ} [h_p_prime : Fact p.Prime] (h_p_ne_2 : p ≠ 2) :
    CyclicGroup 2 →* MulAut (CyclicGroup (p ^ 2)) :=
  haveI := h_p_prime
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 h_p_prime.out.ne_zero⟩
  haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  haveI : NeZero ((2:ℕ) ^ 1) := ⟨pow_ne_zero 1 (by norm_num)⟩
  transportCpCqHom (pow_one 2) (rfl : p ^ 2 = p ^ 2)
    (canonicalAction 2 p 2 1 (Ne.symm h_p_ne_2) h_p_ne_2 (by norm_num)
       1 (by
          have h := (Nat.le_min.mp (one_le_min_two_factorization_two h_p_ne_2)).2
          exact Nat.le_min.mpr ⟨le_refl 1, h⟩))

/-! ## Canonical actions on `C_p × C_p` for the `C_2` factor.

For `p` odd prime, the explicit equivalence
`autMulEquivCpCp p : MulAut (C_p × C_p) ≃* GL₂(𝔽_p)` lets us transport order-2
elements of `GL₂(𝔽_p)` back to order-2 automorphisms of `C_p × C_p`. We use this
to define the two canonical nontrivial `C_2`-actions, by transporting
`diag(1, -1)` and `-I`. -/

/-- Explicit equivalence `MulAut (C_p × C_p) ≃* GL₂(𝔽_p)` (computable). -/
abbrev cpcpEquivGL2 (p : ℕ) [Fact p.Prime] :
    MulAut (CyclicGroup p × CyclicGroup p) ≃* GL (Fin 2) (ZMod p) :=
  autMulEquivCpCp p

/-- The canonical "`diag(1, -1)`" action `C_2 →* Aut(C_p × C_p)`. -/
def canonicalC2OnCpCpAction_r1 {p : ℕ} [Fact p.Prime] (hp_ne_2 : p ≠ 2) :
    CyclicGroup 2 →* MulAut (CyclicGroup p × CyclicGroup p) :=
  cyclicHom 2 ((cpcpEquivGL2 p).symm (gl2Diag1NegOne hp_ne_2)) (by
    rw [← map_pow, gl2Diag1NegOne_sq hp_ne_2, map_one])

/-- The canonical "`-I`" action `C_2 →* Aut(C_p × C_p)`. -/
def canonicalC2OnCpCpAction_r2 (p : ℕ) [Fact p.Prime] :
    CyclicGroup 2 →* MulAut (CyclicGroup p × CyclicGroup p) :=
  cyclicHom 2 ((cpcpEquivGL2 p).symm gl2DiagNeg1Neg1) (by
    rw [← map_pow, gl2DiagNeg1Neg1_sq, map_one])

/-! ## Main classification of groups of order `2p^2`. -/

/-- Bridging helper for the `C_p × C_p` nontrivial-action branch of
`classification_2p2`: if `f g₂` is conjugate to `φ_inter g₂` for a generator
`g₂`, then the two semidirect products are isomorphic. -- (extracted by Fuse golfer) -/
private lemma cpcp_semidirect_iso_of_isConj_at_gen
    {p : ℕ} [Fact p.Prime]
    {φ_inter f : CyclicGroup 2 →* MulAut (CyclicGroup p × CyclicGroup p)}
    {g₂ : CyclicGroup 2} (hg₂_gen : ∀ x : CyclicGroup 2, x ∈ Subgroup.zpowers g₂)
    (h_conj : IsConj (f g₂) (φ_inter g₂)) :
    Nonempty (SemidirectProduct (CyclicGroup p × CyclicGroup p) (CyclicGroup 2) φ_inter ≃*
      SemidirectProduct (CyclicGroup p × CyclicGroup p) (CyclicGroup 2) f) := by
  obtain ⟨cu, hcu⟩ := h_conj
  let c : MulAut (CyclicGroup p × CyclicGroup p) := (cu : MulAut _)
  let conj_hom : CyclicGroup 2 →* MulAut (CyclicGroup p × CyclicGroup p) :=
    { toFun := fun x => c * f x * c⁻¹
      map_one' := by simp
      map_mul' := fun a b => by simp only [map_mul]; group }
  have h_eq_on_g₂ : φ_inter g₂ = conj_hom g₂ := by
    show φ_inter g₂ = c * f g₂ * c⁻¹
    have h1 : c * f g₂ = φ_inter g₂ * c := hcu
    calc φ_inter g₂ = φ_inter g₂ * c * c⁻¹ := by rw [mul_inv_cancel_right]
      _ = c * f g₂ * c⁻¹ := by rw [h1]
  have h_eq : φ_inter = conj_hom :=
    monoidHom_eq_of_generator_eq hg₂_gen h_eq_on_g₂
  obtain ⟨e_iso⟩ := semidirectProduct_iso_of_conjugate_action (f_1 := f) (f_2 := φ_inter) c 1
    (fun x => by simpa using congr_fun (congr_arg DFunLike.coe h_eq) x)
  exact ⟨e_iso.symm⟩

set_option maxHeartbeats 400000 in
theorem classification_2p2 {p : ℕ} [h_p_prime : Fact p.Prime] [Group G]
    (h_ge_3 : p ≥ 3) (h : Nat.card G = p ^ 2 * 2)
    : Nonempty (G ≃* CyclicGroup (2 * p ^ 2))
      ∨ Nonempty (G ≃* CyclicGroup p × CyclicGroup p × CyclicGroup 2)
      ∨ Nonempty (G ≃* SemidirectProduct (CyclicGroup (p ^ 2)) (CyclicGroup 2)
                         (canonicalC2OnCp2Action (by omega : p ≠ 2)))
      ∨ Nonempty (G ≃* SemidirectProduct (CyclicGroup p × CyclicGroup p) (CyclicGroup 2)
                         (canonicalC2OnCpCpAction_r1 (by omega : p ≠ 2)))
      ∨ Nonempty (G ≃* SemidirectProduct (CyclicGroup p × CyclicGroup p) (CyclicGroup 2)
                         (canonicalC2OnCpCpAction_r2 p)) := by
  haveI : NeZero p := ⟨h_p_prime.out.ne_zero⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hp_ne_2 : p ≠ 2 := by omega
  haveI : Finite G := by
    apply Nat.finite_of_card_ne_zero; rw [h]
    have p_ne : p ≠ 0 := Nat.Prime.ne_zero h_p_prime.elim
    simp; tauto
  let n_p := Nat.card (Sylow p G)
  let n_2 := Nat.card (Sylow 2 G)
  have hpne2 : p ≠ 2 := hp_ne_2
  have n_p_or_n_2_one : n_p = 1 ∨ n_2 = 1 :=
    p2q_group_has_normal_sylow_subgroup G hpne2 h
  have h2cop : Nat.Coprime 2 p :=
    ((by norm_num : (2 : ℕ).Prime).coprime_of_ne h_p_prime.out (by omega))
  have h_p2_p_card : Nat.card G = p ^ 2 * 2 ^ 1 := by simpa using h
  have h_2_p2_card : Nat.card G = 2 ^ 1 * p ^ 2 := by rw [h]; ring
  rcases n_p_or_n_2_one with h_np_1 | h_n2_1
  · -- n_p = 1: Sylow p-subgroup N (order p²) is normal, complement K of order 2
    let N : Sylow p G := default
    haveI : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp h_np_1).1
    have h_N_card : Nat.card ↥(N : Subgroup G) = p ^ 2 :=
      sylow_card_eq hpne2 h_p2_p_card N
    have h_N_idx_2 : ∀ N : Sylow p G, (↑N : Subgroup G).index = 2 := fun N => by
      simpa using sylow_index_eq hpne2 h_p2_p_card N
    obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime
      (N := (↑N : Subgroup G)) (by
      rw [h_N_card, h_N_idx_2]
      exact ((h_p_prime.out.coprime_of_ne (by norm_num : (2 : ℕ).Prime) hpne2)).pow_left 2)
    have h_iso_g_n_k := SemidirectProduct.mulEquivSubgroup hK
    let φ : ↥K →* MulAut ↥(↑N : Subgroup G) :=
      (↑N : Subgroup G).normalizerMonoidHom.comp
        (Subgroup.inclusion (by simp [Subgroup.normalizer_eq_top]))
    have hK_card : Nat.card ↥K = 2 := by
      have h1 : Nat.card G = Nat.card ↥(↑N : Subgroup G) * Nat.card ↥K := by
        have heq := Nat.card_congr h_iso_g_n_k.toEquiv
        rw [SemidirectProduct.card] at heq; exact heq.symm
      rw [h_N_card, h] at h1
      have hp_pos : 0 < p ^ 2 := pow_pos h_p_prime.out.pos 2
      exact (Nat.eq_of_mul_eq_mul_left hp_pos h1).symm
    have eK : ↥K ≃* CyclicGroup 2 :=
      Classical.choice (prime_classification_of_group (n := 2) hK_card)
    have h2p2cop : Nat.Coprime 2 (p ^ 2) := h2cop.pow_right 2
    have hp2_2cop : Nat.Coprime (p ^ 2) 2 := h2p2cop.symm
    rcases (p_squared_classification (p := p) h_N_card) with h_N_Cp2 | h_N_CpCp
    · -- N ≅ C_{p²}: bridge φ via eN, eK, dispatch via classify_Cqn_rtimes_Cpm
      let eN := h_N_Cp2.some
      let φ_inter : CyclicGroup 2 →* MulAut (CyclicGroup (p ^ 2)) :=
        (MulAut.congr eN).toMonoidHom.comp (φ.comp eK.symm.toMonoidHom)
      have h_congr : ↥(↑N : Subgroup G) ⋊[φ] ↥K ≃*
          SemidirectProduct (CyclicGroup (p ^ 2)) (CyclicGroup 2) φ_inter :=
        SemidirectProduct.congr' (φ₁ := φ) (fn := eN) (fg := eK)
      haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 h_p_prime.out.ne_zero⟩
      haveI : NeZero ((2:ℕ)^1) := ⟨pow_ne_zero 1 (by norm_num)⟩
      have h2p : (2 : ℕ) ≠ p := by omega
      have h21 : ((2:ℕ)^1 : ℕ) = 2 := by norm_num
      have hp22 : (p^2 : ℕ) = p^2 := rfl
      have h_pre_iso := SemidirectProduct.transportCpCqIso h21.symm hp22.symm φ_inter
      obtain ⟨⟨r, hr_lt⟩, ⟨e_pre⟩, _⟩ := classify_Cqn_rtimes_Cpm (p := 2) (q := p) h2p hpne2 1 2
        Nat.one_pos (by norm_num)
        (transportCpCqHom h21.symm hp22.symm φ_inter)
      have hr_le : r ≤ min 1 ((p - 1).factorization 2) := Nat.lt_succ_iff.mp hr_lt
      let canonR := fun r (hr : r ≤ min 1 ((p - 1).factorization 2)) =>
        canonicalAction 2 p 2 1 h2p hpne2 (by norm_num) r hr
      let e_back := fun r hr => SemidirectProduct.transportCpCqIso h21 hp22 (canonR r hr)
      let pre := h_iso_g_n_k.symm.trans (h_congr.trans (h_pre_iso.trans
        (e_pre.trans (e_back r hr_le))))
      have hr_le_1 : r ≤ 1 := hr_le.trans (min_le_left _ _)
      interval_cases r
      · -- r = 0: trivial action → G ≃* C_{2p²}
        have h_triv := eq_one_of_range_card_one (by
          show Nat.card (transportCpCqHom h21 hp22 (canonR 0 hr_le)).range = 1
          rw [transportCpCqHom_range_card]
          simpa using canonicalAction_range_card 2 p 2 1 0 h2p hpne2 (by norm_num) hr_le)
        have : G ≃* CyclicGroup (2 * p ^ 2) := pre.trans
          ((SemidirectProduct.mulEquivOfTrivialAction h_triv).trans
            (MulEquiv.prodComm.trans (CyclicGroup.prodMulEquiv h2p2cop)))
        tauto
      · -- r = 1: matches `canonicalC2OnCp2Action`.
        tauto
    · -- N ≅ C_p × C_p: by_cases on φ_inter triviality
      let eN := h_N_CpCp.some
      let φ_inter : CyclicGroup 2 →* MulAut (CyclicGroup p × CyclicGroup p) :=
        (MulAut.congr eN).toMonoidHom.comp (φ.comp eK.symm.toMonoidHom)
      have h_congr : ↥(↑N : Subgroup G) ⋊[φ] ↥K ≃*
          SemidirectProduct (CyclicGroup p × CyclicGroup p) (CyclicGroup 2) φ_inter :=
        SemidirectProduct.congr' (φ₁ := φ) (fn := eN) (fg := eK)
      by_cases h_triv : φ_inter = 1
      · -- φ_inter trivial → G ≃* (C_p × C_p) × C_2
        have : G ≃* CyclicGroup p × CyclicGroup p × CyclicGroup 2 :=
          h_iso_g_n_k.symm.trans (h_congr.trans
            ((SemidirectProduct.mulEquivOfTrivialAction h_triv).trans
              MulEquiv.prodAssoc))
        tauto
      · -- φ_inter nontrivial: image has order 2 by Lagrange (|C_2| = 2 prime)
        -- so φ_inter is determined by a single order-2 σ; conjugate to canon₁ or canon₂.
        -- φ_inter(generator) has order dividing 2; nontriviality forces it to be 2.
        have h_card_K2 : Nat.card (CyclicGroup 2) = 2 := card_cyclicGroup 2
        -- |φ_inter.range| divides |C_2| = 2, and isn't 1.
        have h_range_dvd : Nat.card φ_inter.range ∣ 2 := by
          have := Subgroup.card_range_dvd φ_inter; rwa [h_card_K2] at this
        have h_range_ne_1 : Nat.card φ_inter.range ≠ 1 :=
          fun h => h_triv (eq_one_of_range_card_one h)
        have h_range_card : Nat.card φ_inter.range = 2 := by
          rcases (Nat.dvd_prime Nat.prime_two).mp h_range_dvd with h1 | h2
          · exact absurd h1 h_range_ne_1
          · exact h2
        -- the generator (Multiplicative.ofAdd 1 : CyclicGroup 2) maps to some σ
        let g₂ : CyclicGroup 2 := Multiplicative.ofAdd (1 : ZMod 2)
        let σ : MulAut (CyclicGroup p × CyclicGroup p) := φ_inter g₂
        have hg2_sq : g₂ ^ 2 = 1 := by
          have h := pow_card_eq_one' (G := CyclicGroup 2) (x := g₂)
          rwa [card_cyclicGroup] at h
        have hσ_sq : σ ^ 2 = 1 := by
          have := congr_arg φ_inter hg2_sq
          rwa [map_pow, map_one] at this
        -- σ ≠ 1: otherwise φ_inter would be trivial since g₂ generates.
        have hg₂_gen : ∀ x : CyclicGroup 2, x ∈ Subgroup.zpowers g₂ := by
          intro x
          refine Subgroup.mem_zpowers_iff.mpr ⟨((Multiplicative.toAdd x).val : ℤ), ?_⟩
          show Multiplicative.ofAdd (1 : ZMod 2) ^ ((Multiplicative.toAdd x).val : ℤ) = x
          rw [← Multiplicative.ofAdd.apply_symm_apply x]
          show Multiplicative.ofAdd (1 : ZMod 2) ^ ((Multiplicative.toAdd x).val : ℤ)
              = Multiplicative.ofAdd (Multiplicative.toAdd x)
          rw [← ofAdd_zsmul, zsmul_one]
          congr 1
          push_cast
          exact ZMod.natCast_zmod_val _
        have hσ_ne_one : σ ≠ 1 := by
          intro hσ1
          apply h_triv
          have hext : ∀ x : CyclicGroup 2, φ_inter x = 1 := by
            intro x
            obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg₂_gen x)
            have : φ_inter x = (φ_inter g₂) ^ n := by rw [← hn, map_zpow]
            rw [this, show φ_inter g₂ = σ from rfl, hσ1, one_zpow]
          ext x : 1; rw [hext x]; rfl
        have hσ_order : orderOf σ = 2 := orderOf_eq_prime hσ_sq hσ_ne_one
        -- Transport σ to GL₂(F_p) and apply the GL₂ order-2 classification.
        let e := cpcpEquivGL2 p
        let σ' : GL (Fin 2) (ZMod p) := e σ
        have hσ'_order : orderOf σ' = 2 := by
          show orderOf (e σ) = 2; rw [e.orderOf_eq]; exact hσ_order
        have hval_g₂ : ((Multiplicative.toAdd g₂).val : ℤ) = 1 := by
          change ((1 : ZMod 2).val : ℤ) = 1
          rw [ZMod.val_one_eq_one_mod]; norm_num
        -- Common helper: transport `IsConj σ' m` back to `IsConj (canon g₂) σ` for canon g₂ = e.symm m.
        have h_back_of : ∀ {m : GL (Fin 2) (ZMod p)} {canon_g₂ : MulAut (CyclicGroup p × CyclicGroup p)},
            canon_g₂ = (cpcpEquivGL2 p).symm m → IsConj σ' m → IsConj canon_g₂ σ := by
          intro m canon_g₂ hcanon hconj
          rw [hcanon]
          have h := e.symm.toMonoidHom.map_isConj hconj.symm
          change IsConj ((cpcpEquivGL2 p).symm m) (e.symm (e σ)) at h
          rwa [e.symm_apply_apply] at h
        rcases gl2_order_two_classification hp_ne_2 σ' hσ'_order with h_conj1 | h_conj2
        · -- σ' ≈ diag(1,-1): transport back to σ ≈ canonical r1 action at g₂.
          have hr1 : canonicalC2OnCpCpAction_r1 hp_ne_2 g₂
              = (cpcpEquivGL2 p).symm (gl2Diag1NegOne hp_ne_2) := by
            show cyclicHom 2 ((cpcpEquivGL2 p).symm (gl2Diag1NegOne hp_ne_2)) _ g₂ = _
            rw [cyclicHom_apply_eq_zpow, hval_g₂]; exact zpow_one _
          obtain ⟨e_iso⟩ := cpcp_semidirect_iso_of_isConj_at_gen
            (f := canonicalC2OnCpCpAction_r1 hp_ne_2) hg₂_gen (h_back_of hr1 h_conj1)
          have : G ≃* SemidirectProduct (CyclicGroup p × CyclicGroup p) (CyclicGroup 2)
                       (canonicalC2OnCpCpAction_r1 hp_ne_2) :=
            h_iso_g_n_k.symm.trans (h_congr.trans e_iso)
          tauto
        · -- σ' ≈ -I: transport back to σ ≈ canonical r2 action at g₂.
          have hr2 : canonicalC2OnCpCpAction_r2 p g₂
              = (cpcpEquivGL2 p).symm gl2DiagNeg1Neg1 := by
            show cyclicHom 2 ((cpcpEquivGL2 p).symm gl2DiagNeg1Neg1) _ g₂ = _
            rw [cyclicHom_apply_eq_zpow, hval_g₂]; exact zpow_one _
          obtain ⟨e_iso⟩ := cpcp_semidirect_iso_of_isConj_at_gen
            (f := canonicalC2OnCpCpAction_r2 p) hg₂_gen (h_back_of hr2 h_conj2)
          have : G ≃* SemidirectProduct (CyclicGroup p × CyclicGroup p) (CyclicGroup 2)
                       (canonicalC2OnCpCpAction_r2 p) :=
            h_iso_g_n_k.symm.trans (h_congr.trans e_iso)
          tauto
  · -- n_2 = 1: Sylow 2-subgroup Q (order 2) is normal, complement K of order p²
    let Q : Sylow 2 G := default
    haveI : Subsingleton (Sylow 2 G) := (Nat.card_eq_one_iff_unique.mp h_n2_1).1
    have h_Q_card : Nat.card ↥(Q : Subgroup G) = 2 := by
      simpa using sylow_card_eq (Ne.symm hpne2) h_2_p2_card Q
    have h_Q_idx_p2 : ∀ Q : Sylow 2 G, (↑Q : Subgroup G).index = p ^ 2 := fun Q => by
      simpa using sylow_index_eq (Ne.symm hpne2) h_2_p2_card Q
    obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime
      (N := (↑Q : Subgroup G)) (by
      rw [h_Q_card, h_Q_idx_p2]
      exact ((by norm_num : (2 : ℕ).Prime).coprime_of_ne h_p_prime.out
        (by omega : (2 : ℕ) ≠ p)).pow_right 2)
    have h_iso_g_q_k := SemidirectProduct.mulEquivSubgroup hK
    let φ : ↥K →* MulAut ↥(↑Q : Subgroup G) :=
      (↑Q : Subgroup G).normalizerMonoidHom.comp
        (Subgroup.inclusion (by simp [Subgroup.normalizer_eq_top]))
    have hK_card : Nat.card ↥K = p ^ 2 := by
      have h1 : Nat.card G = Nat.card ↥(↑Q : Subgroup G) * Nat.card ↥K := by
        have heq := Nat.card_congr h_iso_g_q_k.toEquiv
        rw [SemidirectProduct.card] at heq; exact heq.symm
      rw [h_Q_card, h] at h1
      exact (Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) (by linarith))
    have eQ : ↥(↑Q : Subgroup G) ≃* CyclicGroup 2 :=
      Classical.choice (prime_classification_of_group (n := 2) h_Q_card)
    -- Aut(C_2) is trivial since |Aut(C_2)| = 1
    have h_aut_card : Nat.card (MulAut ↥(↑Q : Subgroup G)) = 1 := by
      have h_iso_aut : MulAut ↥(↑Q : Subgroup G) ≃* MulAut (CyclicGroup 2) :=
        MulAut.congr eQ
      have h_aut_c2 : Nat.card (MulAut (CyclicGroup 2)) = 1 := by
        have := card_mulAut_cyclicGroup_prime (q := 2)
        simpa using this
      exact (Nat.card_congr h_iso_aut.toEquiv).trans h_aut_c2
    -- φ trivial since codomain has cardinality 1
    have h_phi_triv : φ = 1 := eq_one_of_coprime_card (by
      rw [hK_card, h_aut_card]; simp)
    have h_2p2cop : Nat.Coprime 2 (p ^ 2) := h2cop.pow_right 2
    have h_p22cop : Nat.Coprime (p ^ 2) 2 := h_2p2cop.symm
    rcases (p_squared_classification (p := p) hK_card) with h_K_Cp2 | h_K_CpCp
    · -- K ≅ C_{p²}: G ≅ C_2 × C_{p²} ≅ C_{2p²}
      let eK := h_K_Cp2.some
      have : G ≃* CyclicGroup (2 * p ^ 2) := h_iso_g_q_k.symm.trans
        ((SemidirectProduct.mulEquivOfTrivialAction h_phi_triv).trans
          ((eQ.prodCongr eK).trans (CyclicGroup.prodMulEquiv h_2p2cop)))
      tauto
    · -- K ≅ C_p × C_p: G ≅ C_2 × (C_p × C_p) ≅ C_p × C_p × C_2
      let eK := h_K_CpCp.some
      have : G ≃* CyclicGroup p × CyclicGroup p × CyclicGroup 2 := h_iso_g_q_k.symm.trans
        ((SemidirectProduct.mulEquivOfTrivialAction h_phi_triv).trans
          ((eQ.prodCongr eK).trans (MulEquiv.prodComm.trans MulEquiv.prodAssoc)))
      tauto
