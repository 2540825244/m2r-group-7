import Mathlib
import «M2rGroup7».Lemmas.SylowUtils
import «M2rGroup7».Lemmas.LinearAlgebraUtils
import «M2rGroup7».Lemmas.GroupTheoryLemmas
import «M2rGroup7».Lemmas.ClassificationUtils
import «M2rGroup7».Lemmas.HomomorphismUtils
import «M2rGroup7».Lemmas.NumberTheoryUtils
import «M2rGroup7».P2qClassification.CycPGroupClassification

/-! ## Canonical actions for `4q` groups

The 4q canonical wrappers are computable: they transport `canonicalAction` (which
uses `Finset.find?`-style search) across `(2:ℕ)^2 = 4`, `(2:ℕ)^1 = 2`, `q^1 = q`. -/

/-- Canonical nontrivial action `C_4 →* Aut(C_q)`, image of order 2. -/
def canonicalC4OnCqAction
    {q : ℕ} [hq : Fact q.Prime] (h_q_ne_2 : q ≠ 2) :
    CyclicGroup 4 →* MulAut (CyclicGroup q) :=
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  haveI : NeZero (q^1) := ⟨pow_ne_zero 1 hq.out.ne_zero⟩
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  haveI : NeZero ((2:ℕ)^2) := ⟨pow_ne_zero 2 (by norm_num)⟩
  transportCpCqHom (show ((2:ℕ)^2 : ℕ) = 4 by norm_num) (pow_one q)
    (canonicalAction 2 q 1 2 (show (2:ℕ) ≠ q by omega) h_q_ne_2 Nat.one_pos
       1 (one_le_min_two_factorization_two h_q_ne_2))

/-- Canonical action `C_4 →* Aut(C_q)` of image order 4, for `q ≡ 1 (mod 4)`. -/
def canonicalC4OnCqAction_r2
    {q : ℕ} [hq : Fact q.Prime] (h_1_mod_4 : q ≡ 1 [MOD 4]) :
    CyclicGroup 4 →* MulAut (CyclicGroup q) :=
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  haveI : NeZero (q^1) := ⟨pow_ne_zero 1 hq.out.ne_zero⟩
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  haveI : NeZero ((2:ℕ)^2) := ⟨pow_ne_zero 2 (by norm_num)⟩
  transportCpCqHom (show ((2:ℕ)^2 : ℕ) = 4 by norm_num) (pow_one q)
    (canonicalAction 2 q 1 2
       (show (2 : ℕ) ≠ q from by simp [Nat.ModEq] at h_1_mod_4; omega)
       (show q ≠ 2 from by simp [Nat.ModEq] at h_1_mod_4; omega)
       Nat.one_pos
       2 (two_le_min_two_factorization_two_of_one_mod_four h_1_mod_4))

/-- Canonical nontrivial action `C_2 × C_2 →* Aut(C_q)`, image of order 2. -/
def canonicalC2C2OnCqAction
    {q : ℕ} [hq : Fact q.Prime] (h_q_ne_2 : q ≠ 2) :
    CyclicGroup 2 × CyclicGroup 2 →* MulAut (CyclicGroup q) :=
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  haveI : NeZero (q^1) := ⟨pow_ne_zero 1 hq.out.ne_zero⟩
  haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  haveI : NeZero ((2:ℕ)^1) := ⟨pow_ne_zero 1 (by norm_num)⟩
  (transportCpCqHom (pow_one 2) (pow_one q)
    (canonicalAction 2 q 1 1 (show (2:ℕ) ≠ q by omega) h_q_ne_2 Nat.one_pos
       1 (by have := one_le_min_two_factorization_two h_q_ne_2; omega))).comp
    (MonoidHom.fst (CyclicGroup 2) (CyclicGroup 2))

/-! ## Helpers for the `q = 3` case (the `A_4` disjunct). -/

private instance instFactPrimeThree : Fact (Nat.Prime 3) := ⟨by norm_num⟩

private lemma sq_eq_one_cyclicGroup2 (x : CyclicGroup 2) : x * x = 1 := by
  have h := pow_card_eq_one' (G := CyclicGroup 2) (x := x)
  rwa [card_cyclicGroup, sq] at h

def c2c2OrderThreeAut :
    MulAut (CyclicGroup 2 × CyclicGroup 2) where
  toFun p := (p.1 * p.2, p.1)
  invFun p := (p.2, p.1 * p.2)
  left_inv := by
    rintro ⟨x, y⟩
    have hx2 : x * x = 1 := sq_eq_one_cyclicGroup2 x
    refine Prod.ext rfl ?_
    change (x * y) * x = y
    rw [mul_assoc, mul_comm y x, ← mul_assoc, hx2, one_mul]
  right_inv := by
    rintro ⟨x, y⟩
    have hy2 : y * y = 1 := sq_eq_one_cyclicGroup2 y
    refine Prod.ext ?_ rfl
    change y * (x * y) = x
    rw [mul_comm y (x * y), mul_assoc, hy2, mul_one]
  map_mul' := by
    rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩
    refine Prod.ext ?_ rfl
    change (x₁ * x₂) * (y₁ * y₂) = (x₁ * y₁) * (x₂ * y₂)
    rw [mul_mul_mul_comm]

lemma orderOf_c2c2OrderThreeAut : orderOf c2c2OrderThreeAut = 3 := by
  haveI : Fact (Nat.Prime 3) := instFactPrimeThree
  have hsq : ∀ x : CyclicGroup 2, x * x = 1 := sq_eq_one_cyclicGroup2
  refine orderOf_eq_prime ?_ ?_
  · have hpow : c2c2OrderThreeAut ^ 3 =
        c2c2OrderThreeAut * c2c2OrderThreeAut * c2c2OrderThreeAut := by
      rw [pow_succ, pow_succ, pow_one]
    rw [hpow]; ext ⟨x, y⟩
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
      rw [card_cyclicGroup] at h2; norm_num at h2
    intro h
    have happ : c2c2OrderThreeAut (g, 1) = (1 : MulAut _) (g, 1) := by rw [h]
    rw [MulAut.one_apply] at happ
    have hcompute : c2c2OrderThreeAut (g, 1) = (g * 1, g) := rfl
    rw [hcompute, mul_one] at happ
    exact hg_ne (Prod.mk.injEq _ _ _ _ |>.mp happ).2

def canonicalC3OnC2C2Action :
    CyclicGroup 3 →* MulAut (CyclicGroup 2 × CyclicGroup 2) :=
  cyclicHom 3 c2c2OrderThreeAut (by
    have h : c2c2OrderThreeAut ^ 3 = 1 := by
      rw [← orderOf_c2c2OrderThreeAut]; exact pow_orderOf_eq_one _
    exact h)

lemma canonicalC3OnC2C2Action_range_card :
    Nat.card canonicalC3OnC2C2Action.range = 3 := by
  have h_pow : c2c2OrderThreeAut ^ 3 = 1 := by
    rw [← orderOf_c2c2OrderThreeAut]; exact pow_orderOf_eq_one _
  show Nat.card (cyclicHom 3 c2c2OrderThreeAut h_pow).range = 3
  rw [cyclicHom_range, Nat.card_zpowers, orderOf_c2c2OrderThreeAut]

theorem semidirectProduct_C3_on_C2C2_iso
    (f_1 f_2 : CyclicGroup 3 →* MulAut (CyclicGroup 2 × CyclicGroup 2))
    (hf1_range : Nat.card f_1.range = 3) (hf2_range : Nat.card f_2.range = 3) :
    Nonempty (SemidirectProduct (CyclicGroup 2 × CyclicGroup 2) (CyclicGroup 3) f_1 ≃*
              SemidirectProduct (CyclicGroup 2 × CyclicGroup 2) (CyclicGroup 3) f_2) := by
  haveI : Fact (Nat.Prime 3) := instFactPrimeThree
  have h_aut_dih : Nonempty (MulAut (CyclicGroup 2 × CyclicGroup 2) ≃* DihedralGroup 3) := by
    obtain ⟨e2⟩ := aut_of_CpCp 2
    exact ⟨e2.trans GL2F2_isoS3⟩
  have h_dih_3_card : Nat.card (DihedralGroup 3) = 6 := by aesop
  have h_aut_card : Nat.card (MulAut (CyclicGroup 2 × CyclicGroup 2)) = 6 :=
    h_aut_dih.elim fun e => (Nat.card_congr e.toEquiv).trans h_dih_3_card
  haveI : Finite (MulAut (CyclicGroup 2 × CyclicGroup 2)) :=
    Nat.finite_of_card_ne_zero (by rw [h_aut_card]; norm_num)
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h_fact_eq : ((Nat.card (MulAut (CyclicGroup 2 × CyclicGroup 2))).factorization 3) = 1 := by
    rw [h_aut_card, show (6 : ℕ) = 2 * 3 from rfl]
    exact factorization_prime_mul_prime_left Nat.prime_three Nat.prime_two (by norm_num)
  let S1 : Sylow 3 (MulAut (CyclicGroup 2 × CyclicGroup 2)) :=
    Sylow.ofCard f_1.range (by rw [hf1_range, h_fact_eq, pow_one])
  let S2 : Sylow 3 (MulAut (CyclicGroup 2 × CyclicGroup 2)) :=
    Sylow.ofCard f_2.range (by rw [hf2_range, h_fact_eq, pow_one])
  have h_sylow_subsingleton :
      Subsingleton (Sylow 3 (MulAut (CyclicGroup 2 × CyclicGroup 2))) := by
    have h_card_eq_one :
        Nat.card (Sylow 3 (MulAut (CyclicGroup 2 × CyclicGroup 2))) = 1 := by
      have h_idx : (S1 : Subgroup (MulAut (CyclicGroup 2 × CyclicGroup 2))).index = 2 ^ 1 :=
        sylow_index_eq (by norm_num)
          (show Nat.card (MulAut (CyclicGroup 2 × CyclicGroup 2)) = 3 ^ 1 * 2 ^ 1 by
            rw [h_aut_card]; norm_num) S1
      have h_dvd := Sylow.card_dvd_index S1
      have h_mod := card_sylow_modEq_one 3 (MulAut (CyclicGroup 2 × CyclicGroup 2))
      rw [h_idx] at h_dvd
      have h_le : Nat.card (Sylow 3 (MulAut (CyclicGroup 2 × CyclicGroup 2))) ≤ 2 :=
        Nat.le_of_dvd (by norm_num) h_dvd
      have h_pos : 0 < Nat.card (Sylow 3 (MulAut (CyclicGroup 2 × CyclicGroup 2))) :=
        Nat.card_pos
      unfold Nat.ModEq at h_mod; omega
    exact (Nat.card_eq_one_iff_unique.mp h_card_eq_one).1
  have h_range_eq : f_1.range = f_2.range := by
    have h_S_eq : S1 = S2 := Subsingleton.elim _ _
    have h_coe :
        (S1 : Subgroup (MulAut (CyclicGroup 2 × CyclicGroup 2))) =
          (S2 : Subgroup (MulAut (CyclicGroup 2 × CyclicGroup 2))) := by rw [h_S_eq]
    have h_S1 : (S1 : Subgroup _) = f_1.range := Sylow.coe_ofCard f_1.range _
    have h_S2 : (S2 : Subgroup _) = f_2.range := Sylow.coe_ofCard f_2.range _
    rw [← h_S1, ← h_S2]; exact h_coe
  exact semidirectProduct_iso_if_range_eq instFactPrimeThree
    (by rw [card_cyclicGroup, pow_one]) f_1 f_2 h_range_eq

-- ─── Range cards of the new computable wrappers ──────────────────────────

lemma canonicalC4OnCqAction_range_card
    {q : ℕ} [hq : Fact q.Prime] (h_q_ne_2 : q ≠ 2) :
    Nat.card (canonicalC4OnCqAction h_q_ne_2).range = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  haveI : NeZero (q^1) := ⟨pow_ne_zero 1 hq.out.ne_zero⟩
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  haveI : NeZero ((2:ℕ)^2) := ⟨pow_ne_zero 2 (by norm_num)⟩
  show Nat.card (transportCpCqHom (show ((2:ℕ)^2 : ℕ) = 4 by norm_num) (pow_one q)
    (canonicalAction 2 q 1 2 (show (2:ℕ) ≠ q by omega) h_q_ne_2 Nat.one_pos
       1 (one_le_min_two_factorization_two h_q_ne_2))).range = 2
  rw [transportCpCqHom_range_card]
  have h := canonicalAction_range_card 2 q 1 2 1 (show (2:ℕ) ≠ q by omega) h_q_ne_2 Nat.one_pos
    (one_le_min_two_factorization_two h_q_ne_2)
  simpa using h

lemma canonicalC4OnCqAction_r2_range_card
    {q : ℕ} [hq : Fact q.Prime] (h_1_mod_4 : q ≡ 1 [MOD 4]) :
    Nat.card (canonicalC4OnCqAction_r2 h_1_mod_4).range = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  haveI : NeZero (q^1) := ⟨pow_ne_zero 1 hq.out.ne_zero⟩
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  haveI : NeZero ((2:ℕ)^2) := ⟨pow_ne_zero 2 (by norm_num)⟩
  show Nat.card (transportCpCqHom (show ((2:ℕ)^2 : ℕ) = 4 by norm_num) (pow_one q)
    (canonicalAction 2 q 1 2
       (show (2 : ℕ) ≠ q from by simp [Nat.ModEq] at h_1_mod_4; omega)
       (show q ≠ 2 from by simp [Nat.ModEq] at h_1_mod_4; omega)
       Nat.one_pos
       2 (two_le_min_two_factorization_two_of_one_mod_four h_1_mod_4))).range = 4
  rw [transportCpCqHom_range_card]
  have h := canonicalAction_range_card 2 q 1 2 2
    (show (2 : ℕ) ≠ q from by simp [Nat.ModEq] at h_1_mod_4; omega)
    (show q ≠ 2 from by simp [Nat.ModEq] at h_1_mod_4; omega)
    Nat.one_pos
    (two_le_min_two_factorization_two_of_one_mod_four h_1_mod_4)
  simpa using h

lemma canonicalC2C2OnCqAction_range_card
    {q : ℕ} [hq : Fact q.Prime] (h_q_ne_2 : q ≠ 2) :
    Nat.card (canonicalC2C2OnCqAction h_q_ne_2).range = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  haveI : NeZero (q^1) := ⟨pow_ne_zero 1 hq.out.ne_zero⟩
  haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  haveI : NeZero ((2:ℕ)^1) := ⟨pow_ne_zero 1 (by norm_num)⟩
  -- canonicalC2C2OnCqAction = (transportCpCqHom ... (canonicalAction 2 q 1 1 ... 1 _)).comp fst
  -- The composition with `fst` does not change the range.
  have h_comp_range : ∀ (f : CyclicGroup 2 →* MulAut (CyclicGroup q)),
      (f.comp (MonoidHom.fst (CyclicGroup 2) (CyclicGroup 2))).range = f.range :=
    fun f => by
      ext y; simp only [MonoidHom.mem_range, MonoidHom.comp_apply, MonoidHom.coe_fst]
      exact ⟨fun ⟨⟨a, _⟩, h⟩ => ⟨a, h⟩, fun ⟨a, ha⟩ => ⟨(a, 1), ha⟩⟩
  show Nat.card ((transportCpCqHom (pow_one 2) (pow_one q)
      (canonicalAction 2 q 1 1 (show (2:ℕ) ≠ q by omega) h_q_ne_2 Nat.one_pos
         1 (by have := one_le_min_two_factorization_two h_q_ne_2; omega))).comp
    (MonoidHom.fst (CyclicGroup 2) (CyclicGroup 2))).range = 2
  rw [h_comp_range, transportCpCqHom_range_card]
  have h := canonicalAction_range_card 2 q 1 1 1 (show (2:ℕ) ≠ q by omega) h_q_ne_2 Nat.one_pos
    (by have := one_le_min_two_factorization_two h_q_ne_2; omega)
  simpa using h

-- ─── Bridge lemma for the `C_2 × C_2` case (uses `semidirectProduct_CpCp_iso`). ──

/-- Bridge for the `C_2 × C_2` case (uses `semidirectProduct_CpCp_iso`). -/
lemma sdpCanonicalAction_iso_canonicalC2C2OnCqAction
    {q : ℕ} [hq : Fact q.Prime] (h_q_ne_2 : q ≠ 2)
    (φ : (CyclicGroup 2 × CyclicGroup 2) →* MulAut (CyclicGroup q))
    (hφ_ne : φ ≠ 1) (hφ_range : Nat.card φ.range = 2) :
    Nonempty (SemidirectProduct (CyclicGroup q) (CyclicGroup 2 × CyclicGroup 2) φ
      ≃* SemidirectProduct (CyclicGroup q) (CyclicGroup 2 × CyclicGroup 2)
            (canonicalC2C2OnCqAction h_q_ne_2)) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h_canon_card := canonicalC2C2OnCqAction_range_card h_q_ne_2
  have h_canon_ne : canonicalC2C2OnCqAction h_q_ne_2 ≠ 1 := by
    intro hc; simp [hc] at h_canon_card
  exact semidirectProduct_CpCp_iso (p := 2) (q := q)
    (two_dvd_prime_sub_one h_q_ne_2) φ (canonicalC2C2OnCqAction h_q_ne_2)
    hφ_ne h_canon_ne hφ_range h_canon_card

set_option maxHeartbeats 300000 in
-- The case split for `4q` exercises several large existentials
-- (Sylow, semidirect product, `classify_sdp`), pushing past the default.
/-- Classification of groups `G` of order `4q` for `q ≥ 3` prime. -/
theorem classification_4q {q : ℕ} [h_q_prime : Fact q.Prime] [Group G]
    (h_ge_3 : q ≥ 3) (h : Nat.card G = 4 * q)
    : Nonempty (G ≃* CyclicGroup (4 * q))
      ∨ Nonempty (G ≃* CyclicGroup 2 × CyclicGroup 2 × CyclicGroup q)
      ∨ Nonempty (G ≃* SemidirectProduct (CyclicGroup q) (CyclicGroup 4)
                         (canonicalC4OnCqAction (by omega : q ≠ 2)))
      ∨ (∃ h_1_mod_4 : q ≡ 1 [MOD 4],
            Nonempty (G ≃* SemidirectProduct (CyclicGroup q) (CyclicGroup 4)
                            (canonicalC4OnCqAction_r2 h_1_mod_4)))
      ∨ Nonempty (G ≃* SemidirectProduct (CyclicGroup q) (CyclicGroup 2 × CyclicGroup 2)
                         (canonicalC2C2OnCqAction (by omega : q ≠ 2)))
      ∨ (∃ _ : q = 3,
            Nonempty (G ≃* SemidirectProduct (CyclicGroup 2 × CyclicGroup 2) (CyclicGroup 3)
                            canonicalC3OnC2C2Action)) := by
  haveI : NeZero q := ⟨h_q_prime.out.ne_zero⟩
  haveI : Finite G := by
    apply Nat.finite_of_card_ne_zero; rw [h]
    have q_ne : q ≠ 0 := Nat.Prime.ne_zero h_q_prime.elim
    simp; tauto
  let n_2 := Nat.card (Sylow 2 G)
  let n_q := Nat.card (Sylow q G)
  have n_2_or_n_q_one : n_2 = 1 ∨ n_q = 1 := p2q_group_has_normal_sylow_subgroup G (by aesop) h
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rcases n_2_or_n_q_one with h_n2_1 | h_nq_1
  · -- n_2 = 1: Sylow 2-subgroup P (order 4) is normal, complement K has order q
    let P : Sylow 2 G := default
    haveI : Subsingleton (Sylow 2 G) := (Nat.card_eq_one_iff_unique.mp h_n2_1).1
    have h_card_form : Nat.card G = 2 ^ 2 * q ^ 1 := by aesop
    have h_p_p2 : Nat.card ↥(P : Subgroup G) = 4 := sylow_card_eq (by aesop) h_card_form P
    have h_p_idx_q : ∀ P : Sylow 2 G, (↑P : Subgroup G).index = q := fun P => by
      simpa using sylow_index_eq (by aesop) h_card_form P
    obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime (N := (↑P : Subgroup G)) (by
      rw [h_p_p2, h_p_idx_q]
      exact ((by norm_num : (2 : ℕ).Prime).coprime_of_ne h_q_prime.out (by omega)).pow_left 2)
    have h_iso_g_p_k := SemidirectProduct.mulEquivSubgroup hK
    let φ : ↥K →* MulAut ↥(↑P : Subgroup G) :=
      (↑P : Subgroup G).normalizerMonoidHom.comp
        (Subgroup.inclusion (by simp [Subgroup.normalizer_eq_top]))
    have hK_card : Nat.card ↥K = q := by
      have h1 : Nat.card G = Nat.card ↥(↑P : Subgroup G) * Nat.card ↥K := by
        have heq := Nat.card_congr h_iso_g_p_k.toEquiv
        rw [SemidirectProduct.card] at heq; exact heq.symm
      rw [h_p_p2, h] at h1; grind
    have eK : ↥K ≃* CyclicGroup q := Classical.choice (prime_classification_of_group (n := q) hK_card)
    have h4q : Nat.Coprime 4 q :=
      ((by norm_num : (2 : ℕ).Prime).coprime_of_ne h_q_prime.out (by omega)).pow_left 2
    rcases (p_squared_classification (p := 2) h_p_p2) with h_c4 | h_c2_c2
    · -- P ≅ C_4: Aut(P) ≅ C_2, gcd(q, 2) = 1 forces φ trivial
      simp only [Nat.reducePow] at h_c4
      have h_aut_card : Nat.card (MulAut ↥(↑P : Subgroup G)) = 2 :=
        (Nat.card_congr ((MulAut.congr h_c4.some).trans
          (Classical.choice (aut_of_cyclic_p2 (p := 2)))).toEquiv).trans (card_cyclicGroup 2)
      have h_phi_triv : φ = 1 := eq_one_of_coprime_card (by
        rw [hK_card, h_aut_card]
        exact h_q_prime.out.coprime_of_ne (by norm_num : (2 : ℕ).Prime) (by omega))
      have : G ≃* CyclicGroup (4 * q) := h_iso_g_p_k.symm.trans
        ((SemidirectProduct.mulEquivOfTrivialAction h_phi_triv).trans
          ((h_c4.some.prodCongr eK).trans (CyclicGroup.prodMulEquiv h4q)))
      tauto
    · -- P ≅ C_2 × C_2: Aut(P) ≅ S_3
      have h_aut_dih : Nonempty (MulAut P ≃* DihedralGroup 3) := by
        obtain ⟨e1⟩ := h_c2_c2; obtain ⟨e2⟩ := aut_of_CpCp 2
        exact ⟨((MulAut.congr e1).trans e2).trans GL2F2_isoS3⟩
      have h_mul_aut_p_card : Nat.card (MulAut P) = 6 :=
        h_aut_dih.elim fun e => (Nat.card_congr e.toEquiv).trans (by aesop)
      by_cases h_q_eq_3 : q = 3
      · subst h_q_eq_3; haveI : Fact (Nat.Prime 3) := instFactPrimeThree
        by_cases h_phi_triv : φ = 1
        · have : G ≃* CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 3 := h_iso_g_p_k.symm.trans
            ((SemidirectProduct.mulEquivOfTrivialAction h_phi_triv).trans
              ((h_c2_c2.some.prodCongr eK).trans MulEquiv.prodAssoc))
          tauto
        · let eP := h_c2_c2.some
          let φ' : CyclicGroup 3 →* MulAut (CyclicGroup 2 × CyclicGroup 2) :=
            ((MulAut.congr eP).toMonoidHom).comp (φ.comp eK.symm.toMonoidHom)
          have h_sdp_congr : ↥(↑P : Subgroup G) ⋊[φ] ↥K ≃*
              SemidirectProduct (CyclicGroup 2 × CyclicGroup 2) (CyclicGroup 3) φ' :=
            SemidirectProduct.congr' (φ₁ := φ) (fn := eP) (fg := eK)
          have hφ'_ne : φ' ≠ 1 := transported_action_ne_one eP eK h_phi_triv
          have h_range_card : Nat.card φ'.range = 3 := by
            have h_ne_1 : Nat.card φ'.range ≠ 1 := fun h => hφ'_ne (eq_one_of_range_card_one h)
            have h_dvd : Nat.card φ'.range ∣ 3 := by
              have := Subgroup.card_range_dvd φ'; rwa [card_cyclicGroup] at this
            rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h_dvd with h1 | h3
            · exact absurd h1 h_ne_1
            · exact h3
          obtain ⟨e_phi'_to_canon⟩ := semidirectProduct_C3_on_C2C2_iso φ' canonicalC3OnC2C2Action
            h_range_card canonicalC3OnC2C2Action_range_card
          have : G ≃* (CyclicGroup 2 × CyclicGroup 2) ⋊[canonicalC3OnC2C2Action] CyclicGroup 3 :=
            h_iso_g_p_k.symm.trans (h_sdp_congr.trans e_phi'_to_canon)
          tauto
      · -- q ≠ 3: gcd(q, 6) = 1 forces φ trivial
        have h_phi_triv : φ = 1 := eq_one_of_coprime_card (by
          rw [hK_card, h_mul_aut_p_card]
          have h_cop2 : Nat.Coprime q 2 := h_q_prime.out.coprime_of_ne (by norm_num) (by omega)
          have h_cop3 : Nat.Coprime q 3 := h_q_prime.out.coprime_of_ne (by norm_num) h_q_eq_3
          simpa using h_cop2.mul_right h_cop3)
        have : G ≃* CyclicGroup 2 × CyclicGroup 2 × CyclicGroup q :=
          h_iso_g_p_k.symm.trans
          ((SemidirectProduct.mulEquivOfTrivialAction h_phi_triv).trans
            ((h_c2_c2.some.prodCongr eK).trans MulEquiv.prodAssoc))
        tauto
  · -- n_q = 1: Sylow q-subgroup Q is normal, complement K has order 4
    let Q : Sylow q G := default
    haveI : Subsingleton (Sylow q G) := (Nat.card_eq_one_iff_unique.mp h_nq_1).1
    have h_card_form : Nat.card G = q ^ 1 * 2 ^ 2 := by rw [pow_one, h]; ring
    have h_Q_card : Nat.card ↥(Q : Subgroup G) = q := by
      simpa using sylow_card_eq (Ne.symm (by aesop : (2 : ℕ) ≠ q)) h_card_form Q
    have h_Q_idx_4 : ∀ Q : Sylow q G, (↑Q : Subgroup G).index = 4 := fun Q => by
      simpa using sylow_index_eq (Ne.symm (by aesop : (2 : ℕ) ≠ q)) h_card_form Q
    obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime (N := (↑Q : Subgroup G)) (by
      rw [h_Q_card, h_Q_idx_4]
      exact (h_q_prime.out.coprime_of_ne (by norm_num : (2 : ℕ).Prime) (by omega)).pow_right 2)
    have h_iso_g_q_k := SemidirectProduct.mulEquivSubgroup hK
    let φ : ↥K →* MulAut ↥(↑Q : Subgroup G) :=
      (↑Q : Subgroup G).normalizerMonoidHom.comp
        (Subgroup.inclusion (by simp [Subgroup.normalizer_eq_top]))
    have hK_card : Nat.card ↥K = 4 := by
      have h1 : Nat.card G = Nat.card ↥(↑Q : Subgroup G) * Nat.card ↥K := by
        have heq := Nat.card_congr h_iso_g_q_k.toEquiv
        rw [SemidirectProduct.card] at heq; exact heq.symm
      rw [h_Q_card, h] at h1
      exact (Nat.eq_of_mul_eq_mul_left h_q_prime.out.pos (by linarith)).symm
    have eQ : ↥(↑Q : Subgroup G) ≃* CyclicGroup q :=
      Classical.choice (prime_classification_of_group (n := q) h_Q_card)
    have h4q : Nat.Coprime 4 q :=
      ((by norm_num : (2 : ℕ).Prime).coprime_of_ne h_q_prime.out (by omega)).pow_left 2
    rcases (p_squared_classification (p := 2) hK_card) with h_K_C4 | h_K_C2C2
    · -- K ≅ C_4: transport φ to (CyclicGroup (q^1), CyclicGroup (2^2)) and apply classify_Cqn_rtimes_Cpm
      simp only [Nat.reducePow] at h_K_C4
      haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
      haveI : NeZero (q^1) := ⟨pow_ne_zero 1 h_q_prime.out.ne_zero⟩
      haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
      haveI : NeZero ((2:ℕ)^2) := ⟨pow_ne_zero 2 (by norm_num)⟩
      -- Transport φ : ↥K →* MulAut ↥Q to φ_inter : CyclicGroup 4 →* MulAut (CyclicGroup q)
      let φ_inter : CyclicGroup 4 →* MulAut (CyclicGroup q) :=
        (MulAut.congr eQ).toMonoidHom.comp (φ.comp h_K_C4.some.symm.toMonoidHom)
      have h_bridge_inner : ↥(↑Q : Subgroup G) ⋊[φ] ↥K ≃*
          SemidirectProduct (CyclicGroup q) (CyclicGroup 4) φ_inter :=
        SemidirectProduct.congr' (φ₁ := φ) (fn := eQ) (fg := h_K_C4.some)
      -- Transport φ_inter to φ'' on (CyclicGroup (q^1), CyclicGroup (2^2))
      let φ'' : CyclicGroup ((2:ℕ)^2) →* MulAut (CyclicGroup (q^1)) :=
        transportCpCqHom (rfl : (4:ℕ) = (2:ℕ)^2) (pow_one q).symm φ_inter
      have h_to_idx : SemidirectProduct (CyclicGroup q) (CyclicGroup 4) φ_inter ≃*
          SemidirectProduct (CyclicGroup (q^1)) (CyclicGroup ((2:ℕ)^2)) φ'' :=
        SemidirectProduct.transportCpCqIso (rfl : (4:ℕ) = (2:ℕ)^2) (pow_one q).symm φ_inter
      -- Apply classify_Cqn_rtimes_Cpm
      obtain ⟨⟨rval, hrlt⟩, hr_iso, _⟩ :=
        classify_Cqn_rtimes_Cpm (p := 2) (q := q) (by omega) (by omega) 2 1
          (by norm_num) (by norm_num) φ''
      have h_rval_le_2 : rval ≤ 2 := by
        have h_min_le : min 2 ((q - 1).factorization 2) ≤ 2 := min_le_left _ _
        omega
      interval_cases rval
      · -- r = 0: canonicalAction 0 is trivial → G ≃* C_{4q}
        obtain ⟨e⟩ := hr_iso
        have h_triv :
            canonicalAction 2 q 1 2 (show (2:ℕ) ≠ q by omega) (show q ≠ 2 by omega)
              Nat.one_pos 0 (by simp) = 1 :=
          eq_one_of_range_card_one (by
            rw [canonicalAction_range_card]; norm_num)
        -- Transport SDP from (C q^1, C 2^2) to (C q, C 4) so the product step lands in C (4*q)
        have h_back0 :
            SemidirectProduct (CyclicGroup (q^1)) (CyclicGroup ((2:ℕ)^2))
              (canonicalAction 2 q 1 2 (show (2:ℕ) ≠ q by omega)
                 (show q ≠ 2 by omega) Nat.one_pos 0 (by simp)) ≃*
            SemidirectProduct (CyclicGroup q) (CyclicGroup 4)
              (transportCpCqHom (show ((2:ℕ)^2 : ℕ) = 4 by norm_num) (pow_one q)
                (canonicalAction 2 q 1 2 (show (2:ℕ) ≠ q by omega)
                   (show q ≠ 2 by omega) Nat.one_pos 0 (by simp))) :=
          SemidirectProduct.transportCpCqIso
            (show ((2:ℕ)^2 : ℕ) = 4 by norm_num) (pow_one q) _
        have h_triv_back :
            transportCpCqHom (show ((2:ℕ)^2 : ℕ) = 4 by norm_num) (pow_one q)
              (canonicalAction 2 q 1 2 (show (2:ℕ) ≠ q by omega)
                 (show q ≠ 2 by omega) Nat.one_pos 0 (by simp)) = 1 := by
          rw [h_triv]; exact transportCpCqHom_one _ _
        have : G ≃* CyclicGroup (4 * q) := h_iso_g_q_k.symm.trans (h_bridge_inner.trans
          (h_to_idx.trans (e.trans (h_back0.trans
            ((SemidirectProduct.mulEquivOfTrivialAction h_triv_back).trans
              (MulEquiv.prodComm.trans (CyclicGroup.prodMulEquiv h4q)))))))
        tauto
      · -- r = 1: target canonicalC4OnCqAction
        obtain ⟨e⟩ := hr_iso
        have h_back : SemidirectProduct (CyclicGroup (q^1)) (CyclicGroup ((2:ℕ)^2))
                         (canonicalAction 2 q 1 2 (show (2:ℕ) ≠ q by omega)
                            (show q ≠ 2 by omega) Nat.one_pos 1
                            (one_le_min_two_factorization_two (show q ≠ 2 by omega))) ≃*
                      SemidirectProduct (CyclicGroup q) (CyclicGroup 4)
                         (canonicalC4OnCqAction (show q ≠ 2 by omega)) := by
          show SemidirectProduct _ _ _ ≃* SemidirectProduct _ _
            (transportCpCqHom (show ((2:ℕ)^2 : ℕ) = 4 by norm_num) (pow_one q) _)
          exact (SemidirectProduct.transportCpCqIso
            (show ((2:ℕ)^2 : ℕ) = 4 by norm_num) (pow_one q) _)
        have : G ≃* SemidirectProduct (CyclicGroup q) (CyclicGroup 4)
                         (canonicalC4OnCqAction (by omega : q ≠ 2)) :=
          h_iso_g_q_k.symm.trans (h_bridge_inner.trans (h_to_idx.trans (e.trans h_back)))
        tauto
      · -- r = 2: forces q ≡ 1 (mod 4); target canonicalC4OnCqAction_r2
        have h_vp_ge_2 : 2 ≤ (q - 1).factorization 2 := by
          have h_min_le_vp : min 2 ((q - 1).factorization 2) ≤ (q - 1).factorization 2 :=
            min_le_right _ _
          omega
        have h_1_mod_4 : q ≡ 1 [MOD 4] := by
          have h_qm1_ne : q - 1 ≠ 0 := by have := h_q_prime.out.one_lt; omega
          have h_4_dvd : (4 : ℕ) ∣ q - 1 := by
            have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two h_qm1_ne).mpr h_vp_ge_2
            simpa [show (2 : ℕ) ^ 2 = 4 by norm_num] using this
          unfold Nat.ModEq; omega
        obtain ⟨e⟩ := hr_iso
        have h_back : SemidirectProduct (CyclicGroup (q^1)) (CyclicGroup ((2:ℕ)^2))
                         (canonicalAction 2 q 1 2
                            (show (2 : ℕ) ≠ q from by
                              simp [Nat.ModEq] at h_1_mod_4; omega)
                            (show q ≠ 2 from by
                              simp [Nat.ModEq] at h_1_mod_4; omega)
                            Nat.one_pos 2
                            (two_le_min_two_factorization_two_of_one_mod_four h_1_mod_4)) ≃*
                      SemidirectProduct (CyclicGroup q) (CyclicGroup 4)
                         (canonicalC4OnCqAction_r2 h_1_mod_4) := by
          show SemidirectProduct _ _ _ ≃* SemidirectProduct _ _
            (transportCpCqHom (show ((2:ℕ)^2 : ℕ) = 4 by norm_num) (pow_one q) _)
          exact (SemidirectProduct.transportCpCqIso
            (show ((2:ℕ)^2 : ℕ) = 4 by norm_num) (pow_one q) _)
        have : G ≃* SemidirectProduct (CyclicGroup q) (CyclicGroup 4)
                            (canonicalC4OnCqAction_r2 h_1_mod_4) :=
          h_iso_g_q_k.symm.trans (h_bridge_inner.trans (h_to_idx.trans (e.trans h_back)))
        tauto
    · -- K ≅ C_2 × C_2
      by_cases h_phi_triv : φ = 1
      · have : G ≃* CyclicGroup 2 × CyclicGroup 2 × CyclicGroup q := h_iso_g_q_k.symm.trans
          ((SemidirectProduct.mulEquivOfTrivialAction h_phi_triv).trans
            ((eQ.prodCongr h_K_C2C2.some).trans
              (MulEquiv.prodComm.trans MulEquiv.prodAssoc)))
        tauto
      · let eK := h_K_C2C2.some
        let φ' : CyclicGroup 2 × CyclicGroup 2 →* MulAut (CyclicGroup q) :=
          ((MulAut.congr eQ).toMonoidHom).comp (φ.comp eK.symm.toMonoidHom)
        have h_sdp_congr : ↥(↑Q : Subgroup G) ⋊[φ] ↥K ≃*
            SemidirectProduct (CyclicGroup q) (CyclicGroup 2 × CyclicGroup 2) φ' :=
          SemidirectProduct.congr' (φ₁ := φ) (fn := eQ) (fg := eK)
        have hφ'_ne : φ' ≠ 1 := transported_action_ne_one eQ eK h_phi_triv
        have h_range_dvd_2 : Nat.card φ'.range ∣ 2 := range_card_dvd_two_of_C2C2_hom φ'
        have h_range_card : Nat.card φ'.range = 2 := by
          have h_ne_1 : Nat.card φ'.range ≠ 1 := fun h => hφ'_ne (eq_one_of_range_card_one h)
          have h_pos : 0 < Nat.card φ'.range := Nat.card_pos
          have h_le_2 : Nat.card φ'.range ≤ 2 := Nat.le_of_dvd (by norm_num) h_range_dvd_2
          omega
        obtain ⟨e_phi'_to_canon⟩ :=
          sdpCanonicalAction_iso_canonicalC2C2OnCqAction
            (q := q) (by omega : q ≠ 2) φ' hφ'_ne h_range_card
        have : G ≃* SemidirectProduct (CyclicGroup q) (CyclicGroup 2 × CyclicGroup 2)
                         (canonicalC2C2OnCqAction (by omega : q ≠ 2)) :=
          h_iso_g_q_k.symm.trans (h_sdp_congr.trans e_phi'_to_canon)
        tauto
