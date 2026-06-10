import Mathlib
import «M2rGroup7».Lemmas.GroupTheoryLemmas
import «M2rGroup7».Lemmas.ClassificationUtils
import «M2rGroup7».Lemmas.HomomorphismUtils
import «M2rGroup7».Lemmas.SylowUtils
import «M2rGroup7».P2qClassification.CycPGroupClassification

/-!
# Classification of groups of order p * q (p < q primes)

Every group G of order p * q is isomorphic to exactly one of:
- `CyclicGroup (p * q)` — always a valid class.
- `SemidirectProduct (CyclicGroup q) (CyclicGroup p) (canonicalCpOnCqAction ...)` — the unique
  non-abelian group, existing iff p ∣ q - 1.

The condition p ∣ q - 1 is encoded by `hr : 1 ≤ min 1 ((q-1).factorization p)`.

`canonicalCpOnCqAction` is built directly from `canonicalAction` (n = m = 1, r = 1),
eliminating the old bridge infrastructure (cycGrpPowOne, _canonicalCpOnCqAction,
canonicalAction_r_iso).

**Usage**: supply the two primes directly, e.g. `pq_classification (p := 2) (q := 7) hlt h`.
-/

-- ─── Canonical action C_p →* Aut(C_q) ──────────────────────────────────────

/-- The canonical non-trivial action `C_p →* Aut(C_q)` with image of order p.
    Exists when `p ∣ q - 1`, encoded by `hr : 1 ≤ min 1 ((q-1).factorization p)`.
    Built by transporting `canonicalAction p q 1 1 r=1` across `p^1 = p` and `q^1 = q`. -/
def canonicalCpOnCqAction
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hq2 : q ≠ 2)
    (hr : 1 ≤ min 1 ((q - 1).factorization p)) :
    CyclicGroup p →* MulAut (CyclicGroup q) :=
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  haveI : NeZero (p^1) := ⟨pow_ne_zero 1 hp.out.ne_zero⟩
  haveI : NeZero (q^1) := ⟨pow_ne_zero 1 hq.out.ne_zero⟩
  transportCpCqHom (pow_one p) (pow_one q)
    (canonicalAction p q 1 1 hq2 Nat.one_pos 1 hr)

-- ─── Main classification theorem ─────────────────────────────────────────────

/-- **Classification of groups of order p * q** (p < q primes).

A group G of order p * q is isomorphic to:
- `CyclicGroup (p * q)` — always one isomorphism class.
- `SemidirectProduct (CyclicGroup q) (CyclicGroup p) (canonicalCpOnCqAction ...)` — the unique
  non-abelian group, only when `p ∣ q - 1`. -/
theorem pq_classification
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hlt : p < q)
    {G : Type*} [Group G] (h : Nat.card G = p * q) :
    Nonempty (G ≃* CyclicGroup (p * q)) ∨
    ∃ (hr : 1 ≤ min 1 ((q - 1).factorization p)),
      Nonempty (G ≃* SemidirectProduct (CyclicGroup q) (CyclicGroup p)
                       (canonicalCpOnCqAction
                         (by linarith [hp.out.two_le]) hr)) := by
  have hpq : p ≠ q := Nat.ne_of_lt hlt
  have hq2 : q ≠ 2 := by linarith [hp.out.two_le]
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  haveI : NeZero (p ^ 1) := ⟨pow_ne_zero 1 hp.out.ne_zero⟩
  haveI : NeZero (q ^ 1) := ⟨pow_ne_zero 1 hq.out.ne_zero⟩
  haveI : Finite G :=
    Nat.finite_of_card_ne_zero (h ▸ Nat.mul_ne_zero hp.out.ne_zero hq.out.ne_zero)
  -- The Sylow-q subgroup is normal (Lemma `pq_group_has_normal_sylow_q_subgroup`).
  have hnq : Nat.card (Sylow q G) = 1 := pq_group_has_normal_sylow_q_subgroup G hlt h
  let Q : Sylow q G := default
  haveI : Subsingleton (Sylow q G) := (Nat.card_eq_one_iff_unique.mp hnq).1
  have h_card_form : Nat.card G = q ^ 1 * p ^ 1 := by rw [pow_one, pow_one, h, mul_comm]
  have h_Q_card : Nat.card ↥(Q : Subgroup G) = q := by
    simpa using sylow_card_eq (Ne.symm hpq) h_card_form Q
  have h_Q_idx_p : (↑Q : Subgroup G).index = p := by
    simpa using sylow_index_eq (Ne.symm hpq) h_card_form Q
  -- A complement K to Q has order p, by Schur-Zassenhaus.
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime (N := (↑Q : Subgroup G)) (by
    rw [h_Q_card, h_Q_idx_p]
    exact hq.out.coprime_of_ne hp.out hpq.symm)
  have h_iso_g_q_k := SemidirectProduct.mulEquivSubgroup hK
  let φ : ↥K →* MulAut ↥(↑Q : Subgroup G) :=
    (↑Q : Subgroup G).normalizerMonoidHom.comp
      (Subgroup.inclusion (by simp [Subgroup.normalizer_eq_top]))
  have hK_card : Nat.card ↥K = p := by
    have h1 : Nat.card G = Nat.card ↥(↑Q : Subgroup G) * Nat.card ↥K := by
      have heq := Nat.card_congr h_iso_g_q_k.toEquiv
      rw [SemidirectProduct.card] at heq; exact heq.symm
    rw [h_Q_card, h] at h1
    exact (Nat.eq_of_mul_eq_mul_left hq.out.pos (by linarith)).symm
  have eQ : ↥(↑Q : Subgroup G) ≃* CyclicGroup q :=
    Classical.choice (prime_classification_of_group (n := q) h_Q_card)
  have eK : ↥K ≃* CyclicGroup p :=
    Classical.choice (prime_classification_of_group (n := p) hK_card)
  -- Bridge G ≅ Q ⋊ K to a semidirect product on the abstract cyclic groups.
  let φ_inter : CyclicGroup p →* MulAut (CyclicGroup q) :=
    (MulAut.congr eQ).toMonoidHom.comp (φ.comp eK.symm.toMonoidHom)
  have h_congr : ↥(↑Q : Subgroup G) ⋊[φ] ↥K ≃*
      SemidirectProduct (CyclicGroup q) (CyclicGroup p) φ_inter :=
    SemidirectProduct.congr' (φ₁ := φ) (fn := eQ) (fg := eK)
  -- Classify φ_inter via `classify_Cqn_rtimes_Cpm` (m = n = 1).
  have h_pre_iso := SemidirectProduct.transportCpCqIso (pow_one p).symm (pow_one q).symm φ_inter
  obtain ⟨⟨r, hr_lt⟩, ⟨e_pre⟩, _⟩ := classify_Cqn_rtimes_Cpm (p := p) (q := q) hpq hq2 1 1
    Nat.one_pos (transportCpCqHom (pow_one p).symm (pow_one q).symm φ_inter)
  have hr_le : r ≤ min 1 ((q - 1).factorization p) := Nat.lt_succ_iff.mp hr_lt
  let e_back := SemidirectProduct.transportCpCqIso (pow_one p) (pow_one q)
    (canonicalAction p q 1 1 hq2 Nat.one_pos r hr_le)
  let pre := h_iso_g_q_k.symm.trans (h_congr.trans (h_pre_iso.trans (e_pre.trans e_back)))
  have hr_le_1 : r ≤ 1 := hr_le.trans (min_le_left _ _)
  interval_cases r
  · -- r = 0: trivial action → G ≃* C_{p * q}
    have h_triv := eq_one_of_range_card_one (by
      change Nat.card (transportCpCqHom (pow_one p) (pow_one q)
        (canonicalAction p q 1 1 hq2 Nat.one_pos 0 hr_le)).range = 1
      rw [transportCpCqHom_range_card]
      simpa using canonicalAction_range_card p q 1 1 0 hq2 Nat.one_pos hr_le)
    have hcop : Nat.Coprime q p := hq.out.coprime_of_ne hp.out hpq.symm
    left
    exact ⟨pre.trans ((SemidirectProduct.mulEquivOfTrivialAction h_triv).trans
      ((CyclicGroup.prodMulEquiv hcop).trans
        (mulEquivOfCyclicCardEq (by rw [card_cyclicGroup, card_cyclicGroup, mul_comm]))))⟩
  · -- r = 1: matches `canonicalCpOnCqAction` definitionally.
    right
    exact ⟨hr_le, ⟨pre⟩⟩
