import Mathlib
import «M2rGroup7».Lemmas.GroupTheoryLemmas
import «M2rGroup7».Lemmas.ClassificationUtils
import «M2rGroup7».Lemmas.HomomorphismUtils
import «M2rGroup7».P2qClassification.CycPGroupClassification
import OrderPQ

/-!
# Classification of groups of order p * q (p < q primes)

Every group G of order p * q is isomorphic to exactly one of:
- `CyclicGroup (p * q)` — always a valid class.
- `SemidirectProduct (CyclicGroup q) (CyclicGroup p) (canonicalCpOnCqAction ...)` — the unique
  non-abelian group, existing iff p ∣ q - 1.

The condition p ∣ q - 1 is encoded by `hr : 1 ≤ min 1 ((q-1).factorization p)`.

`canonicalCpOnCqAction` is built directly from `sdpCanonicalAction` (n = m = 1, r = 1),
eliminating the old bridge infrastructure (cycGrpPowOne, _canonicalCpOnCqAction, canonicalAction_r_iso).

**Usage**: supply the two primes directly, e.g. `pq_classification (p := 2) (q := 7) hlt h`.
-/

-- ─── Canonical action C_p →* Aut(C_q) ──────────────────────────────────────

/-- Generic transport: for `CyclicGroup` types parameterized by ℕ with `NeZero`,
    along `p1 = p` and `q1 = q` (with `NeZero p1`, `NeZero q1` already in scope, and
    `NeZero p`, `NeZero q` derived from primality below). Both endpoints have `NeZero`
    so the transport via `Eq.rec` on each is well-typed.

    This is computable: `Eq.mpr` on a propositionally-equal type is a computational
    no-op at the byte-code level once both indices match. -/
private def transportCpCqHom {p q p1 q1 : ℕ} [NeZero p] [NeZero q] [NeZero p1] [NeZero q1]
    (hp : p1 = p) (hq : q1 = q)
    (f : CyclicGroup p1 →* MulAut (CyclicGroup q1)) :
    CyclicGroup p →* MulAut (CyclicGroup q) := by
  subst hp
  subst hq
  exact f

/-- The canonical non-trivial action `C_p →* Aut(C_q)` with image of order p.
    Exists when `p ∣ q - 1`, encoded by `hr : 1 ≤ min 1 ((q-1).factorization p)`.
    Built by transporting `canonicalAction p q 1 1 r=1` across `p^1 = p` and `q^1 = q`. -/
def canonicalCpOnCqAction
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hq2 : q ≠ 2)
    (hr : 1 ≤ min 1 ((q - 1).factorization p)) :
    CyclicGroup p →* MulAut (CyclicGroup q) :=
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  haveI : NeZero (p^1) := ⟨pow_ne_zero 1 hp.out.ne_zero⟩
  haveI : NeZero (q^1) := ⟨pow_ne_zero 1 hq.out.ne_zero⟩
  transportCpCqHom (pow_one p) (pow_one q)
    (canonicalAction p q 1 1 hpq hq2 Nat.one_pos 1 hr)

-- ─── General: non-trivial action → non-cyclic SDP ───────────────────────────

/-- A semidirect product with a non-trivial action is non-cyclic (it is non-abelian). -/
lemma sdp_not_isCyclic_of_action_ne_one
    {N K : Type*} [Group N] [Group K]
    {φ : K →* MulAut N} (h_ne : φ ≠ 1) :
    ¬IsCyclic (SemidirectProduct N K φ) := by
  intro h_cyc
  obtain ⟨k, h_k⟩ : ∃ k : K, φ k ≠ 1 := by
    by_contra h_all; push Not at h_all
    exact h_ne (MonoidHom.ext fun k => MulEquiv.ext fun n => by
      have := MulEquiv.ext_iff.mp (h_all k)
      simp only [MulAut.one_apply] at this; exact this n)
  obtain ⟨n, h_n⟩ : ∃ n : N, φ k n ≠ n := by
    by_contra h_all; push Not at h_all
    exact h_k (MulEquiv.ext fun n => h_all n)
  have h_not_comm :
      (⟨n, 1⟩ : SemidirectProduct N K φ) * ⟨1, k⟩ ≠ ⟨1, k⟩ * ⟨n, 1⟩ := by
    intro h_eq
    apply h_n
    have := congr_arg SemidirectProduct.left h_eq
    simp [SemidirectProduct.mul_left, map_one] at this
    exact this.symm
  haveI := h_cyc
  exact h_not_comm (IsCyclic.commutative.comm _ _)

-- ─── Key lemmas about the canonical SDP ─────────────────────────────────────

lemma canonicalSDP_card
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hq2 : q ≠ 2)
    (hr : 1 ≤ min 1 ((q - 1).factorization p)) :
    Nat.card (SemidirectProduct (CyclicGroup q) (CyclicGroup p)
               (canonicalCpOnCqAction hpq hq2 hr)) = p * q := by
  rw [SemidirectProduct.card, card_cyclicGroup, card_cyclicGroup, mul_comm]

/-- Range cardinality is invariant under `transportCpCqHom`. -/
private lemma transportCpCqHom_range_card {p q p1 q1 : ℕ}
    [NeZero p] [NeZero q] [NeZero p1] [NeZero q1]
    (hp : p1 = p) (hq : q1 = q)
    (f : CyclicGroup p1 →* MulAut (CyclicGroup q1)) :
    Nat.card (transportCpCqHom hp hq f).range = Nat.card f.range := by
  subst hp; subst hq; rfl

lemma canonicalSDP_not_isCyclic
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hq2 : q ≠ 2)
    (hr : 1 ≤ min 1 ((q - 1).factorization p)) :
    ¬IsCyclic (SemidirectProduct (CyclicGroup q) (CyclicGroup p)
                (canonicalCpOnCqAction hpq hq2 hr)) := by
  apply sdp_not_isCyclic_of_action_ne_one
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  haveI : NeZero (p^1) := ⟨pow_ne_zero 1 hp.out.ne_zero⟩
  haveI : NeZero (q^1) := ⟨pow_ne_zero 1 hq.out.ne_zero⟩
  -- canonicalCpOnCqAction transports canonicalAction p q 1 1 r=1 across pow_one rewrites;
  -- the range card is p^1 = p (after transport), so ≠ 1, hence the action is not trivial.
  have h_card_orig : Nat.card (canonicalAction p q 1 1 hpq hq2 Nat.one_pos 1 hr).range = p := by
    have h := canonicalAction_range_card p q 1 1 1 hpq hq2 Nat.one_pos hr
    simpa using h
  have h_card' : Nat.card (canonicalCpOnCqAction hpq hq2 hr).range = p := by
    unfold canonicalCpOnCqAction
    rw [transportCpCqHom_range_card]
    exact h_card_orig
  intro heq
  have h_range : (1 : CyclicGroup p →* MulAut (CyclicGroup q)).range = ⊥ := by
    ext x; simp [Subgroup.mem_bot]
  rw [heq, h_range, Subgroup.card_bot] at h_card'
  linarith [hp.out.one_lt]

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
                       (canonicalCpOnCqAction (Nat.ne_of_lt hlt)
                                              (by linarith [hp.out.two_le]) hr)) := by
  have hpq : p ≠ q := Nat.ne_of_lt hlt
  have hq2 : q ≠ 2 := by linarith [hp.out.two_le]
  by_cases hc : IsCyclic G
  · left
    haveI := hc
    exact ⟨mulEquivOfCyclicCardEq (h.trans (card_cyclicGroup _).symm)⟩
  · have h_pdvd : p ∣ q - 1 := by
      by_contra h_ndvd
      exact hc (isCyclic_of_card_eq_prime_mul_prime hlt h_ndvd h)
    have h_fac : 1 ≤ (q - 1).factorization p :=
      (hp.out.pow_dvd_iff_le_factorization (Nat.sub_pos_of_lt hq.out.one_lt).ne').mp
        (by simpa [pow_one])
    have hr : 1 ≤ min 1 ((q - 1).factorization p) := Nat.le_min.mpr ⟨le_refl 1, h_fac⟩
    right; refine ⟨hr, ?_⟩
    exact nonempty_mulEquiv_of_card_eq_prime_mul_prime_of_not_isCyclic'
      hlt h hc (canonicalSDP_card hpq hq2 hr) (canonicalSDP_not_isCyclic hpq hq2 hr)
