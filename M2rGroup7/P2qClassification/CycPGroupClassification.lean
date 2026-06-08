import Mathlib
import «M2rGroup7».Lemmas.GroupTheoryLemmas
import «M2rGroup7».Lemmas.ClassificationUtils
import «M2rGroup7».Lemmas.HomomorphismUtils

/-- Computable isomorphism `MulAut (CyclicGroup n) ≃* (ZMod n)ˣ`. This composes
`MulAutMultiplicative (ZMod n)` (which converts `MulAut (Multiplicative (ZMod n))` to
`AddAut (ZMod n)`) with `ZMod.AddAutEquivUnits n`. Both factors are computable. -/
def cyclicGroupAutEquivUnits (n : ℕ) [NeZero n] : MulAut (CyclicGroup n) ≃* (ZMod n)ˣ :=
  (MulAutMultiplicative (ZMod n)).trans (ZMod.AddAutEquivUnits n)

/-- Core existence: for each r ≤ v_p(q-1), there is an element of Aut(C_{q^n}) of order exactly p^r.
    Construction: Aut(C_{q^n}) ≃* (ZMod q^n)ˣ is cyclic of order q^{n-1}(q-1);
    a generator α raised to the power |Aut|/p^r has order exactly p^r. -/
private lemma canonicalAutElement_exists
    (p q n r : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hq_odd : q ≠ 2) (hn : 0 < n)
    (hr : r ≤ (q - 1).factorization p) :
    ∃ τ : MulAut (CyclicGroup (q ^ n)), orderOf τ = p ^ r := by
  have h_aut_iso : MulAut (CyclicGroup (q ^ n)) ≃* (ZMod (q ^ n))ˣ := by
    have h := IsCyclic.mulAutMulEquiv (CyclicGroup (q ^ n))
    rwa [card_cyclicGroup] at h
  haveI : IsCyclic (ZMod (q ^ n))ˣ :=
    ZMod.isCyclic_units_of_prime_pow q hq.out hq_odd n
  haveI : Finite (MulAut (CyclicGroup (q ^ n))) :=
    Finite.of_equiv _ h_aut_iso.toEquiv.symm
  let α₀ := (IsCyclic.exists_generator (α := (ZMod (q ^ n))ˣ)).choose
  have hα₀ := (IsCyclic.exists_generator (α := (ZMod (q ^ n))ˣ)).choose_spec
  let α := h_aut_iso.symm α₀
  have hα : ∀ x, x ∈ Subgroup.zpowers α := fun x => by
    have hmem := hα₀ (h_aut_iso x)
    rw [Subgroup.mem_zpowers_iff] at hmem ⊢
    obtain ⟨z, hz⟩ := hmem
    exact ⟨z, by rw [show α = h_aut_iso.symm α₀ from rfl, ← map_zpow, hz, MulEquiv.symm_apply_apply]⟩
  have h_orderOf_α : orderOf α = Nat.card (MulAut (CyclicGroup (q ^ n))) := by
    have hzpow_top : (Subgroup.zpowers α : Subgroup _) = ⊤ :=
      (Subgroup.eq_top_iff' _).mpr hα
    rw [← Nat.card_zpowers, hzpow_top, Nat.card_congr Subgroup.topEquiv.toEquiv]
  have h_pr_dvd : p ^ r ∣ Nat.card (MulAut (CyclicGroup (q ^ n))) := by
    have h_card : Nat.card (MulAut (CyclicGroup (q ^ n))) = (q ^ n).totient := by
      rw [Nat.card_congr h_aut_iso.toEquiv, Nat.card_eq_fintype_card,
          ZMod.card_units_eq_totient]
    have h_totient : (q ^ n).totient = q ^ (n - 1) * (q - 1) := by
      have := Nat.totient_prime_pow_succ hq.out (n - 1)
      rwa [Nat.sub_add_cancel hn] at this
    rw [h_card, h_totient]
    exact dvd_mul_of_dvd_right
      ((hp.out.pow_dvd_iff_le_factorization (Nat.sub_pos_of_lt hq.out.one_lt).ne').mpr hr) _
  set aut_card := Nat.card (MulAut (CyclicGroup (q ^ n)))
  have h_aut_card_pos : 0 < aut_card := Nat.card_pos
  have h_pos : 0 < aut_card / p ^ r :=
    Nat.div_pos (Nat.le_of_dvd h_aut_card_pos h_pr_dvd) (pow_pos hp.out.pos r)
  have h_dvd_aut : aut_card / p ^ r ∣ orderOf α := by
    rw [h_orderOf_α]; exact Nat.div_dvd_of_dvd h_pr_dvd
  have h_orderOf_target : orderOf (α ^ (aut_card / p ^ r)) = p ^ r := by
    rw [orderOf_pow_of_dvd h_pos.ne' h_dvd_aut, h_orderOf_α]
    nth_rw 1 [show aut_card = aut_card / p ^ r * p ^ r from (Nat.div_mul_cancel h_pr_dvd).symm]
    exact Nat.mul_div_cancel_left (p ^ r) h_pos
  exact ⟨α ^ (aut_card / p ^ r), h_orderOf_target⟩

/-- Computable predicate: a unit has order exactly `p^r` (for prime `p`). We use the
    characterization: `u^(p^r) = 1` and either `r = 0` (then we need `u = 1`, i.e. `u^p^0 = u = 1`)
    or `u^(p^(r-1)) ≠ 1` (so the order is exactly `p^r`, not smaller dividing). -/
private def hasOrderPrimePow {n : ℕ} (p r : ℕ) (u : (ZMod n)ˣ) : Bool :=
  decide (u ^ (p ^ r) = 1) && decide (r = 0 ∨ u ^ (p ^ (r - 1)) ≠ 1)

/-- Helper: pick the first unit u ∈ list with order = p^r (using `hasOrderPrimePow`). -/
private def findFirstUnitWithOrder {n : ℕ} (p r : ℕ) :
    List (ZMod n)ˣ → (ZMod n)ˣ
  | [] => 1
  | u :: tl => if hasOrderPrimePow p r u then u else findFirstUnitWithOrder p r tl

/-- Computable enumeration: pick the first unit `u : (ZMod (q^n))ˣ` whose order equals `p^r`.
    Falls back to `1` when none exists (unreachable under the canonical hypotheses). -/
private def canonicalAutElement_unit (p q n r : ℕ) [Fact q.Prime] (hn : 0 < n) :
    (ZMod (q ^ n))ˣ :=
  haveI : NeZero (q ^ n) := ⟨pow_ne_zero n (Fact.out (p := q.Prime)).ne_zero⟩
  -- Enumerate i ∈ {0, ..., q^n - 1}, keep those coprime to q^n (these give units),
  -- and pick the first unit with order = p^r.
  let candidates : List (ZMod (q^n))ˣ :=
    (List.range (q^n)).filterMap (fun i =>
      if h : Nat.Coprime i (q^n) then some (ZMod.unitOfCoprime i h) else none)
  findFirstUnitWithOrder p r candidates

/-- The canonical element of Aut(C_{q^n}) of order p^r, for r ≤ v_p(q-1). Computable. -/
def canonicalAutElement
    (p q n r : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hq_odd : q ≠ 2) (hn : 0 < n)
    (hr : r ≤ (q - 1).factorization p) :
    MulAut (CyclicGroup (q ^ n)) :=
  haveI : NeZero (q ^ n) := ⟨pow_ne_zero n hq.out.ne_zero⟩
  (cyclicGroupAutEquivUnits (q ^ n)).symm (canonicalAutElement_unit p q n r hn)

/-- Characterization: for prime `p`, `hasOrderPrimePow p r u = true ↔ orderOf u = p^r`. -/
private lemma hasOrderPrimePow_iff {n : ℕ} (p r : ℕ) [hp : Fact p.Prime] (u : (ZMod n)ˣ) :
    hasOrderPrimePow p r u = true ↔ orderOf u = p ^ r := by
  unfold hasOrderPrimePow
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    -- orderOf u divides p^r (from h1), and is either p^r (good) or smaller (then divides
    -- p^(r-1), contradicting h2 unless r=0).
    have h_dvd : orderOf u ∣ p ^ r := orderOf_dvd_iff_pow_eq_one.mpr h1
    rcases (Nat.dvd_prime_pow hp.out).mp h_dvd with ⟨k, hkle, hk_eq⟩
    rcases Nat.lt_or_ge k r with hlt | hge
    · -- k < r → orderOf u | p^(r-1), so u^(p^(r-1)) = 1, contradicting h2 (unless r = 0)
      rcases h2 with hr0 | hne
      · -- r = 0: then k ≤ r = 0, so k = 0, so orderOf u = p^0 = 1
        rw [hr0]; rw [hr0] at hkle; interval_cases k; simp [hk_eq]
      · exfalso; apply hne
        rw [← orderOf_dvd_iff_pow_eq_one, hk_eq]
        exact pow_dvd_pow p (Nat.le_sub_one_of_lt hlt)
    · -- k ≥ r and k ≤ r, so k = r
      rw [hk_eq, show k = r from le_antisymm hkle hge]
  · intro h_ord
    refine ⟨?_, ?_⟩
    · rw [← h_ord]; exact pow_orderOf_eq_one u
    · rcases Nat.eq_zero_or_pos r with rfl | hr_pos
      · left; rfl
      · right
        intro h_eq
        have h_dvd : orderOf u ∣ p ^ (r - 1) := orderOf_dvd_iff_pow_eq_one.mpr h_eq
        rw [h_ord] at h_dvd
        -- p^r ∣ p^(r-1) is false
        have : r ≤ r - 1 := (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp h_dvd
        omega

/-- If a list contains some unit with order `p^r`, then `findFirstUnitWithOrder` returns
    a unit whose order equals `p^r`. -/
private lemma findFirstUnitWithOrder_orderOf {n : ℕ} (p r : ℕ) [Fact p.Prime]
    (L : List (ZMod n)ˣ) (h : ∃ u ∈ L, orderOf u = p ^ r) :
    orderOf (findFirstUnitWithOrder p r L) = p ^ r := by
  induction L with
  | nil => obtain ⟨u, hu, _⟩ := h; exact absurd hu (List.not_mem_nil)
  | cons u tl ih =>
    unfold findFirstUnitWithOrder
    split_ifs with hcase
    · exact (hasOrderPrimePow_iff p r u).mp hcase
    · apply ih
      obtain ⟨v, hv_mem, hv_ord⟩ := h
      rw [List.mem_cons] at hv_mem
      rcases hv_mem with rfl | hv_tl
      · exact absurd ((hasOrderPrimePow_iff p r v).mpr hv_ord) hcase
      · exact ⟨v, hv_tl, hv_ord⟩

lemma canonicalAutElement_orderOf
    (p q n r : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hq_odd : q ≠ 2) (hn : 0 < n)
    (hr : r ≤ (q - 1).factorization p) :
    orderOf (canonicalAutElement p q n r hpq hq_odd hn hr) = p ^ r := by
  haveI : NeZero (q ^ n) := ⟨pow_ne_zero n hq.out.ne_zero⟩
  -- Bridge to the existence proof: transport to (ZMod (q^n))ˣ.
  show orderOf ((cyclicGroupAutEquivUnits (q ^ n)).symm (canonicalAutElement_unit p q n r hn))
      = p ^ r
  rw [(cyclicGroupAutEquivUnits (q ^ n)).symm.orderOf_eq]
  show orderOf (canonicalAutElement_unit p q n r hn) = p ^ r
  -- The unit comes from the candidates list; we show the candidates list contains some
  -- unit with order p^r (transported from canonicalAutElement_exists), then apply
  -- findFirstUnitWithOrder_orderOf.
  obtain ⟨τ, hτ⟩ := canonicalAutElement_exists p q n r hpq hq_odd hn hr
  let u₀ : (ZMod (q^n))ˣ := cyclicGroupAutEquivUnits (q^n) τ
  have hu₀ : orderOf u₀ = p ^ r := by
    show orderOf (cyclicGroupAutEquivUnits (q^n) τ) = p ^ r
    rw [(cyclicGroupAutEquivUnits (q^n)).orderOf_eq]; exact hτ
  -- Show u₀ appears in the candidates list. Let i = u₀.val.val (the underlying ℕ).
  set i : ℕ := (u₀.val.val) with hi_def
  have hi_lt : i < q ^ n := by
    rw [hi_def]; exact ZMod.val_lt (u₀.val)
  -- u₀ corresponds to a unit, so i is coprime with q^n.
  have hcop : Nat.Coprime i (q ^ n) := by
    rw [hi_def]
    exact (ZMod.val_coe_unit_coprime u₀)
  -- ZMod.unitOfCoprime i hcop = u₀
  have h_unit_eq : ZMod.unitOfCoprime i hcop = u₀ := by
    apply Units.ext
    show ((ZMod.unitOfCoprime i hcop : ZMod (q ^ n)) : ZMod (q ^ n)) = (u₀ : ZMod (q ^ n))
    rw [ZMod.coe_unitOfCoprime]
    rw [hi_def]
    exact (ZMod.natCast_zmod_val (u₀ : ZMod (q ^ n)))
  -- Build the candidates list and show u₀ is in it.
  show orderOf (canonicalAutElement_unit p q n r hn) = p ^ r
  unfold canonicalAutElement_unit
  apply findFirstUnitWithOrder_orderOf
  refine ⟨u₀, ?_, hu₀⟩
  rw [List.mem_filterMap]
  refine ⟨i, ?_, ?_⟩
  · exact List.mem_range.mpr hi_lt
  · simp only [dif_pos hcop, h_unit_eq]

/-- For each r ≤ min(m, d) where d = v_p(q-1), the canonical action
    φ_r : C_{p^m} →* Aut(C_{q^n}) with image of order p^r. Computable.

    Built via `cyclicHom (p^m)` applied to `canonicalAutElement r`, whose `p^m`-th power
    is `1` because its order divides `p^m`. -/
def canonicalAction
    (p q n m : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hq_odd : q ≠ 2) (hn : 0 < n)
    (r : ℕ) (hr : r ≤ min m ((q - 1).factorization p)) :
    CyclicGroup (p ^ m) →* MulAut (CyclicGroup (q ^ n)) :=
  haveI : NeZero (p ^ m) := ⟨pow_ne_zero m hp.out.ne_zero⟩
  let τ := canonicalAutElement p q n r hpq hq_odd hn (hr.trans (min_le_right m _))
  cyclicHom (p ^ m) τ (by
    have h_ord : orderOf τ = p ^ r := canonicalAutElement_orderOf p q n r hpq hq_odd hn _
    have h_dvd : τ ^ p ^ m = 1 := by
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [h_ord]
      exact pow_dvd_pow p (hr.trans (min_le_left m _))
    exact h_dvd)

/-- For any `cyclicHom n a h`, applied at `x : CyclicGroup n`, we get `a ^ (toAdd x).val`. -/
lemma cyclicHom_apply_eq_zpow
    (n : Nat) [NeZero n] {G : Type*} [Group G] (a : G) (h : a ^ n = 1) (x : CyclicGroup n) :
    cyclicHom n a h x = a ^ ((Multiplicative.toAdd x).val : ℤ) := by
  show Additive.toMul ((ZMod.lift n
      ⟨zmultiplesHom (Additive G) (Additive.ofMul a),
        by change (n : ℤ) • Additive.ofMul a = 0
           rw [← ofMul_zpow, zpow_natCast, h, ofMul_one]⟩) (Multiplicative.toAdd x))
      = a ^ ((Multiplicative.toAdd x).val : ℤ)
  set m : ℕ := (Multiplicative.toAdd x).val with hm
  conv_lhs => rw [show (Multiplicative.toAdd x : ZMod n) = (((m : ℤ) : ZMod n)) from by
    push_cast; exact (ZMod.natCast_zmod_val _).symm]
  rw [ZMod.lift_coe]
  rw [zmultiplesHom_apply, ← ofMul_zpow]
  rfl

/-- Helper: `Multiplicative.ofAdd 1` generates `CyclicGroup n` as zpowers. -/
private lemma ofAdd_one_zpowers_top (n : Nat) [NeZero n] :
    (Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod n)) : Subgroup (CyclicGroup n)) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro x
  refine Subgroup.mem_zpowers_iff.mpr ⟨((Multiplicative.toAdd x).val : ℤ), ?_⟩
  show Multiplicative.ofAdd (1 : ZMod n) ^ ((Multiplicative.toAdd x).val : ℤ) = x
  rw [← Multiplicative.ofAdd.apply_symm_apply x]
  show Multiplicative.ofAdd (1 : ZMod n) ^ ((Multiplicative.toAdd x).val : ℤ)
      = Multiplicative.ofAdd (Multiplicative.toAdd x)
  rw [← ofAdd_zsmul, zsmul_one]
  congr 1
  push_cast
  exact ZMod.natCast_zmod_val _

/-- The range of `cyclicHom n a h` equals `Subgroup.zpowers a`. -/
lemma cyclicHom_range (n : Nat) [NeZero n] {G : Type*} [Group G] (a : G) (h : a ^ n = 1) :
    (cyclicHom n a h).range = Subgroup.zpowers a := by
  rw [MonoidHom.range_eq_map, ← ofAdd_one_zpowers_top n, MonoidHom.map_zpowers]
  congr 1
  -- cyclicHom n a h (ofAdd 1) = a^1 = a
  rw [cyclicHom_apply_eq_zpow]
  -- need: a ^ ((toAdd (ofAdd (1 : ZMod n))).val : ℤ) = a
  -- when n > 1, (1 : ZMod n).val = 1. When n = 1, (1 : ZMod n).val = 0 and a = a^0 since a^1 = 1.
  have hn_pos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  by_cases hn1 : n = 1
  · -- n = 1: (1 : ZMod 1) = 0, so val = 0
    subst hn1
    show a ^ ((Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 1))).val : ℤ) = a
    have hval : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 1))).val = 0 := by
      simp [Subsingleton.elim (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 1))) 0]
    rw [hval]
    -- a = 1 since a^1 = 1
    simpa using h.symm
  · show a ^ ((Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod n))).val : ℤ) = a
    have h2 : 2 ≤ n := by omega
    have hval : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod n))).val = 1 := by
      change (1 : ZMod n).val = 1
      rw [ZMod.val_one_eq_one_mod, Nat.one_mod_eq_one.mpr (by omega)]
    rw [hval]; simp

/-- The range of canonicalAction r has cardinality p^r. -/
lemma canonicalAction_range_card
    (p q n m r : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hq_odd : q ≠ 2) (hn : 0 < n)
    (hr : r ≤ min m ((q - 1).factorization p)) :
    Nat.card (canonicalAction p q n m hpq hq_odd hn r hr).range = p ^ r := by
  haveI : NeZero (p ^ m) := ⟨pow_ne_zero m hp.out.ne_zero⟩
  set τ := canonicalAutElement p q n r hpq hq_odd hn (hr.trans (min_le_right m _))
  have h_pm : τ ^ p ^ m = 1 := by
    have h_ord : orderOf τ = p ^ r := canonicalAutElement_orderOf p q n r hpq hq_odd hn _
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [h_ord]
    exact pow_dvd_pow p (hr.trans (min_le_left m _))
  -- canonicalAction = cyclicHom applied to τ, so its range = zpowers τ.
  have hrange : (canonicalAction p q n m hpq hq_odd hn r hr).range = Subgroup.zpowers τ := by
    show (cyclicHom (p ^ m) τ h_pm).range = Subgroup.zpowers τ
    exact cyclicHom_range (p ^ m) τ h_pm
  rw [hrange, Nat.card_zpowers, canonicalAutElement_orderOf]

/-- Generic transport: for `CyclicGroup` types parameterized by ℕ with `NeZero`,
    along `p1 = p` and `q1 = q` (with `NeZero p1`, `NeZero q1` already in scope, and
    `NeZero p`, `NeZero q` derived from primality below). Both endpoints have `NeZero`
    so the transport via `Eq.rec` on each is well-typed.

    This is computable: `Eq.mpr` on a propositionally-equal type is a computational
    no-op at the byte-code level once both indices match. -/
def transportCpCqHom {p q p1 q1 : ℕ} [NeZero p] [NeZero q] [NeZero p1] [NeZero q1]
    (hp : p1 = p) (hq : q1 = q)
    (f : CyclicGroup p1 →* MulAut (CyclicGroup q1)) :
    CyclicGroup p →* MulAut (CyclicGroup q) := by
  subst hp
  subst hq
  exact f

/-- Range cardinality is invariant under `transportCpCqHom`. -/
lemma transportCpCqHom_range_card {p q p1 q1 : ℕ}
    [NeZero p] [NeZero q] [NeZero p1] [NeZero q1]
    (hp : p1 = p) (hq : q1 = q)
    (f : CyclicGroup p1 →* MulAut (CyclicGroup q1)) :
    Nat.card (transportCpCqHom hp hq f).range = Nat.card f.range := by
  subst hp; subst hq; rfl

/-- Transport the SDP across the parameter changes `p1 = p` and `q1 = q`. -/
def SemidirectProduct.transportCpCqIso {p q p1 q1 : ℕ}
    [NeZero p] [NeZero q] [NeZero p1] [NeZero q1]
    (hp : p1 = p) (hq : q1 = q)
    (f : CyclicGroup p1 →* MulAut (CyclicGroup q1)) :
    SemidirectProduct (CyclicGroup q1) (CyclicGroup p1) f ≃*
      SemidirectProduct (CyclicGroup q) (CyclicGroup p) (transportCpCqHom hp hq f) := by
  subst hp; subst hq; rfl

/-- Subgroup of N fixed pointwise by every automorphism in Im(f). -/
def fixedPointsSubgroup {N H : Type*} [Group N] [Group H] (f : H →* MulAut N) : Subgroup N where
  carrier := {n | ∀ h : H, f h n = n}
  one_mem' h := map_one (f h)
  mul_mem' {a b} ha hb h := by simp [map_mul (f h), ha h, hb h]
  inv_mem' {a} ha h := by simp [map_inv (f h) a, ha h]

/-- Center of N ⋊_f H for N, H abelian: (n, h) ∈ Z(G) iff h ∈ Ker(f) and Im(f) fixes n. -/
theorem mem_center_semidirectProduct_iff
    {N H : Type*} [CommGroup N] [CommGroup H]
    (f : H →* MulAut N)
    (g : SemidirectProduct N H f) :
    g ∈ Subgroup.center (SemidirectProduct N H f) ↔
    g.right ∈ f.ker ∧ ∀ h : H, f h g.left = g.left := by
  simp only [Subgroup.mem_center_iff, MonoidHom.mem_ker]
  constructor
  · intro hg
    -- Extract the left-component equation from commutativity x * g = g * x
    have hleft : ∀ x : SemidirectProduct N H f,
        x.left * f x.right g.left = g.left * f g.right x.left :=
      fun x => congr_arg SemidirectProduct.left (hg x)
    -- Setting x = inl n: f(g.right) = id, i.e. g.right ∈ Ker(f)
    have hker : f g.right = 1 := by
      ext n
      have h := hleft (SemidirectProduct.inl n)
      simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one] at h
      -- h : n * g.left = g.left * f g.right n
      -- N abelian + left cancellation → f g.right n = n
      exact (mul_left_cancel ((mul_comm g.left n).trans h)).symm
    -- Setting x = inr h: f(h)(g.left) = g.left for all h
    refine ⟨hker, fun h => ?_⟩
    have h' := hleft (SemidirectProduct.inr h)
    simp only [SemidirectProduct.left_inr, SemidirectProduct.right_inr, one_mul,
               hker, MulAut.one_apply, mul_one] at h'
    exact h'
  · intro ⟨hker, hfix⟩ x
    ext
    · simp only [SemidirectProduct.mul_left, hfix x.right, hker, MulAut.one_apply]
      exact mul_comm x.left g.left
    · simp only [SemidirectProduct.mul_right, mul_comm]

/-- The center of N ⋊_f H is isomorphic to Fix(Im(f)) × Ker(f). -/
noncomputable def center_semidirectProduct_iso
    {N H : Type*} [CommGroup N] [CommGroup H]
    (f : H →* MulAut N) :
    Subgroup.center (SemidirectProduct N H f) ≃* fixedPointsSubgroup f × f.ker := by
  refine MulEquiv.ofBijective
    (show Subgroup.center (SemidirectProduct N H f) →* fixedPointsSubgroup f × f.ker from
      { toFun := fun g =>
          let hg := (mem_center_semidirectProduct_iff f g.val).mp g.prop
          (⟨g.val.left, hg.2⟩, ⟨g.val.right, hg.1⟩)
        map_one' := by simp
        map_mul' := fun g₁ g₂ => by
          obtain ⟨hker₁, _⟩ := (mem_center_semidirectProduct_iff f g₁.val).mp g₁.prop
          have hfg₁ : f g₁.val.right = 1 := MonoidHom.mem_ker.mp hker₁
          ext
          · simp [Subgroup.coe_mul, SemidirectProduct.mul_left, hfg₁, MulAut.one_apply]
          · simp [Subgroup.coe_mul, SemidirectProduct.mul_right] })
    ⟨fun a b h => ?_, fun ⟨⟨n, hn⟩, ⟨k, hk⟩⟩ => ?_⟩
  · -- Injectivity
    have h1 : a.val.left = b.val.left := congr_arg (fun p => (Prod.fst p).val) h
    have h2 : a.val.right = b.val.right := congr_arg (fun p => (Prod.snd p).val) h
    exact Subtype.val_injective (SemidirectProduct.ext h1 h2)
  · -- Surjectivity
    exact ⟨⟨⟨n, k⟩, (mem_center_semidirectProduct_iff f ⟨n, k⟩).mpr ⟨hk, hn⟩⟩, by simp⟩

/-- When f is trivial, Fix = N and Ker = H, so Z(N ⋊_f H) has order |N| * |H|. -/
theorem center_card_of_trivial_action
    {N H : Type*} [CommGroup N] [CommGroup H]
    (f : H →* MulAut N) (hf : f = 1) :
    Nat.card (Subgroup.center (SemidirectProduct N H f)) = Nat.card N * Nat.card H := by
  subst hf
  have hfix : fixedPointsSubgroup (1 : H →* MulAut N) = ⊤ := by
    ext n; simp [fixedPointsSubgroup]
  have hker : (1 : H →* MulAut N).ker = ⊤ := by
    ext h; simp
  calc Nat.card (Subgroup.center (SemidirectProduct N H 1))
      = Nat.card (fixedPointsSubgroup (1 : H →* MulAut N) × (1 : H →* MulAut N).ker) :=
          Nat.card_congr (center_semidirectProduct_iso 1).toEquiv
    _ = Nat.card (fixedPointsSubgroup (1 : H →* MulAut N)) *
        Nat.card (1 : H →* MulAut N).ker := Nat.card_prod _ _
    _ = Nat.card (⊤ : Subgroup N) * Nat.card (⊤ : Subgroup H) := by rw [hfix, hker]
    _ = Nat.card N * Nat.card H := by rw [Subgroup.card_top, Subgroup.card_top]

/-- For r = 0 (trivial action), |Z(C_{q^n} ⋊ C_{p^m})| = q^n * p^m. -/
theorem center_card_of_r_zero
    (p q n m : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hq_odd : q ≠ 2) (hn : 0 < n) :
    Nat.card (Subgroup.center (SemidirectProduct (CyclicGroup (q ^ n)) (CyclicGroup (p ^ m))
      (canonicalAction p q n m hpq hq_odd hn 0 (Nat.zero_le _)))) = q ^ n * p ^ m := by
  have h_range : Nat.card (canonicalAction p q n m hpq hq_odd hn 0 (Nat.zero_le _)).range = 1 := by
    simpa using canonicalAction_range_card p q n m 0 hpq hq_odd hn (Nat.zero_le _)
  calc Nat.card (Subgroup.center (SemidirectProduct (CyclicGroup (q ^ n)) (CyclicGroup (p ^ m))
          (canonicalAction p q n m hpq hq_odd hn 0 (Nat.zero_le _))))
      = Nat.card (CyclicGroup (q ^ n)) * Nat.card (CyclicGroup (p ^ m)) :=
          center_card_of_trivial_action _ (eq_one_of_range_card_one h_range)
    _ = q ^ n * p ^ m := by rw [card_cyclicGroup, card_cyclicGroup]

/-- For r > 0 (non-trivial action), |Z(C_{q^n} ⋊ C_{p^m})| = p^(m-r). -/
theorem center_card_of_r_pos
    (p q n m r : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hq_odd : q ≠ 2) (hn : 0 < n) (hr : 0 < r)
    (hle : r ≤ min m ((q - 1).factorization p)) :
    Nat.card (Subgroup.center (SemidirectProduct (CyclicGroup (q ^ n)) (CyclicGroup (p ^ m))
      (canonicalAction p q n m hpq hq_odd hn r hle))) = p ^ (m - r) := by
  set f := canonicalAction p q n m hpq hq_odd hn r hle
  have hrm : r ≤ m := hle.trans (min_le_left _ _)
  -- |Z(G)| = |Fix(Im(f))| × |Ker(f)|
  have h_center : Nat.card (Subgroup.center (SemidirectProduct (CyclicGroup (q ^ n))
        (CyclicGroup (p ^ m)) f)) =
      Nat.card (fixedPointsSubgroup f) * Nat.card f.ker :=
    (Nat.card_congr (center_semidirectProduct_iso f).toEquiv).trans (Nat.card_prod _ _)
  -- Fix(Im(f)) = ⊥: only 1 is fixed by the non-trivial canonical action
  have h_fix : fixedPointsSubgroup f = ⊥ := by
    -- Give CyclicGroup(p^m) a MulDistribMulAction on CyclicGroup(q^n) via f
    letI : MulDistribMulAction (CyclicGroup (p ^ m)) (CyclicGroup (q ^ n)) :=
      MulDistribMulAction.compHom _ f
    -- Under this action, k • y = f k y definitionally
    have hsmul : ∀ (k : CyclicGroup (p ^ m)) (y : CyclicGroup (q ^ n)), k • y = f k y :=
      fun _ _ => rfl
    ext x
    simp only [fixedPointsSubgroup, Subgroup.mem_mk, Set.mem_setOf_eq, Subgroup.mem_bot]
    constructor
    · intro hx
      -- hx : ∀ h, f h x = x, equivalently k • x = x for all k
      have hfixed : ∀ k : CyclicGroup (p ^ m), k • x = x :=
        fun k => (hsmul k x).trans (hx k)
      -- Coprimality: gcd(q^n, p^m) = 1 since p ≠ q
      have hcop_pq : Nat.Coprime p q := hp.out.coprime_of_ne hq.out hpq
      have hcop : (Nat.card (CyclicGroup (q ^ n))).Coprime (Nat.card (CyclicGroup (p ^ m))) := by
        rw [card_cyclicGroup, card_cyclicGroup]
        exact ((hcop_pq.pow_left m).pow_right n).symm
      -- CyclicGroup(q^n) is a q-group
      have hqgrp : IsPGroup q (CyclicGroup (q ^ n)) :=
        IsPGroup.of_card (by rw [card_cyclicGroup])
      -- Case split: trivial action or surjective commutator map
      rcases IsPGroup.smul_mul_inv_trivial_or_surjective hqgrp hcop with htrivial | hsurj
      · -- Trivial action: f = 1, so Im(f) = {1}, |Im(f)| = 1 = p^r — but r > 0
        exfalso
        have hf_one : f = 1 := MonoidHom.ext fun k => MulEquiv.ext fun y => by
          show (f k) y = y
          have : k • y = y := mul_inv_eq_one.mp (htrivial y k)
          rw [← hsmul k y]; exact this
        linarith [canonicalAction_range_card p q n m r hpq hq_odd hn hle,
                  show Nat.card f.range = 1 by simp [hf_one],
                  Nat.one_lt_pow hr.ne' hp.out.one_lt]
      · -- Surjective: for x ∈ Fix, write x = k₀ • q₀ * q₀⁻¹; induction gives x^(p^m) = 1
        obtain ⟨k₀, q₀, hq_eq⟩ := hsurj x
        -- Key: k₀ • (k₀ • q₀) = x * (k₀ • q₀)
        have step : k₀ • (k₀ • q₀) = x * (k₀ • q₀) := by
          have h3 : k₀ • (k₀ • q₀) * (k₀ • q₀)⁻¹ = x := by
            have aux := congr_arg (k₀ • ·) hq_eq
            simp only [smul_mul', smul_inv'] at aux
            exact aux.trans (hfixed k₀)
          calc k₀ • (k₀ • q₀)
              = k₀ • (k₀ • q₀) * (k₀ • q₀)⁻¹ * (k₀ • q₀) := (inv_mul_cancel_right _ _).symm
            _ = x * (k₀ • q₀) := by rw [h3]
        -- By induction: k₀^n • (k₀ • q₀) = x^n * (k₀ • q₀)
        have ind : ∀ n : ℕ, k₀ ^ n • (k₀ • q₀) = x ^ n * (k₀ • q₀) := by
          intro n; induction n with
          | zero => simp
          | succ n ih =>
            rw [pow_succ, mul_smul, show k₀ • (k₀ • q₀) = x * (k₀ • q₀) from step,
                smul_mul', hfixed (k₀ ^ n), ih]; group
        -- k₀^(p^m) = 1 in CyclicGroup(p^m), so x^(p^m) = 1
        have hkpm : k₀ ^ p ^ m = 1 := by
          have h : k₀ ^ Nat.card (CyclicGroup (p ^ m)) = 1 := pow_card_eq_one'
          rwa [card_cyclicGroup] at h
        -- hind : k₀ • q₀ = x^(p^m) * (k₀ • q₀), so x^(p^m) = 1
        have hind : k₀ • q₀ = x ^ p ^ m * (k₀ • q₀) := by
          have h := ind (p ^ m)
          have h_lhs : k₀ ^ p ^ m • (k₀ • q₀) = k₀ • q₀ := by rw [hkpm]; exact one_smul _ _
          rw [h_lhs] at h; exact h
        have hxpm : x ^ p ^ m = 1 :=
          mul_right_cancel (hind.symm.trans (one_mul _).symm)
        -- orderOf x | p^m and | q^n; gcd = 1 forces x = 1
        have h1 : orderOf x ∣ p ^ m := orderOf_dvd_of_pow_eq_one hxpm
        have h2 : orderOf x ∣ q ^ n := by
          have := orderOf_dvd_natCard (G := CyclicGroup (q ^ n)) x
          rwa [card_cyclicGroup] at this
        have h3 : orderOf x ∣ 1 := by
          have := Nat.dvd_gcd h1 h2
          rwa [Nat.Coprime.gcd_eq_one ((hcop_pq.pow_left m).pow_right n)] at this
        exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
    · aesop
  -- |Ker(f)| = p^(m-r) by first isomorphism: |C_{p^m}| = |Ker(f)| × |Im(f)|
  have h_ker : Nat.card f.ker = p ^ (m - r) := by
    have h_lagrange : Nat.card f.ker * f.ker.index = Nat.card (CyclicGroup (p ^ m)) :=
      Subgroup.card_mul_index (H := f.ker)
    have h_index : f.ker.index = p ^ r := by
      rw [Subgroup.index_ker, canonicalAction_range_card p q n m r hpq hq_odd hn hle]
    rw [h_index, card_cyclicGroup] at h_lagrange
    have h_split : p ^ r * p ^ (m - r) = p ^ m := by
      rw [← pow_add, Nat.add_sub_cancel' hrm]
    nlinarith [pow_pos hp.out.pos r, pow_pos hp.out.pos (m - r)]
  rw [h_center, show Nat.card (fixedPointsSubgroup f) = 1 from by rw [h_fix]; exact Subgroup.card_bot,
    one_mul, h_ker]

/-- Semidirect products C_{q^n} ⋊ C_{p^m} (q odd prime, p ≠ q) are classified up to
    isomorphism by r ∈ {0, …, min(m, d)} where d = v_p(q - 1), giving min(m, d) + 1
    classes. Every action f belongs to exactly one class, represented by canonicalAction r. -/
theorem classify_Cqn_rtimes_Cpm
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hq_odd : q ≠ 2)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (f : CyclicGroup (p ^ m) →* MulAut (CyclicGroup (q ^ n))) :
    ∃! r : Fin (min m ((q - 1).factorization p) + 1),
      Nonempty (SemidirectProduct (CyclicGroup (q ^ n)) (CyclicGroup (p ^ m)) f ≃*
               SemidirectProduct (CyclicGroup (q ^ n)) (CyclicGroup (p ^ m))
                 (canonicalAction p q n m hpq hq_odd hn ↑r (Nat.lt_succ_iff.mp r.isLt))) := by
  -- |f.range| = p^r for some r ≤ m, since |f.range| ∣ |C_{p^m}| = p^m
  have h_range_dvd_pm : Nat.card ↥f.range ∣ p ^ m := by
    have := Subgroup.card_range_dvd f; rwa [card_cyclicGroup] at this
  obtain ⟨r, hr_le_m, h_range_card⟩ := (Nat.dvd_prime_pow hp.out).mp h_range_dvd_pm
  -- r ≤ v_p(q-1): p^r | |f.range| | |Aut| = q^(n-1)*(q-1) and gcd(p^r, q^(n-1))=1
  have hr_le_vp : r ≤ (q - 1).factorization p :=
    (hp.out.pow_dvd_iff_le_factorization (Nat.sub_pos_of_lt hq.out.one_lt).ne').mp (by
      -- p^r | (q-1): from p^r | |Aut| = q^(n-1)*(q-1) and gcd(p^r, q^(n-1))=1
      have h_aut_card : Nat.card (MulAut (CyclicGroup (q ^ n))) = q ^ (n - 1) * (q - 1) := by
        have heq := Nat.card_congr (IsCyclic.mulAutMulEquiv (CyclicGroup (q ^ n))).toEquiv
        rw [card_cyclicGroup] at heq
        rw [heq, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
        exact Nat.totient_prime_pow hq.out hn
      have h_pr_dvd : p ^ r ∣ q ^ (n - 1) * (q - 1) := by
        have h1 : Nat.card ↥f.range ∣ Nat.card (MulAut (CyclicGroup (q ^ n))) := by
          rw [← Subgroup.index_mul_card f.range]
          exact dvd_mul_left _ _
        rwa [h_range_card, h_aut_card] at h1
      have h_cop : Nat.Coprime (p ^ r) (q ^ (n - 1)) :=
        ((hp.out.coprime_of_ne hq.out hpq).pow_left r).pow_right (n - 1)
      exact h_cop.dvd_mul_left.mp h_pr_dvd)
  have hr : r ≤ min m ((q - 1).factorization p) := Nat.le_min.mpr ⟨hr_le_m, hr_le_vp⟩
  refine ⟨⟨r, Nat.lt_succ_of_le hr⟩, ?_, ?_⟩
  · -- f ≅ canonicalAction r: both ranges are the unique order-p^r subgroup of Aut(C_{q^n})
    apply semidirectProduct_iso_if_range_eq hp (card_cyclicGroup _)
    have h_aut_iso : MulAut (CyclicGroup (q ^ n)) ≃* (ZMod (q ^ n))ˣ := by
      have h := IsCyclic.mulAutMulEquiv (CyclicGroup (q ^ n))
      rwa [card_cyclicGroup] at h
    haveI : Finite (MulAut (CyclicGroup (q ^ n))) :=
      Finite.of_equiv _ h_aut_iso.toEquiv.symm
    haveI : IsCyclic (MulAut (CyclicGroup (q ^ n))) :=
      (MulEquiv.isCyclic h_aut_iso).mpr (ZMod.isCyclic_units_of_prime_pow q hq.out hq_odd n)
    exact cyclic_subgroup_of_cyclic_group_is_unique
      Nat.card_pos rfl f.range _ h_range_card
      (canonicalAction_range_card p q n m r hpq hq_odd hn hr)
  · -- r is uniquely determined by the isomorphism class
    intro ⟨r', hr'_lt⟩ hr'_iso; simp only [Fin.mk.injEq]
    have hr'_le : r' ≤ min m ((q - 1).factorization p) := Nat.lt_succ_iff.mp hr'_lt
    -- Re-derive f ≅ canonicalAction r (same construction as the existence branch)
    have hiso_r : Nonempty (SemidirectProduct (CyclicGroup (q ^ n)) (CyclicGroup (p ^ m)) f ≃*
        SemidirectProduct (CyclicGroup (q ^ n)) (CyclicGroup (p ^ m))
          (canonicalAction p q n m hpq hq_odd hn r hr)) := by
      apply semidirectProduct_iso_if_range_eq hp (card_cyclicGroup _)
      have h_aut_iso : MulAut (CyclicGroup (q ^ n)) ≃* (ZMod (q ^ n))ˣ := by
        have h := IsCyclic.mulAutMulEquiv (CyclicGroup (q ^ n)); rwa [card_cyclicGroup] at h
      haveI : Finite (MulAut (CyclicGroup (q ^ n))) := Finite.of_equiv _ h_aut_iso.toEquiv.symm
      haveI : IsCyclic (MulAut (CyclicGroup (q ^ n))) :=
        (MulEquiv.isCyclic h_aut_iso).mpr (ZMod.isCyclic_units_of_prime_pow q hq.out hq_odd n)
      exact cyclic_subgroup_of_cyclic_group_is_unique Nat.card_pos rfl f.range _
        h_range_card (canonicalAction_range_card p q n m r hpq hq_odd hn hr)
    obtain ⟨φ_r⟩ := hiso_r
    obtain ⟨φ_r'⟩ := hr'_iso
    -- canonicalAction r ≅ canonicalAction r'
    have hiso : SemidirectProduct (CyclicGroup (q ^ n)) (CyclicGroup (p ^ m))
          (canonicalAction p q n m hpq hq_odd hn r hr) ≃*
        SemidirectProduct (CyclicGroup (q ^ n)) (CyclicGroup (p ^ m))
          (canonicalAction p q n m hpq hq_odd hn r' hr'_le) :=
      φ_r.symm.trans φ_r'
    -- Isomorphic groups have isomorphic centers, hence equal center cardinalities
    have h_center_eq :
        Nat.card (Subgroup.center (SemidirectProduct (CyclicGroup (q ^ n)) (CyclicGroup (p ^ m))
          (canonicalAction p q n m hpq hq_odd hn r hr))) =
        Nat.card (Subgroup.center (SemidirectProduct (CyclicGroup (q ^ n)) (CyclicGroup (p ^ m))
          (canonicalAction p q n m hpq hq_odd hn r' hr'_le))) :=
      Nat.card_congr (Subgroup.centerCongr hiso).toEquiv
    -- coprimality of q^n and p^k, needed for the r=0 contradiction cases
    have hcop_pq : Nat.Coprime p q := hp.out.coprime_of_ne hq.out hpq
    have hqn_gt_one : 1 < q ^ n := Nat.one_lt_pow hn.ne' hq.out.one_lt
    -- Distinguish r from r' by center cardinality
    rcases Nat.eq_zero_or_pos r with rfl | hr_pos
    · rcases Nat.eq_zero_or_pos r' with rfl | hr'_pos
      · rfl
      · exfalso
        rw [center_card_of_r_zero p q n m hpq hq_odd hn,
            center_card_of_r_pos p q n m r' hpq hq_odd hn hr'_pos hr'_le] at h_center_eq
        -- q^n * p^m = p^(m-r') is impossible: q^n > 1 but gcd(q^n, p^(m-r')) = 1
        have hcop : Nat.Coprime (q ^ n) (p ^ (m - r')) :=
          (hcop_pq.symm.pow_left n).pow_right (m - r')
        have h_not_dvd : ¬ (q ^ n ∣ p ^ (m - r')) := fun hdvd =>
          absurd (Nat.le_of_dvd Nat.one_pos (hcop ▸ Nat.dvd_gcd (dvd_refl _) hdvd))
            (by linarith)
        exact h_not_dvd (h_center_eq ▸ dvd_mul_right (q ^ n) (p ^ m))
    · rcases Nat.eq_zero_or_pos r' with rfl | hr'_pos
      · exfalso
        rw [center_card_of_r_pos p q n m r hpq hq_odd hn hr_pos hr,
            center_card_of_r_zero p q n m hpq hq_odd hn] at h_center_eq
        have hcop : Nat.Coprime (q ^ n) (p ^ (m - r)) :=
          (hcop_pq.symm.pow_left n).pow_right (m - r)
        have h_not_dvd : ¬ (q ^ n ∣ p ^ (m - r)) := fun hdvd =>
          absurd (Nat.le_of_dvd Nat.one_pos (hcop ▸ Nat.dvd_gcd (dvd_refl _) hdvd))
            (by linarith)
        exact h_not_dvd (h_center_eq.symm ▸ dvd_mul_right (q ^ n) (p ^ m))
      · -- Both r, r' > 0: p^(m-r) = p^(m-r') → m-r = m-r' → r = r'
        rw [center_card_of_r_pos p q n m r hpq hq_odd hn hr_pos hr,
            center_card_of_r_pos p q n m r' hpq hq_odd hn hr'_pos hr'_le] at h_center_eq
        have h_exp : m - r = m - r' := Nat.pow_right_injective hp.out.two_le h_center_eq
        have hr_le_m := hr.trans (min_le_left m _)
        have hr'_le_m := hr'_le.trans (min_le_left m _)
        omega

/-- Convenient variant of `classify_Cqn_rtimes_Cpm`: given an explicit `r` and a
    proof that `|f.range| = p^r`, build the iso to the canonical action. -/
theorem classify_Cqn_rtimes_Cpm_exists
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

/-- The canonical action on abstract cyclic groups N, K: conjugates `canonicalAction p q n m r`
    through the unique isos N ≃* CyclicGroup (q^n) and K ≃* CyclicGroup (p^m).
    This lets `classify_sdp` output an iso back to `N ⋊ K` rather than to the concrete
    CyclicGroup types, eliminating transport bridges at call sites.

    Note: this remains `noncomputable` because `mulEquivOfCyclicCardEq` is noncomputable.
    The downstream wrappers (`canonicalCpOnCqAction`, etc.) use `canonicalAction` directly
    on the concrete `CyclicGroup` types, so they remain computable. -/
noncomputable def sdpCanonicalAction
    {N K : Type*} [Group N] [Group K] [IsCyclic N] [IsCyclic K]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hq_odd : q ≠ 2)
    (m n : ℕ) (hn : 0 < n)
    (hN : Nat.card N = q ^ n) (hK : Nat.card K = p ^ m)
    (r : ℕ) (hr : r ≤ min m ((q - 1).factorization p)) :
    K →* MulAut N :=
  letI : Finite N := Nat.finite_of_card_ne_zero (hN ▸ pow_ne_zero n hq.out.ne_zero)
  letI : Finite K := Nat.finite_of_card_ne_zero (hK ▸ pow_ne_zero m hp.out.ne_zero)
  let eN : N ≃* CyclicGroup (q ^ n) := mulEquivOfCyclicCardEq (by rw [hN, card_cyclicGroup])
  let eK : K ≃* CyclicGroup (p ^ m) := mulEquivOfCyclicCardEq (by rw [hK, card_cyclicGroup])
  (MulAut.congr eN.symm).toMonoidHom.comp
    ((canonicalAction p q n m hpq hq_odd hn r hr).comp eK.toMonoidHom)

/-- Abstract-group variant of `classify_Cqn_rtimes_Cpm`: classifies any semidirect product
    N ⋊ K of cyclic groups with |N| = q^n and |K| = p^m up to isomorphism, giving a unique
    r such that N ⋊ φ ≃* N ⋊ sdpCanonicalAction r. The output stays in N and K — no
    transport to CyclicGroup types at call sites. -/
theorem classify_sdp
    {N K : Type*} [Group N] [Group K] [IsCyclic N] [IsCyclic K]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hq_odd : q ≠ 2)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hN : Nat.card N = q ^ n) (hK : Nat.card K = p ^ m)
    (φ : K →* MulAut N) :
    ∃! r : Fin (min m ((q - 1).factorization p) + 1),
      Nonempty (SemidirectProduct N K φ ≃*
               SemidirectProduct N K
                 (sdpCanonicalAction hpq hq_odd m n hn hN hK ↑r (Nat.lt_succ_iff.mp r.isLt))) := by
  haveI : Finite N := Nat.finite_of_card_ne_zero (by
    rw [hN]; exact pow_ne_zero n hq.out.ne_zero)
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]; exact pow_ne_zero m hp.out.ne_zero)
  let eN : N ≃* CyclicGroup (q ^ n) := mulEquivOfCyclicCardEq (by rw [hN, card_cyclicGroup])
  let eK : K ≃* CyclicGroup (p ^ m) := mulEquivOfCyclicCardEq (by rw [hK, card_cyclicGroup])
  let f : CyclicGroup (p ^ m) →* MulAut (CyclicGroup (q ^ n)) :=
    (MulAut.congr eN).toMonoidHom.comp (φ.comp eK.symm.toMonoidHom)
  have h_bridge : SemidirectProduct N K φ ≃*
      SemidirectProduct (CyclicGroup (q ^ n)) (CyclicGroup (p ^ m)) f :=
    SemidirectProduct.congr' (φ₁ := φ) (fn := eN) (fg := eK)
  have h_bridge_back : ∀ r' : Fin (min m ((q - 1).factorization p) + 1),
      SemidirectProduct (CyclicGroup (q ^ n)) (CyclicGroup (p ^ m))
        (canonicalAction p q n m hpq hq_odd hn ↑r' (Nat.lt_succ_iff.mp r'.isLt)) ≃*
      SemidirectProduct N K
        (sdpCanonicalAction hpq hq_odd m n hn hN hK ↑r' (Nat.lt_succ_iff.mp r'.isLt)) :=
    fun r' => SemidirectProduct.congr'
      (φ₁ := canonicalAction p q n m hpq hq_odd hn ↑r' (Nat.lt_succ_iff.mp r'.isLt))
      (fn := eN.symm) (fg := eK.symm)
  obtain ⟨r, hr_iso, hr_uniq⟩ := classify_Cqn_rtimes_Cpm hpq hq_odd m n hm hn f
  refine ⟨r, ⟨h_bridge.trans (hr_iso.some.trans (h_bridge_back r))⟩, ?_⟩
  intro r' hr'_iso
  exact hr_uniq r' ⟨h_bridge.symm.trans (hr'_iso.some.trans (h_bridge_back r').symm)⟩

/-- Canonical iso: `CyclicGroup (q^n) ⋊ canonicalAction r ≃* N ⋊ sdpCanonicalAction r`
    for any cyclic N, K with the right cardinalities. The proof is a single `SemidirectProduct.congr'`
    call; definitional equality of the output action follows from proof irrelevance on
    the `mulEquivOfCyclicCardEq` arguments inside `sdpCanonicalAction`. -/
noncomputable def sdpCanonicalAction_iso_canonicalAction
    {N K : Type*} [Group N] [Group K] [IsCyclic N] [IsCyclic K]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hq_odd : q ≠ 2)
    (m n : ℕ) (hn : 0 < n)
    (hN : Nat.card N = q ^ n) (hK : Nat.card K = p ^ m)
    (r : ℕ) (hr : r ≤ min m ((q - 1).factorization p)) :
    SemidirectProduct (CyclicGroup (q ^ n)) (CyclicGroup (p ^ m))
        (canonicalAction p q n m hpq hq_odd hn r hr) ≃*
    SemidirectProduct N K
        (sdpCanonicalAction hpq hq_odd m n hn hN hK r hr) :=
  letI : Finite N := Nat.finite_of_card_ne_zero (hN ▸ pow_ne_zero n hq.out.ne_zero)
  letI : Finite K := Nat.finite_of_card_ne_zero (hK ▸ pow_ne_zero m hp.out.ne_zero)
  let eN : N ≃* CyclicGroup (q ^ n) := mulEquivOfCyclicCardEq (by rw [hN, card_cyclicGroup])
  let eK : K ≃* CyclicGroup (p ^ m) := mulEquivOfCyclicCardEq (by rw [hK, card_cyclicGroup])
  SemidirectProduct.congr' (φ₁ := canonicalAction p q n m hpq hq_odd hn r hr)
    (fn := eN.symm) (fg := eK.symm)

/-- The range of `sdpCanonicalAction r` has cardinality `p^r`, matching `canonicalAction r`. -/
lemma sdpCanonicalAction_range_card
    {N K : Type*} [Group N] [Group K] [IsCyclic N] [IsCyclic K]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hq_odd : q ≠ 2)
    (m n : ℕ) (hn : 0 < n)
    (hN : Nat.card N = q ^ n) (hK : Nat.card K = p ^ m)
    (r : ℕ) (hr : r ≤ min m ((q - 1).factorization p)) :
    Nat.card (sdpCanonicalAction hpq hq_odd m n hn hN hK r hr).range = p ^ r := by
  letI : Finite N := Nat.finite_of_card_ne_zero (hN ▸ pow_ne_zero n hq.out.ne_zero)
  letI : Finite K := Nat.finite_of_card_ne_zero (hK ▸ pow_ne_zero m hp.out.ne_zero)
  let eN : N ≃* CyclicGroup (q ^ n) := mulEquivOfCyclicCardEq (by rw [hN, card_cyclicGroup])
  let eK : K ≃* CyclicGroup (p ^ m) := mulEquivOfCyclicCardEq (by rw [hK, card_cyclicGroup])
  -- sdpCanonicalAction = (MulAut.congr eN.symm) ∘ (canonicalAction r) ∘ eK  [definitionally]
  have h1 : ((canonicalAction p q n m hpq hq_odd hn r hr).comp eK.toMonoidHom).range =
      (canonicalAction p q n m hpq hq_odd hn r hr).range := by
    ext x; simp only [MonoidHom.mem_range, MonoidHom.comp_apply]
    exact ⟨fun ⟨k, hk⟩ => ⟨eK k, hk⟩, fun ⟨y, hy⟩ => ⟨eK.symm y, by simp [hy]⟩⟩
  show Nat.card (((MulAut.congr eN.symm).toMonoidHom.comp
      ((canonicalAction p q n m hpq hq_odd hn r hr).comp eK.toMonoidHom))).range = p ^ r
  rw [MonoidHom.range_comp, h1]
  exact Nat.card_congr
    (Subgroup.equivMapOfInjective (canonicalAction p q n m hpq hq_odd hn r hr).range
      (MulAut.congr eN.symm).toMonoidHom (MulAut.congr eN.symm).injective).symm.toEquiv |>.trans
    (canonicalAction_range_card p q n m r hpq hq_odd hn hr)

/-- Transport `sdpCanonicalAction r` across isos `N₁ ≃* N₂` and `K₁ ≃* K₂`:
    `N₁ ⋊ sdpCanonicalAction r ≃* N₂ ⋊ sdpCanonicalAction r`. -/
noncomputable def sdpCanonicalAction_transport
    {N₁ N₂ K₁ K₂ : Type*} [Group N₁] [Group N₂] [Group K₁] [Group K₂]
    [IsCyclic N₁] [IsCyclic N₂] [IsCyclic K₁] [IsCyclic K₂]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hq_odd : q ≠ 2)
    (m n : ℕ) (hn : 0 < n)
    (hN₁ : Nat.card N₁ = q ^ n) (hK₁ : Nat.card K₁ = p ^ m)
    (hN₂ : Nat.card N₂ = q ^ n) (hK₂ : Nat.card K₂ = p ^ m)
    (r : ℕ) (hr : r ≤ min m ((q - 1).factorization p)) :
    SemidirectProduct N₁ K₁ (sdpCanonicalAction hpq hq_odd m n hn hN₁ hK₁ r hr) ≃*
    SemidirectProduct N₂ K₂ (sdpCanonicalAction hpq hq_odd m n hn hN₂ hK₂ r hr) :=
  (sdpCanonicalAction_iso_canonicalAction hpq hq_odd m n hn hN₁ hK₁ r hr).symm.trans
    (sdpCanonicalAction_iso_canonicalAction hpq hq_odd m n hn hN₂ hK₂ r hr)
