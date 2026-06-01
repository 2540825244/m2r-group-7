import Mathlib
import «M2rGroup7».Lemmas.GroupTheoryLemmas
import «M2rGroup7».Lemmas.ClassificationUtils
import «M2rGroup7».Lemmas.HomomorphismUtils

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

/-- The canonical element of Aut(C_{q^n}) of order p^r, for r ≤ v_p(q-1). -/
noncomputable def canonicalAutElement
    (p q n r : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hq_odd : q ≠ 2) (hn : 0 < n)
    (hr : r ≤ (q - 1).factorization p) :
    MulAut (CyclicGroup (q ^ n)) :=
  (canonicalAutElement_exists p q n r hpq hq_odd hn hr).choose

lemma canonicalAutElement_orderOf
    (p q n r : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hq_odd : q ≠ 2) (hn : 0 < n)
    (hr : r ≤ (q - 1).factorization p) :
    orderOf (canonicalAutElement p q n r hpq hq_odd hn hr) = p ^ r :=
  (canonicalAutElement_exists p q n r hpq hq_odd hn hr).choose_spec

/-- For each r ≤ min(m, d) where d = v_p(q-1), the canonical action
    φ_r : C_{p^m} →* Aut(C_{q^n}) with image of order p^r. -/
noncomputable def canonicalAction
    (p q n m : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hq_odd : q ≠ 2) (hn : 0 < n)
    (r : ℕ) (hr : r ≤ min m ((q - 1).factorization p)) :
    CyclicGroup (p ^ m) →* MulAut (CyclicGroup (q ^ n)) := by
  let k := (IsCyclic.exists_generator (α := CyclicGroup (p ^ m))).choose
  have hk := (IsCyclic.exists_generator (α := CyclicGroup (p ^ m))).choose_spec
  have h_orderOf_k : orderOf k = p ^ m := by
    have hzpow_top : (Subgroup.zpowers k : Subgroup _) = ⊤ :=
      (Subgroup.eq_top_iff' _).mpr hk
    rw [← Nat.card_zpowers, hzpow_top, Nat.card_congr Subgroup.topEquiv.toEquiv, card_cyclicGroup]
  have h_dvd : orderOf (canonicalAutElement p q n r hpq hq_odd hn (hr.trans (min_le_right m _))) ∣ orderOf k := by
    rw [canonicalAutElement_orderOf, h_orderOf_k]
    exact pow_dvd_pow p (hr.trans (min_le_left m _))
  exact monoidHomOfForallMemZpowers hk h_dvd

/-- The range of canonicalAction r has cardinality p^r. -/
lemma canonicalAction_range_card
    (p q n m r : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hq_odd : q ≠ 2) (hn : 0 < n)
    (hr : r ≤ min m ((q - 1).factorization p)) :
    Nat.card (canonicalAction p q n m hpq hq_odd hn r hr).range = p ^ r := by
  set k := (IsCyclic.exists_generator (α := CyclicGroup (p ^ m))).choose
  have hk : ∀ x, x ∈ Subgroup.zpowers k :=
    (IsCyclic.exists_generator (α := CyclicGroup (p ^ m))).choose_spec
  -- range of a hom from a cyclic group equals zpowers of the generator's image
  have hrange : (canonicalAction p q n m hpq hq_odd hn r hr).range =
      Subgroup.zpowers ((canonicalAction p q n m hpq hq_odd hn r hr) k) := by
    rw [MonoidHom.range_eq_map, ← (Subgroup.eq_top_iff' _).mpr hk, MonoidHom.map_zpowers]
  -- canonicalAction sends the generator k to canonicalAutElement
  have h_orderOf_k : orderOf k = p ^ m := by
    have hzpow_top : (Subgroup.zpowers k : Subgroup _) = ⊤ :=
      (Subgroup.eq_top_iff' _).mpr hk
    rw [← Nat.card_zpowers, hzpow_top, Nat.card_congr Subgroup.topEquiv.toEquiv, card_cyclicGroup]
  have h_dvd : orderOf (canonicalAutElement p q n r hpq hq_odd hn (hr.trans (min_le_right m _))) ∣ orderOf k := by
    rw [canonicalAutElement_orderOf, h_orderOf_k]; exact pow_dvd_pow p (hr.trans (min_le_left m _))
  have happ : (canonicalAction p q n m hpq hq_odd hn r hr) k =
      canonicalAutElement p q n r hpq hq_odd hn (hr.trans (min_le_right m _)) := by
    show (monoidHomOfForallMemZpowers hk h_dvd) k = _
    exact monoidHomOfForallMemZpowers_apply_gen hk h_dvd
  rw [hrange, happ, Nat.card_zpowers, canonicalAutElement_orderOf]

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

/-- Abstract-group variant of `classify_Cqn_rtimes_Cpm`: works for any cyclic groups
    N, K with the right cardinalities, avoiding transport to canonical CyclicGroup types. -/
theorem classify_sdp
    {N K : Type*} [Group N] [Group K] [IsCyclic N] [IsCyclic K]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hq_odd : q ≠ 2)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hN : Nat.card N = q ^ n) (hK : Nat.card K = p ^ m)
    (φ : K →* MulAut N) :
    ∃! r : Fin (min m ((q - 1).factorization p) + 1),
      Nonempty (SemidirectProduct N K φ ≃*
               SemidirectProduct (CyclicGroup (q ^ n)) (CyclicGroup (p ^ m))
                 (canonicalAction p q n m hpq hq_odd hn ↑r (Nat.lt_succ_iff.mp r.isLt))) := by
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
  obtain ⟨r, hr_iso, hr_uniq⟩ := classify_Cqn_rtimes_Cpm hpq hq_odd m n hm hn f
  refine ⟨r, ⟨h_bridge.trans hr_iso.some⟩, ?_⟩
  intro r' hr'_iso
  exact hr_uniq r' ⟨h_bridge.symm.trans hr'_iso.some⟩
