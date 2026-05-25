import Mathlib.GroupTheory.Sylow
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finite.Card
import Mathlib.GroupTheory.SemidirectProduct
import «M2rGroup7».GroupTheoryLemmas
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Hom.Basic

/-- In a finite group of order p^a * q^b (p, q distinct primes),
    every Sylow p-subgroup has order p^a. -/
lemma sylow_card_eq {p q : ℕ} {a b : ℕ}
    [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q)
    {G : Type*} [Group G] [Finite G]
    (h : Nat.card G = p ^ a * q ^ b) (P : Sylow p G) :
    Nat.card ↥(P : Subgroup G) = p ^ a := by
  rw [Sylow.card_eq_multiplicity, h]
  have hcop : Nat.Coprime (p ^ a) (q ^ b) :=
    ((hp.out.coprime_iff_not_dvd.mpr fun hdvd =>
      absurd (hq.out.eq_one_or_self_of_dvd p hdvd)
        (by rintro (h1 | h2)
            · exact hp.out.one_lt.ne' h1
            · exact hpq h2)).pow_left a).pow_right b
  rw [Nat.factorization_mul_of_coprime hcop, Finsupp.add_apply,
      Nat.factorization_pow_self hp.out]
  have hqb : (q ^ b).factorization p = 0 := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, hq.out.factorization,
        Finsupp.single_apply, if_neg (Ne.symm hpq)]
    simp
  rw [hqb, add_zero]

/-- In a finite group of order p^a * q^b (p, q distinct primes),
    every Sylow p-subgroup has index q^b. -/
lemma sylow_index_eq {p q : ℕ} {a b : ℕ}
    [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q)
    {G : Type*} [Group G] [Finite G]
    (h : Nat.card G = p ^ a * q ^ b) (P : Sylow p G) :
    (P : Subgroup G).index = q ^ b := by
  have hcard := Subgroup.index_mul_card (P : Subgroup G)
  rw [sylow_card_eq hpq h P, h] at hcard
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.out.pos a) (hcard.trans (mul_comm _ _))

theorem semidirectProduct_iso_of_conjugate_action
    {H K : Type*} [Group H] [Group K]
    {f_1 f_2 : K →* MulAut H}
    (h : MulAut H) (β : MulAut K)
    (hconj : ∀ x : K, f_2 x = h * f_1 (β x) * h⁻¹) :
    Nonempty (SemidirectProduct H K f_1 ≃* SemidirectProduct H K f_2) :=
  ⟨SemidirectProduct.congr h β.symm fun g => by
    ext n
    simp [MulEquiv.trans_apply, hconj (β.symm g), MulAut.mul_apply,
          MulAut.inv_apply, MulEquiv.apply_symm_apply]⟩


noncomputable def powerMapAut {K : Type*} [CommGroup K] [Finite K]
      (c : ℕ) (hc : Nat.Coprime c (Nat.card K)) : MulAut K := by
    -- Power map is a group hom (commutativity gives mul_pow)
    let β : K →* K :=
      { toFun    := (· ^ c)
        map_one' := one_pow c
        map_mul' := fun x y => mul_pow x y c }
    -- β is injective: show trivial kernel
    have hβ_inj : Function.Injective β :=
      (injective_iff_map_eq_one β).mpr fun x hx => by
        -- hx : x ^ c = 1
        have h1 : orderOf x ∣ c          := orderOf_dvd_of_pow_eq_one hx
        have h2 : orderOf x ∣ Nat.card K := orderOf_dvd_natCard x
        -- orderOf x ∣ gcd(c, |K|) = 1
        have h3 : orderOf x ∣ 1 := by
          have := Nat.dvd_gcd h1 h2; rwa [hc] at this
        exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
    -- Injective endomorphism on a finite type is surjective, hence bijective
    exact MulEquiv.ofBijective β ⟨hβ_inj, Finite.injective_iff_surjective.mp hβ_inj⟩

/-- If K is cyclic p-group, two homomorphisms f g : K → Aut(H) define
    isomorphic semidirect products if they have the same image. -/
lemma semidirectProduct_iso_iff_range_eq
    {H K : Type*} {p m : ℕ} [Group H] [Group K] [IsCyclic K]
    (hp : Fact p.Prime) (h_p_group : Nat.card K = p ^ m)
    (f_1 f_2 : K →* MulAut H) (h_range_eq : f_1.range = f_2.range) :
    Nonempty (SemidirectProduct H K f_1 ≃* SemidirectProduct H K f_2) := by
  -- k is a generator of K
  obtain ⟨k, hk⟩ := IsCyclic.exists_generator (α := K)

  have : ∃ β : (MulAut K), ∀ x : K, f_2 x = f_1 (β x) := by
    have hrange_f1 : f_1.range = Subgroup.zpowers (f_1 k) := by
      rw [MonoidHom.range_eq_map, ← (Subgroup.eq_top_iff' _).mpr hk, MonoidHom.map_zpowers]
    have hf2k_mem : f_2 k ∈ Subgroup.zpowers (f_1 k) := by
      simp_all only [MonoidHom.mem_range, exists_apply_eq_apply]
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hf2k_mem
    -- |f_1.range| = p^j for some j, since it divides |K| = p^m
    obtain ⟨j, hj⟩ := (Nat.dvd_prime_pow hp.out).mp (h_p_group ▸ Subgroup.card_range_dvd f_1)
    rcases Nat.eq_zero_or_pos j with rfl | hj_pos
    · -- j = 0: f_1.range = {1}, both trivial, use β = 1
      simp only [pow_zero] at hj
      have h_bot : f_1.range = ⊥ := by rw [Subgroup.eq_bot_iff_card]; exact hj.2
      exact ⟨1, fun x => by
        have h1 : f_1 x = 1 :=
          Subgroup.mem_bot.mp (h_bot ▸ MonoidHom.mem_range.mpr ⟨x, rfl⟩)
        have h2 : f_2 x = 1 := by
          have hmem : f_2 x ∈ f_2.range := MonoidHom.mem_range.mpr ⟨x, rfl⟩
          rw [← h_range_eq, h_bot] at hmem
          exact Subgroup.mem_bot.mp hmem
        simp [h1, h2]⟩
    · -- j ≥ 1: gcd(n, p^j) = 1 → ¬ p ∣ n → gcd(n, p^m) = 1
      have hgcd : n.gcd ↑(Nat.card ↥f_1.range) = 1 := by
        have hrange_f2 : f_2.range = Subgroup.zpowers (f_2 k) := by
          rw [MonoidHom.range_eq_map, ← (Subgroup.eq_top_iff' _).mpr hk, MonoidHom.map_zpowers]
        have hf1k_mem : f_1 k ∈ Subgroup.zpowers (f_2 k) := by
          have h : f_1 k ∈ f_1.range := MonoidHom.mem_range.mpr ⟨k, rfl⟩
          rw [h_range_eq, hrange_f2] at h; exact h
        rw [← hn] at hf1k_mem
        have hcop := mem_zpowers_zpow_iff.mp hf1k_mem
        rwa [show orderOf (f_1 k) = Nat.card ↥f_1.range from by
          rw [hrange_f1, Nat.card_zpowers]] at hcop
      have h_not_p_dvd : ¬ ((p : ℤ) ∣ n) := by
        have hcop_j : Nat.Coprime n.natAbs (p ^ j) := by
          have h := hgcd; rw [hj.2] at h; exact_mod_cast h
        have hcop_p : Nat.Coprime n.natAbs p :=
          hcop_j.of_dvd_right (dvd_pow_self p hj_pos.ne')
        intro hdvd
        exact absurd (Int.natCast_dvd.mp hdvd) (hp.out.coprime_iff_not_dvd.mp hcop_p.symm)
      have h_n_gcd_K : n.gcd (Nat.card K) = 1 := by
        rw [h_p_group, Int.gcd_def]
        simp only [Int.natAbs_natCast]
        exact hp.out.coprime_pow_of_not_dvd fun h => h_not_p_dvd (Int.natCast_dvd.mpr h)
      -- K is finite (Nat.card = p^m > 0)
      haveI hfin : Finite K := Nat.finite_of_card_ne_zero (by
        rw [h_p_group]; exact (pow_pos hp.out.pos m).ne')
      -- β : K →* K given by x ↦ x^n
      -- map_mul' uses only zpow_add/zpow_mul (Group-level), avoiding CommGroup diamond
      let β_hom : K →* K :=
        { toFun    := (· ^ n)
          map_one' := one_zpow n
          map_mul' := fun x y => by
            obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hk x)
            obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hk y)
            rw [← zpow_add k a b, ← zpow_mul k (a + b) n, add_mul,
                zpow_add k (a * n) (b * n), zpow_mul k a n, zpow_mul k b n] }
      -- β_hom is injective: x^n = 1 → orderOf x | gcd(n, |K|) = 1 → x = 1
      have hβ_inj : Function.Injective β_hom :=
        (injective_iff_map_eq_one β_hom).mpr fun x hx => by
          have h1 : orderOf x ∣ n.natAbs :=
            Int.natCast_dvd.mp (orderOf_dvd_iff_zpow_eq_one.mpr hx)
          have h2 : orderOf x ∣ Nat.card K := orderOf_dvd_natCard x
          have hcop : Nat.Coprime n.natAbs (Nat.card K) := by
            have h := h_n_gcd_K
            rw [Int.gcd_def, Int.natAbs_natCast] at h
            exact h
          exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h1 h2))
      -- Injective endo of finite group → MulAut
      let β : MulAut K := MulEquiv.ofBijective β_hom
        ⟨hβ_inj, Finite.injective_iff_surjective.mp hβ_inj⟩
      -- f_2 and f_1 ∘ β agree on generator k (since f_1(k^n) = f_1(k)^n = f_2(k))
      refine ⟨β, fun x => ?_⟩
      have heq : f_2 = f_1.comp β.toMonoidHom :=
        monoidHom_eq_of_generator_eq hk (by
          show f_2 k = f_1 (β k)
          rw [show β k = k ^ n from rfl, map_zpow, hn])
      exact congr_fun (congr_arg DFunLike.coe heq) x

  obtain ⟨β, hβ⟩ := this

  exact semidirectProduct_iso_of_conjugate_action 1 β (by simp [hβ])

/-- For each r ≤ min(m, d) where d = v_p(q - 1), the canonical action
    φ_r : C_{p^m} →* Aut(C_{q^n}) with image of order p^r.
    Construction: Aut(C_{q^n}) is cyclic of order q^{n-1}(q-1); picking a generator α,
    the element α ^ (|Aut| / p^r) has order exactly p^r. -/
noncomputable def canonicalAction
    (p q n m : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hq_odd : q ≠ 2) (hn : 0 < n)
    (r : ℕ) (hr : r ≤ min m ((q - 1).factorization p)) :
    CyclicGroup (p ^ m) →* MulAut (CyclicGroup (q ^ n)) := by
  -- MulAut(C_{q^n}) ≃* (ZMod q^n)ˣ, which is cyclic since q is an odd prime
  have h_aut_iso : MulAut (CyclicGroup (q ^ n)) ≃* (ZMod (q ^ n))ˣ := by
    have h := IsCyclic.mulAutMulEquiv (CyclicGroup (q ^ n))
    rwa [card_cyclicGroup] at h
  haveI : IsCyclic (ZMod (q ^ n))ˣ :=
    ZMod.isCyclic_units_of_prime_pow q hq.out hq_odd n
  -- Transfer the generator from (ZMod q^n)ˣ to MulAut(C_{q^n})
  let α₀ := (IsCyclic.exists_generator (α := (ZMod (q ^ n))ˣ)).choose
  have hα₀ := (IsCyclic.exists_generator (α := (ZMod (q ^ n))ˣ)).choose_spec
  let α := h_aut_iso.symm α₀
  have hα : ∀ x, x ∈ Subgroup.zpowers α := fun x => by
    have hmem := hα₀ (h_aut_iso x)
    rw [Subgroup.mem_zpowers_iff] at hmem ⊢
    obtain ⟨z, hz⟩ := hmem
    exact ⟨z, by rw [show α = h_aut_iso.symm α₀ from rfl, ← map_zpow, hz, MulEquiv.symm_apply_apply]⟩
  -- orderOf α = |Aut(C_{q^n})|
  have h_orderOf_α : orderOf α = Nat.card (MulAut (CyclicGroup (q ^ n))) := by
    have hzpow_top : (Subgroup.zpowers α : Subgroup _) = ⊤ :=
      (Subgroup.eq_top_iff' _).mpr hα
    rw [← Nat.card_zpowers, hzpow_top, Nat.card_congr Subgroup.topEquiv.toEquiv]
  -- p^r divides |Aut(C_{q^n})|
  have h_pr_dvd : p ^ r ∣ Nat.card (MulAut (CyclicGroup (q ^ n))) := by
    have h_card : Nat.card (MulAut (CyclicGroup (q ^ n))) = (q ^ n).totient := by
      rw [Nat.card_congr h_aut_iso.toEquiv, Nat.card_eq_fintype_card,
          ZMod.card_units_eq_totient]
    have h_totient : (q ^ n).totient = q ^ (n - 1) * (q - 1) := by
      have := Nat.totient_prime_pow_succ hq.out (n - 1)
      rwa [Nat.sub_add_cancel hn] at this
    rw [h_card, h_totient]
    have h_dvd_q1 : p ^ r ∣ q - 1 :=
      (hp.out.pow_dvd_iff_le_factorization (Nat.sub_pos_of_lt hq.out.one_lt).ne').mpr
        (hr.trans (min_le_right m _))
    exact dvd_mul_of_dvd_right h_dvd_q1 _
  haveI : Finite (MulAut (CyclicGroup (q ^ n))) :=
    Finite.of_equiv _ h_aut_iso.toEquiv.symm
  set aut_card := Nat.card (MulAut (CyclicGroup (q ^ n)))
  set target := α ^ (aut_card / p ^ r)
  have h_aut_card_pos : 0 < aut_card := Nat.card_pos
  have h_pos : 0 < aut_card / p ^ r :=
    Nat.div_pos (Nat.le_of_dvd h_aut_card_pos h_pr_dvd) (pow_pos hp.out.pos r)
  -- α^(|Aut|/p^r) has order exactly p^r
  have h_orderOf_target : orderOf target = p ^ r := by
    have h_dvd_aut : aut_card / p ^ r ∣ orderOf α := by
      rw [h_orderOf_α]; exact Nat.div_dvd_of_dvd h_pr_dvd
    rw [show target = α ^ (aut_card / p ^ r) from rfl,
        orderOf_pow_of_dvd h_pos.ne' h_dvd_aut, h_orderOf_α]
    nth_rw 1 [show aut_card = aut_card / p ^ r * p ^ r from
      (Nat.div_mul_cancel h_pr_dvd).symm]
    exact Nat.mul_div_cancel_left (p ^ r) h_pos
  -- Generator k of C_{p^m} with orderOf k = p^m
  let k := (IsCyclic.exists_generator (α := CyclicGroup (p ^ m))).choose
  have hk := (IsCyclic.exists_generator (α := CyclicGroup (p ^ m))).choose_spec
  have h_orderOf_k : orderOf k = p ^ m := by
    have hzpow_top : (Subgroup.zpowers k : Subgroup _) = ⊤ :=
      (Subgroup.eq_top_iff' _).mpr hk
    rw [← Nat.card_zpowers, hzpow_top, Nat.card_congr Subgroup.topEquiv.toEquiv, card_cyclicGroup]
  -- orderOf target ∣ orderOf k since p^r ∣ p^m (r ≤ m)
  have h_dvd : orderOf target ∣ orderOf k := by
    rw [h_orderOf_target, h_orderOf_k]
    exact pow_dvd_pow p (hr.trans (min_le_left m _))
  exact monoidHomOfForallMemZpowers hk h_dvd

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
      sorry)
  have hr : r ≤ min m ((q - 1).factorization p) := Nat.le_min.mpr ⟨hr_le_m, hr_le_vp⟩
  refine ⟨⟨r, Nat.lt_succ_of_le hr⟩, ?_, ?_⟩
  · -- f ≅ canonicalAction r: their ranges both equal the unique order-p^r subgroup of Aut
    apply semidirectProduct_iso_iff_range_eq hp (card_cyclicGroup _)
    -- needs cyclic_subgroup_of_cyclic_group_is_unique (groupmate's sorry)
    sorry
  · -- r is uniquely determined by the isomorphism class
    intro ⟨r', _⟩ _; simp only [Fin.mk.injEq]
    sorry
