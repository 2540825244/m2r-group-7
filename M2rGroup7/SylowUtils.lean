import Mathlib
import «M2rGroup7».GroupTheoryLemmas

variable (G : Type*) [Group G]

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
      haveI hqn_ne : NeZero (q ^ n) := ⟨(Nat.pow_pos hq.out.pos).ne'⟩
      haveI hfin_aut : Finite (MulAut (CyclicGroup (q ^ n))) := by
        have h := (IsCyclic.mulAutMulEquiv (CyclicGroup (q ^ n))).toEquiv
        rw [card_cyclicGroup] at h
        exact Finite.of_equiv _ h.symm
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
        ((hp.out.coprime_iff_not_dvd.mpr (fun hdvd =>
          absurd (hq.out.eq_one_or_self_of_dvd p hdvd)
            (by rintro (h1 | h2)
                · exact hp.out.one_lt.ne' h1
                · exact hpq h2))).pow_left r).pow_right (n - 1)
      exact h_cop.dvd_mul_left.mp h_pr_dvd)
  have hr : r ≤ min m ((q - 1).factorization p) := Nat.le_min.mpr ⟨hr_le_m, hr_le_vp⟩
  refine ⟨⟨r, Nat.lt_succ_of_le hr⟩, ?_, ?_⟩
  · -- f ≅ canonicalAction r: their ranges both equal the unique order-p^r subgroup of Aut
    apply semidirectProduct_iso_iff_range_eq hp (card_cyclicGroup _)
    -- needs cyclic_subgroup_of_cyclic_group_is_unique (groupmate's sorry)
    sorry
  · -- r is uniquely determined by the isomorphism class
    intro ⟨r', _⟩ _; simp only [Fin.mk.injEq]
    sorry

lemma p2q_group_has_normal_sylow_subgroup {p : ℕ} {q : ℕ} [h_p_prime : Fact p.Prime] [h_q_prime : Fact q.Prime] (h_p_ne_q : p ≠ q) (h : Nat.card G = p^2 * q)
  : Nat.card (Sylow p G) = 1 ∨ Nat.card (Sylow q G) = 1 := by
  let n_p := Nat.card (Sylow p G)
  let n_q := Nat.card (Sylow q G)

  -- G is finite
  haveI : Finite G := by
    apply Nat.finite_of_card_ne_zero
    rw [h]
    have p_ne : p ≠ 0 := Nat.Prime.ne_zero h_p_prime.elim
    have q_ne : q ≠ 0 := Nat.Prime.ne_zero h_q_prime.elim
    simp; tauto

  let P : Sylow p G := default

  -- Order of Sylow p-group is p^2
  have h_p_p2 : Nat.card ↥(P : Subgroup G) = p ^ 2 :=
    sylow_card_eq h_p_ne_q (show Nat.card G = p ^ 2 * q ^ 1 by aesop) P

  -- Index of Sylow p-group is q
  have h_p_idx_q : (↑P : Subgroup G).index = q := by
    simpa using sylow_index_eq h_p_ne_q (show Nat.card G = p ^ 2 * q ^ 1 by aesop) P

  -- n_p divides q
  have h_n_p_div_q : n_p ∣ q := by
    have h_sylow_dvd_p_index := Sylow.card_dvd_index P
    rw [h_p_idx_q] at h_sylow_dvd_p_index
    exact h_sylow_dvd_p_index

  -- n_p is 1 (mod p)
  have h_n_p_one_mod_p : n_p ≡ 1 [MOD p] := by
    change Nat.card (Sylow p G) ≡ 1 [MOD p]
    exact card_sylow_modEq_one p G

  -- Claim 1: n_p = 1 or n_q = 1

  have n_p_or_n_q_one : n_p = 1 ∨ n_q = 1 := by
    rcases lt_trichotomy p q with h_lt | h_eq | h_gt
    · -- case h_lt : p < q

      -- Step 1: n_q can be either 1, p, p^2

      let Q : Sylow q G := default

      -- Order of Sylow q-group is q
      have h_q_q : Nat.card ↥(Q : Subgroup G) = q := by
        have := sylow_card_eq (Ne.symm h_p_ne_q)
          (show Nat.card G = q ^ 1 * p ^ 2 by rw [pow_one, h]; ring) Q
        simpa using this

      -- Index of Sylow q-group is p^2
      have h_q_idx_p2 : (↑Q : Subgroup G).index = p ^ 2 := by
        simpa using sylow_index_eq (Ne.symm h_p_ne_q)
          (show Nat.card G = q ^ 1 * p ^ 2 by rw [pow_one, h]; ring) Q

      -- n_q divides p^2
      have h_n_p_div_q : n_q ∣ p^2 := by
        have h_sylow_dvd_p_index := Sylow.card_dvd_index Q
        rw [h_q_idx_p2] at h_sylow_dvd_p_index
        exact h_sylow_dvd_p_index

      -- n_q is 1, p, or p^2
      have h_n_q_cases : n_q = 1 ∨ n_q = p ∨ n_q = p^2 := by
        obtain ⟨k, hk, hkn⟩ := (Nat.dvd_prime_pow h_p_prime.out).mp h_n_p_div_q
        interval_cases k
        · left;  simpa using hkn
        · right; left;  simpa using hkn
        · right; right; simpa using hkn


      -- Step 2: n_q ≠ p as then q | p−1 contradicting p < q

      -- n_q is 1 (mod q)
      have h_n_p_one_mod_p : n_q ≡ 1 [MOD q] := by
        change Nat.card (Sylow q G) ≡ 1 [MOD q]
        exact card_sylow_modEq_one q G

      -- n_q ≠ p
      have h_n_q_neq_p : n_q ≠ p := by
        intro n_q_eq_p
        rw [n_q_eq_p] at h_n_p_one_mod_p
        unfold Nat.ModEq at h_n_p_one_mod_p
        rw [Nat.mod_eq_of_lt h_lt, Nat.mod_eq_of_lt h_q_prime.out.one_lt] at h_n_p_one_mod_p
        linarith [h_p_prime.out.one_lt]

      -- Step 3: If n_q ≠ 1, then n_q = p^2
      rcases h_n_q_cases with h_nq1 | h_nqp | h_nqp2
      · -- n_q = 1, done
        right; exact h_nq1
      · -- n_q = p, impossible
        exact absurd h_nqp h_n_q_neq_p
      · -- n_q = p^2

        -- Step 4: p^2 Sylow q-subgroup are trivially intersecting, so contribute p²(q−1) elements of order q

        -- Step 5: Remaining p² elements form one Sylow p-subgroup, so n_p = 1

        -- =========================================================
        -- BEGIN PROOF OF STEPS 4 & 5 (counting argument, n_p = 1)
        -- =========================================================

        left
        haveI hFinG : Fintype G := Fintype.ofFinite G
        haveI hDecEq : DecidableEq G := Classical.decEq G

        -- Helper: build a Finset G from a Subgroup G
        let toFset : ∀ H : Subgroup G, Finset G := fun H =>
          letI : Fintype ↥H := Fintype.ofFinite _
          (H : Set G).toFinset

        have mem_toFset : ∀ (H : Subgroup G) (x : G), x ∈ toFset H ↔ x ∈ H := fun H x => by
          letI : Fintype ↥H := Fintype.ofFinite _
          change x ∈ (H : Set G).toFinset ↔ x ∈ H
          simp [Set.mem_toFinset, SetLike.mem_coe]

        have toFset_card : ∀ H : Subgroup G, (toFset H).card = Nat.card ↥H := fun H => by
          letI : Fintype ↥H := Fintype.ofFinite _
          aesop

        -- All Sylow q-subgroups have order q
        have h_sylow_q_card : ∀ Q' : Sylow q G, Nat.card ↥(Q' : Subgroup G) = q := fun Q' => by
          have := sylow_card_eq (Ne.symm h_p_ne_q)
            (show Nat.card G = q ^ 1 * p ^ 2 by rw [pow_one, h]; ring) Q'
          simpa using this

        -- Any Sylow p-subgroup has order p^2
        have h_p_p2_gen : ∀ P' : Sylow p G, Nat.card ↥(P' : Subgroup G) = p ^ 2 := fun P' =>
          sylow_card_eq h_p_ne_q (show Nat.card G = p ^ 2 * q ^ 1 by aesop) P'

        -- Distinct Sylow q-subgroups intersect trivially
        have h_Qdisj : ∀ Q₁ Q₂ : Sylow q G, Q₁ ≠ Q₂ → Disjoint (Q₁ : Subgroup G) Q₂ := by
          intro Q₁ Q₂ hne
          rw [disjoint_iff]
          have hdvd : Nat.card ↥((Q₁ : Subgroup G) ⊓ Q₂) ∣ q := by
            calc Nat.card ↥((Q₁ : Subgroup G) ⊓ Q₂)
                ∣ Nat.card ↥(Q₁ : Subgroup G) := Subgroup.card_dvd_of_le inf_le_left
              _ = q := h_sylow_q_card Q₁
          rcases h_q_prime.out.eq_one_or_self_of_dvd _ hdvd with h1 | hq
          · exact Subgroup.card_eq_one.mp h1
          · exfalso; apply hne; apply Sylow.ext
            have hce1 : Nat.card ↥((Q₁ : Subgroup G) ⊓ Q₂) = Nat.card ↥(Q₁ : Subgroup G) :=
              hq.trans (h_sylow_q_card Q₁).symm
            have hce2 : Nat.card ↥((Q₁ : Subgroup G) ⊓ Q₂) = Nat.card ↥(Q₂ : Subgroup G) :=
              hq.trans (h_sylow_q_card Q₂).symm
            -- subgroupOf preserves Nat.card (via injective subtype map)
            have h_sgOf_card : ∀ (H K : Subgroup G), H ≤ K →
                Nat.card ↥(H.subgroupOf K) = Nat.card ↥H := fun H K hle => by
              calc Nat.card ↥(H.subgroupOf K)
                  = Nat.card ↥((H.subgroupOf K).map K.subtype) :=
                      (Subgroup.card_map_of_injective Subtype.coe_injective).symm
                _ = Nat.card ↥H := by rw [Subgroup.map_subgroupOf_eq_of_le hle]
            -- map K.subtype ⊤ = K (the image of ⊤ under the inclusion is K itself)
            have map_top_subtype : ∀ K : Subgroup G,
                Subgroup.map K.subtype (⊤ : Subgroup ↥K) = K := fun K => by
              ext x; simp only [Subgroup.mem_map, Subgroup.mem_top, true_and]
              exact ⟨fun ⟨y, hy⟩ => hy ▸ y.prop, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
            have heq1 : (Q₁ : Subgroup G) ⊓ Q₂ = Q₁ := by
              haveI : Finite ↥((Q₁ ⊓ Q₂ : Subgroup G).subgroupOf Q₁) := inferInstance
              have htop := (Subgroup.card_eq_iff_eq_top _).mp
                ((h_sgOf_card _ Q₁ inf_le_left).trans hce1)
              have hmb := Subgroup.map_subgroupOf_eq_of_le
                (inf_le_left (a := (Q₁ : Subgroup G)) (b := Q₂))
              rw [htop] at hmb
              exact (map_top_subtype Q₁ ▸ hmb).symm
            have heq2 : (Q₁ : Subgroup G) ⊓ Q₂ = Q₂ := by
              haveI : Finite ↥((Q₁ ⊓ Q₂ : Subgroup G).subgroupOf Q₂) := inferInstance
              have htop := (Subgroup.card_eq_iff_eq_top _).mp
                ((h_sgOf_card _ Q₂ inf_le_right).trans hce2)
              have hmb := Subgroup.map_subgroupOf_eq_of_le
                (inf_le_right (a := (Q₁ : Subgroup G)) (b := Q₂))
              rw [htop] at hmb
              exact (map_top_subtype Q₂ ▸ hmb).symm
            exact heq1.symm.trans heq2

        -- A Sylow p-subgroup and a Sylow q-subgroup always intersect trivially (different primes)
        have h_PQdisj : ∀ (P' : Sylow p G) (Q' : Sylow q G), Disjoint (P' : Subgroup G) Q' :=
          fun P' Q' => IsPGroup.disjoint_of_ne p q h_p_ne_q _ _ P'.isPGroup' Q'.isPGroup'

        -- Non-identity elements of any Sylow p-subgroup are absent from every Sylow q-subgroup
        have h_P_avoid_Q : ∀ (P' : Sylow p G) x, x ∈ (P' : Subgroup G) → x ≠ 1 →
            ∀ Q' : Sylow q G, x ∉ (Q' : Subgroup G) := fun P' x hxP hx1 Q' hxQ =>
          hx1 (Subgroup.mem_bot.mp ((disjoint_iff.mp (h_PQdisj P' Q'))
            ▸ Subgroup.mem_inf.mpr ⟨hxP, hxQ⟩))

        -- U = union of all Sylow q-subgroups (as a Finset)
        let U : Finset G := Finset.univ.biUnion (fun Q' : Sylow q G => toFset Q')

        -- Non-identity parts of distinct Sylow q-subgroups are pairwise disjoint
        have h_ne_pdisj : Set.PairwiseDisjoint ↑(Finset.univ : Finset (Sylow q G))
            (fun Q' : Sylow q G => toFset Q' \ {(1 : G)}) := by
          intro Q₁ _ Q₂ _ hne
          simp only [Function.onFun]
          rw [Finset.disjoint_left]
          rintro x hx1 hx2
          simp only [Finset.mem_sdiff, mem_toFset, Finset.mem_singleton] at hx1 hx2
          exact hx1.2 (Subgroup.mem_bot.mp ((disjoint_iff.mp (h_Qdisj Q₁ Q₂ hne))
            ▸ Subgroup.mem_inf.mpr ⟨hx1.1, hx2.1⟩))

        -- The biUnion of non-identity parts has cardinality n_q * (q - 1)
        have h_ne_card : (Finset.univ.biUnion (fun Q' : Sylow q G =>
            toFset Q' \ {(1 : G)})).card = n_q * (q - 1) := by
          rw [Finset.card_biUnion h_ne_pdisj]
          have h_each : ∀ Q' : Sylow q G, (toFset Q' \ {(1 : G)}).card = q - 1 := fun Q' => by
            have hmem : (1 : G) ∈ toFset Q' := (mem_toFset _ _).mpr (Q' : Subgroup G).one_mem
            rw [Finset.card_sdiff, Finset.inter_comm, Finset.inter_singleton_of_mem hmem,
                Finset.card_singleton, toFset_card, h_sylow_q_card]
          simp only [h_each, Finset.sum_const, Finset.card_univ, smul_eq_mul,
                      ← Nat.card_eq_fintype_card]
          rfl

        -- U decomposes as {1} ∪ (non-identity parts)
        have hU_split : U = {(1 : G)} ∪ Finset.univ.biUnion (fun Q' : Sylow q G =>
            toFset Q' \ {(1 : G)}) := by
          ext x
          simp only [U, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union,
                      Finset.mem_singleton, Finset.mem_sdiff, mem_toFset]
          constructor
          · rintro ⟨Q', hxQ'⟩
            rcases eq_or_ne x 1 with rfl | hx1
            · left; rfl
            · right; exact ⟨Q', hxQ', hx1⟩
          · rintro (rfl | ⟨Q', hxQ', _⟩)
            · exact ⟨Q, (Q : Subgroup G).one_mem⟩
            · exact ⟨Q', hxQ'⟩

        have hU_split_disj : Disjoint {(1 : G)} (Finset.univ.biUnion (fun Q' : Sylow q G =>
            toFset Q' \ {(1 : G)})) := by
          simp only [Finset.disjoint_left, Finset.mem_singleton, Finset.mem_biUnion,
                      Finset.mem_univ, true_and, Finset.mem_sdiff, mem_toFset]
          rintro _ rfl ⟨Q', _, h1⟩; exact h1 rfl

        -- |U| = 1 + n_q * (q - 1)
        have hUcard : U.card = 1 + n_q * (q - 1) := by
          rw [hU_split, Finset.card_union_of_disjoint hU_split_disj, Finset.card_singleton,
              h_ne_card]

        -- |univ \ U| = p^2 - 1  (the "remaining" elements)
        have hTcard : (Finset.univ \ U).card = p ^ 2 - 1 := by
          have hsum : (Finset.univ \ U).card + U.card = Fintype.card G := by
            have h1 := @Finset.card_sdiff_add_card_inter G _ Finset.univ U
            simp only [Finset.univ_inter] at h1
            linarith [Finset.card_univ (α := G)]
          have hU' : U.card = 1 + p ^ 2 * (q - 1) := h_nqp2 ▸ hUcard
          rw [← Nat.card_eq_fintype_card, h, hU'] at hsum
          have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ h_p_prime.out.pos
          rcases q with _ | k
          · exact absurd h_q_prime.out.pos (by omega)
          · simp only [Nat.succ_sub_one] at hsum
            have hring : p ^ 2 * (k + 1) = p ^ 2 * k + p ^ 2 := by ring
            omega

        -- Non-identity elements of any Sylow p-subgroup lie outside U
        have hPin_T : ∀ P' : Sylow p G, toFset P' \ {(1 : G)} ⊆ Finset.univ \ U := fun P' x => by
          simp only [Finset.mem_sdiff, mem_toFset, Finset.mem_singleton, Finset.mem_univ,
                      true_and, U, Finset.mem_biUnion]
          rintro ⟨hxP, hx1⟩ ⟨Q', hxQ⟩
          exact h_P_avoid_Q P' x hxP hx1 Q' hxQ

        -- Each Sylow p-subgroup contributes exactly p^2 - 1 non-identity elements
        have hPcard : ∀ P' : Sylow p G, (toFset P' \ {(1 : G)}).card = p ^ 2 - 1 := fun P' => by
          have hmem : (1 : G) ∈ toFset P' := (mem_toFset _ _).mpr (P' : Subgroup G).one_mem
          rw [Finset.card_sdiff, Finset.inter_comm, Finset.inter_singleton_of_mem hmem,
              Finset.card_singleton, toFset_card, h_p_p2_gen]

        -- The non-identity part of every Sylow p-subgroup equals univ \ U exactly
        have hPeqT : ∀ P' : Sylow p G, toFset P' \ {(1 : G)} = Finset.univ \ U :=
          fun P' => (Finset.subset_iff_eq_of_card_le
            (le_of_eq (hTcard.trans (hPcard P').symm))).mp (hPin_T P')

        -- Hence all Sylow p-subgroups coincide → Subsingleton → n_p = 1
        haveI hSubsing : Subsingleton (Sylow p G) := by
          refine ⟨fun P₁ P₂ => ?_⟩
          apply Sylow.ext; apply Subgroup.ext; intro x
          rcases eq_or_ne x 1 with rfl | hx1
          · simp
          · have h_neq : toFset P₁ \ {(1 : G)} = toFset P₂ \ {(1 : G)} :=
              (hPeqT P₁).trans (hPeqT P₂).symm
            have key := Finset.ext_iff.mp h_neq x
            simp only [Finset.mem_sdiff, mem_toFset, Finset.mem_singleton, hx1,
                        not_false_eq_true, and_true] at key
            exact key

        exact Nat.card_eq_one_iff_unique.mpr ⟨hSubsing, ⟨P⟩⟩

        -- =========================================================
        -- END PROOF OF STEPS 4 & 5
        -- =========================================================
    · -- case h_eq : p = q  (impossible since p ≠ q)
      trivial
    · -- case h_gt : q < p

      -- Step 1: Only divisor of q that's ≡ 1 (mod p) is 1. So n_p = 1.
      left
      rcases h_q_prime.out.eq_one_or_self_of_dvd n_p h_n_p_div_q with h | h
      · exact h
      · exfalso
        have hmod := h_n_p_one_mod_p
        rw [h] at hmod
        unfold Nat.ModEq at hmod
        rw [Nat.mod_eq_of_lt h_gt, Nat.mod_eq_of_lt h_p_prime.out.one_lt] at hmod
        linarith [h_q_prime.out.one_lt]
  tauto
