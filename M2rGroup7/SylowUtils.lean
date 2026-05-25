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

  -- Goal: f_2(x) = h f_1(beta(x)) h^-1 for every x in K, h in Aut(H), for some beta in Aut(K)
  -- Equivalent to: f_2(k) = f_1(beta(k)) for some beta in Aut(K)
  -- Now f_1 to Im(f_1) to f_2 is a isomorphism between K and K, so let beta be that and done
