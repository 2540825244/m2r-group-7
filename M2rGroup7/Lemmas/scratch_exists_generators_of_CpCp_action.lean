import Mathlib
import «M2rGroup7».Lemmas.GroupTheoryLemmas
import «M2rGroup7».Lemmas.HomomorphismUtils

/-- When the homomorphism φ is trivial, N ⋊[φ] K ≃* N × K via the identity map on pairs. -/
noncomputable def SemidirectProduct.mulEquivOfTrivialAction
    {N K : Type*} [Group N] [Group K] {φ : K →* MulAut N} (hφ : φ = 1) :
    SemidirectProduct N K φ ≃* N × K where
  toFun x := (x.left, x.right)
  invFun p := ⟨p.1, p.2⟩
  left_inv x := SemidirectProduct.ext rfl rfl
  right_inv _ := rfl
  map_mul' x y := by
    have hact : ∀ (k : K) (n : N), φ k n = n := fun k n => by
      have hk : φ k = 1 := DFunLike.congr_fun hφ k
      simp [hk]
    exact Prod.ext
      (by simp [SemidirectProduct.mul_left, hact])
      (by simp [SemidirectProduct.mul_right])

/-- Simplified conjugacy condition for isomorphism of semi direct products -/
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

/-- If K is cyclic p-group, two homomorphisms f g : K → Aut(H) define
    isomorphic semidirect products if they have the same image. -/
lemma semidirectProduct_iso_if_range_eq
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

/-- If K is cyclic p-group and Aut(H) is also cyclic, then two homomorphisms f g : K → Aut(H) define
    isomorphic semidirect products if their images have equal order -/
lemma semidirectProduct_iso_if_range_card_eq
    {H K : Type*} {p m : ℕ} [Group H] [Group K] [IsCyclic K] [Finite H]
    (hp : Fact p.Prime) (h_p_group : Nat.card K = p ^ m)
    (f_1 f_2 : K →* MulAut H) (h_mul_aut_cyclic : IsCyclic (MulAut H)) (h_range_card_eq : Nat.card f_1.range = Nat.card f_2.range) :
    Nonempty (SemidirectProduct H K f_1 ≃* SemidirectProduct H K f_2) := by
      -- 1. Prove the ambient group order is positive
      have h_pos : Nat.card (MulAut H) > 0 := Nat.card_pos

      -- 2. Apply the uniqueness lemma
      have h' : f_1.range = f_2.range := by
        exact cyclic_subgroup_of_cyclic_group_is_unique
          (by aesop)
          rfl
          f_1.range
          f_2.range
          rfl
          h_range_card_eq.symm

      grind [semidirectProduct_iso_if_range_eq]

/-- Given f : C_p × C_p →* Aut(C_q) with image of order p, and σ a generator of f.range
    (i.e. σ ∈ f.range with orderOf σ = p), there exist elements x, y of C_p × C_p that
    together generate C_p × C_p, with f(x) = σ and f(y) = 1. -/
lemma exists_generators_of_CpCp_action
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (f : CyclicGroup p × CyclicGroup p →* MulAut (CyclicGroup q))
    (hf_range : Nat.card f.range = p)
    (σ : MulAut (CyclicGroup q))
    (hσ_mem : σ ∈ f.range)
    (hσ_order : orderOf σ = p) :
    ∃ x y : CyclicGroup p × CyclicGroup p,
      Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤ ∧
      f x = σ ∧ f y = 1 := by
  -- Set up: |CyclicGroup p| = p
  haveI : NeZero p := ⟨hp.out.pos.ne'⟩
  have h_card_cp : Nat.card (CyclicGroup p) = p := card_cyclicGroup p
  -- Get a generator g of CyclicGroup p
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := CyclicGroup p)
  have hg_order : orderOf g = p := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, h_card_cp]
  -- f.range = Subgroup.zpowers σ (both have order p; σ ∈ f.range)
  have hσ_zpow_card : Nat.card (Subgroup.zpowers σ) = p := by
    rw [Nat.card_zpowers, hσ_order]
  have h_range_eq : f.range = Subgroup.zpowers σ := by
    have h_le : Subgroup.zpowers σ ≤ f.range := Subgroup.zpowers_le.mpr hσ_mem
    haveI : Finite f.range := by
      apply Nat.finite_of_card_ne_zero
      rw [hf_range]; exact hp.out.pos.ne'
    refine (Subgroup.eq_of_le_of_card_ge h_le ?_).symm
    rw [hσ_zpow_card, hf_range]
  -- Define x₀ := (g, 1), y₀ := (1, g)
  set x₀ : CyclicGroup p × CyclicGroup p := (g, 1) with hx₀_def
  set y₀ : CyclicGroup p × CyclicGroup p := (1, g) with hy₀_def
  -- Orders of x₀ and y₀
  have hx₀_order : orderOf x₀ = p := by
    show orderOf (g, (1 : CyclicGroup p)) = p
    rw [Prod.orderOf, orderOf_one, hg_order, Nat.lcm_one_right]
  have hy₀_order : orderOf y₀ = p := by
    show orderOf ((1 : CyclicGroup p), g) = p
    rw [Prod.orderOf, orderOf_one, hg_order, Nat.lcm_one_left]
  -- x₀, y₀ generate everything
  have h_gen_top : Subgroup.zpowers x₀ ⊔ Subgroup.zpowers y₀ = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
    have hab : (a, b) = x₀^i * y₀^j := by
      simp only [hx₀_def, hy₀_def, Prod.pow_def, Prod.mk_mul_mk,
        one_zpow, zpow_natCast, one_mul, mul_one]
      exact Prod.mk.injEq .. |>.mpr ⟨hi.symm, hj.symm⟩
    rw [hab]
    exact mul_mem
      (Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x₀) i))
      (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers y₀) j))
  -- f x₀ and f y₀ are powers of σ
  have hfx₀_mem : f x₀ ∈ Subgroup.zpowers σ :=
    h_range_eq ▸ MonoidHom.mem_range.mpr ⟨x₀, rfl⟩
  have hfy₀_mem : f y₀ ∈ Subgroup.zpowers σ :=
    h_range_eq ▸ MonoidHom.mem_range.mpr ⟨y₀, rfl⟩
  -- Helper: if τ ∈ ⟨σ⟩ and τ ≠ 1, then ∃ m, τ^m = σ
  have helper : ∀ τ : MulAut (CyclicGroup q), τ ∈ Subgroup.zpowers σ → τ ≠ 1 →
      ∃ m : ℤ, τ ^ m = σ := by
    intro τ hτ_mem hτ_ne
    haveI hp_prime : Nat.Prime p := hp.out
    have h_τ_order_dvd : orderOf τ ∣ p := by
      have h1 : orderOf (⟨τ, hτ_mem⟩ : Subgroup.zpowers σ) ∣ Nat.card (Subgroup.zpowers σ) :=
        orderOf_dvd_natCard _
      rwa [Subgroup.orderOf_mk, hσ_zpow_card] at h1
    have h_τ_order : orderOf τ = p := by
      rcases (Nat.dvd_prime hp_prime).mp h_τ_order_dvd with h1 | hp'
      · exact absurd (orderOf_eq_one_iff.mp h1) hτ_ne
      · exact hp'
    have h_τ_zpow_eq : Subgroup.zpowers τ = Subgroup.zpowers σ := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hτ_mem) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, h_τ_order, hσ_order]
    have hσ_in_τ : σ ∈ Subgroup.zpowers τ := h_τ_zpow_eq ▸ Subgroup.mem_zpowers σ
    exact Subgroup.mem_zpowers_iff.mp hσ_in_τ
  -- Helper: case 1 — if w₀ has order p, f w₀ ≠ 1, f w₀ ∈ ⟨σ⟩, then
  -- we can find x with f x = σ and ⟨x⟩ = ⟨w₀⟩.
  have case1 : ∀ w₀ : CyclicGroup p × CyclicGroup p, orderOf w₀ = p →
      f w₀ ≠ 1 → f w₀ ∈ Subgroup.zpowers σ →
      ∃ m : ℤ, f (w₀^m) = σ ∧ Subgroup.zpowers (w₀^m) = Subgroup.zpowers w₀ := by
    intro w₀ hw₀_order hfw₀_ne hfw₀_mem
    obtain ⟨m, hm⟩ := helper (f w₀) hfw₀_mem hfw₀_ne
    refine ⟨m, ?_, ?_⟩
    · rw [map_zpow]; exact hm
    · -- orderOf (w₀^m) = p since f(w₀^m) = σ has order p
      have hwm_order : orderOf (w₀^m) = p := by
        have h_f_ord : orderOf (f (w₀^m)) = p := by rw [map_zpow, hm]; exact hσ_order
        have h_f_dvd : orderOf (f (w₀^m)) ∣ orderOf (w₀^m) := orderOf_map_dvd f (w₀^m)
        rw [h_f_ord] at h_f_dvd
        have h_div : orderOf (w₀^m) ∣ orderOf w₀ := orderOf_zpow_dvd w₀ m
        rw [hw₀_order] at h_div
        exact Nat.dvd_antisymm h_div h_f_dvd
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · exact Subgroup.zpowers_le.mpr (Subgroup.zpow_mem (Subgroup.mem_zpowers w₀) m)
      · rw [Nat.card_zpowers, Nat.card_zpowers, hwm_order, hw₀_order]
  -- Now case split on whether f x₀ = 1
  by_cases hfx₀_one : f x₀ = 1
  · -- f x₀ = 1, so f y₀ ≠ 1
    have hfy₀_ne : f y₀ ≠ 1 := by
      intro h_one
      -- f is trivial on the generating set {x₀, y₀}, so f.range = ⊥
      have h_triv : ∀ z : CyclicGroup p × CyclicGroup p, f z = 1 := by
        intro z
        have hz : z ∈ Subgroup.zpowers x₀ ⊔ Subgroup.zpowers y₀ :=
          h_gen_top ▸ Subgroup.mem_top z
        rw [Subgroup.mem_sup] at hz
        obtain ⟨u, hu_mem, v, hv_mem, huv⟩ := hz
        obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hu_mem
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hv_mem
        rw [← huv, ← hi, ← hj, map_mul, map_zpow, map_zpow,
          hfx₀_one, h_one, one_zpow, one_zpow, one_mul]
      have h_range_bot : f.range = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        rintro x ⟨z, rfl⟩
        exact h_triv z
      have h_card_one : Nat.card f.range = 1 := by
        rw [h_range_bot]
        exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
      rw [hf_range] at h_card_one
      exact hp.out.one_lt.ne' h_card_one
    -- Apply case1 to y₀
    obtain ⟨m, hfym_eq, h_zpow_eq⟩ := case1 y₀ hy₀_order hfy₀_ne hfy₀_mem
    refine ⟨y₀^m, x₀, ?_, hfym_eq, hfx₀_one⟩
    rw [h_zpow_eq, sup_comm]
    exact h_gen_top
  · -- f x₀ ≠ 1
    obtain ⟨m, hfxm_eq, h_zpow_x_eq⟩ := case1 x₀ hx₀_order hfx₀_one hfx₀_mem
    -- Get n with f y₀ = σ^n
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hfy₀_mem
    let x := x₀^m
    let y := y₀ * x^(-n)
    have hfx_eq : f x = σ := hfxm_eq
    have hfy_eq : f y = 1 := by
      show f (y₀ * x^(-n)) = 1
      rw [map_mul, map_zpow, hfx_eq, hn]
      group
    refine ⟨x, y, ?_, hfx_eq, hfy_eq⟩
    -- Generation: y₀ = y * x^n, so ⟨x₀⟩ ⊔ ⟨y₀⟩ ⊆ ⟨x⟩ ⊔ ⟨y⟩
    rw [eq_top_iff]
    intro z _
    have hz_top : z ∈ Subgroup.zpowers x₀ ⊔ Subgroup.zpowers y₀ :=
      h_gen_top ▸ Subgroup.mem_top z
    -- Show ⟨x₀⟩ ≤ ⟨x⟩ ⊔ ⟨y⟩ and ⟨y₀⟩ ≤ ⟨x⟩ ⊔ ⟨y⟩
    have h_x₀_mem : x₀ ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
      show x₀ ∈ Subgroup.zpowers (x₀^m) ⊔ Subgroup.zpowers y
      rw [h_zpow_x_eq]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x₀)
    have h_y₀_mem : y₀ ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
      -- y₀ = y * x^n
      have h_y₀_eq : y₀ = y * x^n := by
        show y₀ = y₀ * x^(-n) * x^n
        rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
      rw [h_y₀_eq]
      exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
        (Subgroup.mem_sup_left (Subgroup.zpow_mem (Subgroup.mem_zpowers x) n))
    have h_sup_le : Subgroup.zpowers x₀ ⊔ Subgroup.zpowers y₀ ≤
        Subgroup.zpowers x ⊔ Subgroup.zpowers y :=
      sup_le (Subgroup.zpowers_le.mpr h_x₀_mem) (Subgroup.zpowers_le.mpr h_y₀_mem)
    exact h_sup_le hz_top

/-- Given two nontrivial homomorphisms f_1, f_2 : C_p × C_p →* Aut(C_q) whose images
    both have order p (and p ∣ q − 1), there exists an automorphism
    β : Aut(C_p × C_p) such that f_2 = f_1 ∘ β. -/
lemma exists_aut_of_CpCp_conjugating_actions
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (h_pdvd : p ∣ q - 1)
    (f_1 f_2 : CyclicGroup p × CyclicGroup p →* MulAut (CyclicGroup q))
    (hf1_range : Nat.card f_1.range = p)
    (hf2_range : Nat.card f_2.range = p) :
    ∃ β : MulAut (CyclicGroup p × CyclicGroup p),
      ∀ x : CyclicGroup p × CyclicGroup p, f_2 x = f_1 (β x) := by
  sorry

/-- Direct product of cyclic groups of coprime orders is cyclic of product order. -/
noncomputable def CyclicGroup.prodMulEquiv {m n : ℕ} [NeZero m] [NeZero n]
    (hcop : Nat.Coprime m n) :
    CyclicGroup m × CyclicGroup n ≃* CyclicGroup (m * n) := by
  haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  haveI : IsCyclic (CyclicGroup m × CyclicGroup n) :=
    Group.isCyclic_prod_iff.mpr ⟨inferInstance, inferInstance,
      by rw [card_cyclicGroup, card_cyclicGroup]; exact hcop⟩
  exact mulEquivOfCyclicCardEq (by simp only [Nat.card_prod, card_cyclicGroup])

/-- Any two nontrivial semidirect products C_q ⋊ (C_p × C_p) arising from homomorphisms
    with image of order p are isomorphic, provided p ∣ q − 1. -/
theorem semidirectProduct_CpCp_iso
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (h_pdvd : p ∣ q - 1)
    (f_1 f_2 : CyclicGroup p × CyclicGroup p →* MulAut (CyclicGroup q))
    (_ : f_1 ≠ 1) (_ : f_2 ≠ 1)
    (hf1_range : Nat.card f_1.range = p)
    (hf2_range : Nat.card f_2.range = p) :
    Nonempty (SemidirectProduct (CyclicGroup q) (CyclicGroup p × CyclicGroup p) f_1 ≃*
              SemidirectProduct (CyclicGroup q) (CyclicGroup p × CyclicGroup p) f_2) := by
  obtain ⟨β, hβ⟩ := exists_aut_of_CpCp_conjugating_actions h_pdvd f_1 f_2 hf1_range hf2_range
  exact semidirectProduct_iso_of_conjugate_action 1 β (fun x => by simp [hβ x])
