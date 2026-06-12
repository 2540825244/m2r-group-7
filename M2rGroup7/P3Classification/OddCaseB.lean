import Mathlib
import «M2rGroup7».SmallGroupsLibrary
import Mathlib.Algebra.Group.TypeTags.Basic

set_option maxHeartbeats 3200000
set_option linter.style.longLine false
set_option linter.style.refine false
set_option linter.style.cases false
set_option linter.flexible false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false

/-!
# Case B2 (odd prime): a has order p², b has order p → C_{p²} ⋊ C_p

We prove that a non-abelian group G of order p³ (p an odd prime) with elements
a of order p² and b of order p (non-commuting) is isomorphic to the semidirect
product `CyclicGroup (p^2) ⋊[cpSqAction p] CyclicGroup p`.
-/

variable {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime]

section BasicLemmas

/-- The subgroup ⟨a⟩ has index p when orderOf a = p² and |G| = p³ -/
lemma zpowers_index_eq_p (a : G) (ha : orderOf a = p ^ 2) (hcard : Nat.card G = p ^ 3) :
    (Subgroup.zpowers a).index = p := by
  have h_card : Nat.card (Subgroup.zpowers a) = p ^ 2 := by
    rw [Nat.card_zpowers, ha]
  have h_index : (Subgroup.zpowers a).index * p ^ 2 = p ^ 3 := by
    rw [← hcard, ← h_card, Subgroup.index_mul_card]
  nlinarith [hp.1.two_le]

/-- ⟨a⟩ is normal when it has index p (the smallest prime factor of p³) -/
lemma zpowers_normal_of_order_p_sq (a : G) (ha : orderOf a = p ^ 2)
    (hcard : Nat.card G = p ^ 3) :
    (Subgroup.zpowers a).Normal := by
  have h_index : (Subgroup.zpowers a).index = p :=
    zpowers_index_eq_p a ha hcard
  apply Subgroup.normal_of_index_eq_minFac_card
  rw [h_index, hcard]
  exact (Nat.Prime.pow_minFac hp.out (by omega)).symm

/-- If a and b don't commute, b cannot be in the cyclic (hence abelian) subgroup ⟨a⟩ -/
lemma b_not_mem_zpowers_a (a b : G) (hab : a * b ≠ b * a) :
    b ∉ Subgroup.zpowers a := by
  contrapose! hab
  obtain ⟨k, rfl⟩ := hab; group

/--
⟨a⟩ and ⟨b⟩ are disjoint when b has prime order and b ∉ ⟨a⟩
-/
lemma zpowers_disjoint_of_not_comm (a b : G) (hb : orderOf b = p)
    (hab : a * b ≠ b * a) :
    Disjoint (Subgroup.zpowers a) (Subgroup.zpowers b) := by
  have h_order_eq_p : ∀ x ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers b,
      x = 1 ∨ orderOf x = p := by
    intro x hx
    have h_order_div_p : orderOf x ∣ p := by
      exact hb ▸ orderOf_dvd_of_mem_zpowers hx.2
    rw [Nat.dvd_prime hp.1] at h_order_div_p; aesop
  have h_zpowers_eq : ∀ x ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers b, orderOf x = p →
      Subgroup.zpowers x = Subgroup.zpowers b := by
    intro x hx hx_order
    have h_card_eq : Nat.card (Subgroup.zpowers x) = Nat.card (Subgroup.zpowers b) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, hx_order, hb]
    apply SetLike.coe_injective
    apply Set.eq_of_subset_of_ncard_le
    · exact fun y hy => Subgroup.zpowers_le.mpr hx.2 hy
    · convert h_card_eq.ge using 1
    · have h_finite : Finite (Subgroup.zpowers b) := by
        have h_card : Nat.card (Subgroup.zpowers b) = p := by
          rw [Nat.card_zpowers, hb]
        exact Nat.finite_of_card_ne_zero (h_card.symm ▸ hp.1.ne_zero)
      exact Set.finite_coe_iff.mp h_finite
  simp_all +decide [Subgroup.disjoint_def]
  intro x hx₁ hx₂; specialize h_order_eq_p x hx₁ hx₂
  specialize h_zpowers_eq x hx₁ hx₂
  rcases h_order_eq_p with (rfl | h) <;> simp_all +decide
  have h_contradiction : b ∈ Subgroup.zpowers a := by
    exact Subgroup.zpowers_le.mpr hx₁ (h_zpowers_eq.symm ▸ Subgroup.mem_zpowers b)
  exact False.elim (b_not_mem_zpowers_a a b hab h_contradiction)

/-- ⟨a⟩ and ⟨b⟩ are complementary subgroups -/
lemma zpowers_complement' (a b : G) (ha : orderOf a = p ^ 2) (hb : orderOf b = p)
    (hab : a * b ≠ b * a) (hcard : Nat.card G = p ^ 3) :
    (Subgroup.zpowers a).IsComplement' (Subgroup.zpowers b) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero
    (by rw [hcard]; exact pow_ne_zero 3 (Nat.Prime.ne_zero hp.out))
  exact Subgroup.isComplement'_of_card_mul_and_disjoint
    (by rw [Nat.card_zpowers, Nat.card_zpowers, ha, hb, hcard]; ring)
    (zpowers_disjoint_of_not_comm a b hb hab)

end BasicLemmas

section Uniqueness

/--
In a cyclic group, two subgroups of the same finite cardinality are equal
-/
lemma IsCyclic.eq_subgroup_of_card_eq {A : Type*} [Group A] [IsCyclic A]
    (H K : Subgroup A) (hHK : Nat.card H = Nat.card K)
    (hH : Nat.card H ≠ 0) : H = K := by
  obtain ⟨g, hg⟩ : ∃ g : A, ∀ x : A, x ∈ Subgroup.zpowers g := IsCyclic.exists_generator
  obtain ⟨m, hm⟩ : ∃ m : ℕ, H = Subgroup.zpowers (g ^ m) := by
    have hH_cyclic : ∃ h : A, H = Subgroup.zpowers h := by
      have h_cyclic : IsCyclic H := inferInstance
      obtain ⟨x, hx⟩ := h_cyclic.exists_generator
      refine ⟨x, le_antisymm ?_ ?_⟩
      · exact fun y hy => by
          obtain ⟨n, hn⟩ := hx ⟨y, hy⟩
          exact ⟨n, by simpa [Subtype.ext_iff] using hn⟩
      · aesop
    obtain ⟨h, rfl⟩ := hH_cyclic; obtain ⟨m, rfl⟩ := hg h; use Int.natAbs m
    cases' Int.eq_nat_or_neg m with hm hm; aesop
  obtain ⟨n, hn⟩ : ∃ n : ℕ, K = Subgroup.zpowers (g ^ n) := by
    obtain ⟨k, hk⟩ := IsCyclic.exists_generator (α := K)
    have hK_gen : K = Subgroup.zpowers (k : A) := by
      refine le_antisymm ?_ ?_ <;> simp_all +decide [Subgroup.zpowers_le]
      exact fun x hx => by
        obtain ⟨n, hn⟩ := hk x hx
        exact ⟨n, by simpa [Subtype.ext_iff] using hn⟩
    obtain ⟨n, hn⟩ := hg k
    cases' Int.eq_nat_or_neg n with hn hn; aesop
  by_cases hm0 : m = 0 <;> by_cases hn0 : n = 0 <;> simp_all +decide [Nat.card_eq_zero]
  · rw [eq_comm, orderOf_eq_one_iff] at hHK; aesop
  · have h_eq : Nat.gcd (orderOf g) m = Nat.gcd (orderOf g) n := by
      simp_all +decide [orderOf_pow']
      rw [Nat.div_eq_iff_eq_mul_left
        (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero (by aesop)))] at hHK
      · nlinarith [Nat.div_mul_cancel (Nat.gcd_dvd_left (orderOf g) n),
          Nat.div_mul_cancel (Nat.gcd_dvd_left (orderOf g) m),
          Nat.pos_of_ne_zero (show orderOf g ≠ 0 from hH.orderOf_pos.ne')]
      · exact Nat.gcd_dvd_left _ _
    have h_eq_subgroup :
        Subgroup.zpowers (g ^ m) = Subgroup.zpowers (g ^ Nat.gcd (orderOf g) m) ∧
        Subgroup.zpowers (g ^ n) = Subgroup.zpowers (g ^ Nat.gcd (orderOf g) n) := by
      constructor <;> refine le_antisymm ?_ ?_ <;> simp +decide [Subgroup.zpowers_le]
      · obtain ⟨k, hk⟩ := Nat.gcd_dvd_right (orderOf g) m
        rw [hk, pow_mul, ← hk]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
      · have := Nat.gcd_eq_gcd_ab (orderOf g) m
        replace this := congr_arg (fun x : ℤ => g ^ x) this
        simp_all +decide [zpow_add, zpow_mul]
      · have : ∃ k : ℕ, n = k * Nat.gcd (orderOf g) n :=
          exists_eq_mul_left_of_dvd (Nat.gcd_dvd_right _ _)
        obtain ⟨k, hk⟩ := this; rw [hk]; simp +decide [pow_mul']
        rw [← hk]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
      · have := Nat.gcd_eq_gcd_ab (orderOf g) n
        simp_all +decide [← zpow_natCast, ← zpow_mul]
        simp +decide [zpow_add, zpow_mul, pow_orderOf_eq_one]
    grind

/--
Non-trivial hom from C_p (p prime) to a group sends the generator to
    an element of order p
-/
lemma order_image_of_nontrivial_hom {A : Type*} [Group A]
    (φ : CyclicGroup p →* A) (hφ : φ ≠ 1) :
    orderOf (φ (Multiplicative.ofAdd (1 : ZMod p))) = p := by
  have h_order : orderOf (φ (Multiplicative.ofAdd 1)) ∣ p := by
    convert orderOf_map_dvd _ _
    convert (ZMod.addOrderOf_one p).symm
  contrapose! hφ
  have h_kernel : ∀ b : CyclicGroup p, φ b = 1 := by
    intro b
    have hb : ∃ k : ℤ, b = (Multiplicative.ofAdd 1) ^ k := by
      have : ∀ b : ZMod p, ∃ k : ℤ, b = k • (1 : ZMod p) :=
        fun b => ⟨b.val, by simp +decide⟩
      convert this (Multiplicative.toAdd b) using 1
    obtain ⟨k, hk⟩ := hb
    rw [hk]
    rw [orderOf_dvd_iff_pow_eq_one] at h_order
    have := orderOf_dvd_iff_pow_eq_one.mpr h_order
    simp_all +decide [Nat.dvd_prime hp.1]
    calc φ (Multiplicative.ofAdd (1 : ZMod p) ^ k)
        = φ (Multiplicative.ofAdd (1 : ZMod p)) ^ k := map_zpow φ (Multiplicative.ofAdd (1 : ZMod p)) k
      _ = 1 ^ k := by rw [this]
      _ = 1 := one_zpow k
  exact MonoidHom.ext h_kernel

/--
Given two elements of the same prime order in a cyclic group,
    one is a power of the other
-/
lemma exists_pow_eq_of_same_order_in_cyclic {A : Type*} [Group A] [IsCyclic A]
    {σ τ : A} (hσ : orderOf σ = p) (hτ : orderOf τ = p) :
    ∃ k : ℕ, σ = τ ^ k := by
  have h_subgroup : Subgroup.zpowers σ = Subgroup.zpowers τ := by
    apply IsCyclic.eq_subgroup_of_card_eq
    · rw [Nat.card_zpowers, Nat.card_zpowers, hσ, hτ]
    · rw [Nat.card_zpowers, hσ]; exact hp.1.ne_zero
  have := Subgroup.mem_zpowers_iff.mp (h_subgroup ▸ Subgroup.mem_zpowers σ)
  obtain ⟨k, hk⟩ := this
  refine ⟨Int.toNat (k % p), ?_⟩
  rw [← hk, ← zpow_mod_orderOf, hτ]
  rw [← zpow_natCast,
    Int.toNat_of_nonneg (Int.emod_nonneg _ (Nat.cast_ne_zero.mpr hp.1.ne_zero))]

/--
Helper: every element of CyclicGroup p is a zpow of the generator
-/
private lemma cyclic_gen_generates (x : CyclicGroup p) :
    ∃ n : ℤ, x = (Multiplicative.ofAdd 1 : CyclicGroup p) ^ n := by
  have : ∀ b : ZMod p, ∃ k : ℤ, b = k • (1 : ZMod p) :=
    fun b => ⟨b.val, by simp +decide⟩
  convert this (Multiplicative.toAdd x) using 1

/--
Key uniqueness lemma: for any two non-trivial homomorphisms φ₁ φ₂ : C_p →* Aut(C_{p²}),
    the semidirect products are isomorphic.
-/
lemma semidirect_unique_of_nontrivial (hp_odd : p ≠ 2)
    (φ₁ φ₂ : CyclicGroup p →* MulAut (CyclicGroup (p ^ 2)))
    (h₁ : φ₁ ≠ 1) (h₂ : φ₂ ≠ 1) :
    Nonempty (CyclicGroup (p ^ 2) ⋊[φ₁] CyclicGroup p ≃*
              CyclicGroup (p ^ 2) ⋊[φ₂] CyclicGroup p) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.gcd k p = 1 ∧
      φ₁ (Multiplicative.ofAdd 1) = φ₂ (Multiplicative.ofAdd (k : ZMod p)) := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, φ₁ (Multiplicative.ofAdd 1) =
        φ₂ (Multiplicative.ofAdd (k : ZMod p)) := by
      have h_conj : ∃ k : ℕ, φ₁ (Multiplicative.ofAdd 1) =
          (φ₂ (Multiplicative.ofAdd 1)) ^ k := by
        have h_order : orderOf (φ₁ (Multiplicative.ofAdd 1)) = p ∧
            orderOf (φ₂ (Multiplicative.ofAdd 1)) = p :=
          ⟨order_image_of_nontrivial_hom φ₁ h₁, order_image_of_nontrivial_hom φ₂ h₂⟩
        convert exists_pow_eq_of_same_order_in_cyclic h_order.1 h_order.2 using 1
        obtain ⟨f⟩ := aut_of_cyclic_p2 (h_p_prime := hp)
        exact isCyclic_of_surjective f.symm f.symm.surjective
      obtain ⟨k, hk⟩ := h_conj; use k; simp_all +decide [← map_pow]
      erw [← ofAdd_nsmul]; norm_num
    refine ⟨k, ?_, hk⟩
    refine Nat.Coprime.symm (hp.1.coprime_iff_not_dvd.mpr ?_)
    intro hkp
    apply h₁
    have hk0 : (k : ZMod p) = 0 := by rwa [ZMod.natCast_eq_zero_iff k p]
    rw [hk0] at hk; simp at hk
    ext x; obtain ⟨n, rfl⟩ := cyclic_gen_generates x
    simp [map_zpow, hk]
    have htriv : φ₁ (Multiplicative.ofAdd 1) = 1 := by
      rw [hk]; exact map_one φ₂
    have hpow : φ₁ (Multiplicative.ofAdd 1 ^ n) = 1 := by
      calc φ₁ (Multiplicative.ofAdd 1 ^ n)
          = φ₁ (Multiplicative.ofAdd 1) ^ n := map_zpow φ₁ _ n
        _ = 1 ^ n := by rw [htriv]
        _ = 1 := one_zpow n
    rename_i x
    have htriv : φ₁ (Multiplicative.ofAdd 1) = 1 := by rw [hk]; exact map_one φ₂
    calc (φ₁ (Multiplicative.ofAdd 1 ^ n)) x
        = (φ₁ (Multiplicative.ofAdd 1) ^ n) x := by
            congr 1; exact φ₁.map_zpow (Multiplicative.ofAdd 1) n
      _ = (1 ^ n : MulAut _) x := by rw [htriv]
      _ = x := by simp [one_zpow]
  -- Define the automorphism `fg` of `CyclicGroup p` that sends `gen` to `gen^k`.
  obtain ⟨fg, hfg⟩ : ∃ fg : CyclicGroup p ≃* CyclicGroup p,
      fg (Multiplicative.ofAdd 1) = Multiplicative.ofAdd (k : ZMod p) := by
    have h_mul_k_aut : ∃ fg : (ZMod p) ≃+ (ZMod p), fg 1 = k := by
      have h_data : ∃ fg : (ZMod p) →+ (ZMod p), fg 1 = k ∧ Function.Bijective fg := by
        refine ⟨AddMonoidHom.mk' (fun x => k * x) ?_, ?_, ?_⟩
          <;> simp_all +decide [Function.Bijective]
        · exact fun a b => mul_add _ _ _
        · have hku : IsUnit (k : ZMod p) := by
            rw [ZMod.isUnit_iff_coprime]; aesop
          exact ⟨fun x y hxy => by simpa [hku.mul_right_inj] using hxy,
                 fun x => by obtain ⟨y, hy⟩ := hku.exists_right_inv;
                              exact ⟨y * x, by linear_combination' hy * x⟩⟩
      exact ⟨AddEquiv.ofBijective h_data.choose h_data.choose_spec.2,
             h_data.choose_spec.1⟩
    exact ⟨h_mul_k_aut.choose.toMultiplicative,
           by simpa using congr_arg Multiplicative.ofAdd h_mul_k_aut.choose_spec⟩
  -- φ₁ = φ₂ ∘ fg
  have h_phi_eq : ∀ x : CyclicGroup p, φ₁ x = φ₂ (fg x) := by
    intro x
    obtain ⟨n, rfl⟩ := cyclic_gen_generates x
    calc φ₁ (Multiplicative.ofAdd 1 ^ n)
        = φ₁ (Multiplicative.ofAdd 1) ^ n := φ₁.map_zpow (Multiplicative.ofAdd 1) n
      _ = φ₂ (fg (Multiplicative.ofAdd 1)) ^ n := by rw [hfg, hk.2]
      _ = φ₂ (fg (Multiplicative.ofAdd 1) ^ n) := (φ₂.map_zpow _ n).symm
      _ = φ₂ (fg (Multiplicative.ofAdd 1 ^ n)) := by
            congr 1; exact (fg.toMonoidHom.map_zpow _ n).symm
  refine ⟨?_⟩
  exact {
    toFun := fun x => ⟨x.left, fg x.right⟩
    invFun := fun x => ⟨x.left, fg.symm x.right⟩
    left_inv := fun x => by cases x; simp [SemidirectProduct.ext_iff]
    right_inv := fun x => by cases x; simp [SemidirectProduct.ext_iff]
    map_mul' := fun x y => by
      cases x with | mk xl xr =>
      cases y with | mk yl yr =>
      simp only [SemidirectProduct.mul_def]
      ext
      · -- left component: xl * (φ₁ xr) yl = xl * (φ₂ (fg xr)) yl
        change xl * (φ₁ xr) yl = xl * (φ₂ (fg xr)) yl
        congr 1; rw [← h_phi_eq]
      · -- right component: fg (xr * yr) = fg xr * fg yr
        exact map_mul fg xr yr
  }

end Uniqueness

section MainTheorem

/-- `cyclicHom n a h` sends the canonical generator `Multiplicative.ofAdd 1`
of `CyclicGroup n` to `a`. -/
lemma cyclicHom_gen (n : ℕ) [NeZero n] {G : Type*} [Group G] (a : G) (h : a ^ n = 1) :
    cyclicHom n a h (Multiplicative.ofAdd (1 : ZMod n)) = a := by
  unfold cyclicHom
  change Additive.toMul (((ZMod.lift n)
    ⟨(zmultiplesHom (Additive G)) (Additive.ofMul a), _⟩) (1 : ZMod n)) = a
  have h1 : (1 : ZMod n) = ((1 : ℤ) : ZMod n) := by push_cast; ring
  rw [h1, ZMod.lift_coe]
  simp [zmultiplesHom_apply]

/-- The image of the generator of `C_p` under `cpSqAction p` is the canonical
order-`p` automorphism `cpSqAut p`. -/
lemma cpSqAction_gen :
    cpSqAction p (Multiplicative.ofAdd 1) = cpSqAut p :=
  cyclicHom_gen p (cpSqAut p) (cpSqAut_pow_p p)

/-- `cpSqAction p` is non-trivial.

(The hypothesis `hp_odd : p ≠ 2` is unnecessary for the computable construction,
but kept so this is a drop-in replacement for the original lemma.) -/
lemma cpSqAction_nontrivial (hp_odd : p ≠ 2) :
    cpSqAction p ≠ 1 := by
  intro h
  -- Evaluate the (supposedly trivial) hom on the generator: it equals `cpSqAut p`.
  have h_gen : cpSqAut p = 1 := by
    have hg := cpSqAction_gen (p := p)
    rw [h] at hg
    simpa using hg.symm
  -- `cpSqAut p` sends the generator of `C_{p²}` to `Multiplicative.ofAdd ((1 + p) * 1)`.
  have h_eval : cpSqAut p (Multiplicative.ofAdd (1 : ZMod (p ^ 2)))
      = Multiplicative.ofAdd ((onePlusP p : ZMod (p ^ 2)) * 1) := rfl
  rw [h_gen] at h_eval
  simp only [MulAut.one_apply] at h_eval
  -- Hence `onePlusP p = 1` in `ZMod (p²)`.
  have h_unit : (onePlusP p : ZMod (p ^ 2)) = 1 := by
    have := congrArg Multiplicative.toAdd h_eval.symm
    simpa using this
  -- But `onePlusP p = 1 + p`, so `p = 0` in `ZMod (p²)`.
  have hval : (onePlusP p : ZMod (p ^ 2)) = 1 + (p : ZMod (p ^ 2)) := by
    unfold onePlusP
    rw [ZMod.coe_unitOfCoprime]; push_cast; ring
  rw [hval] at h_unit
  have h_p_zero : (p : ZMod (p ^ 2)) = 0 := by
    have h2 : (1 : ZMod (p ^ 2)) + (p : ZMod (p ^ 2)) = 1 + 0 := by rw [add_zero]; exact h_unit
    exact add_left_cancel h2
  rw [ZMod.natCast_eq_zero_iff] at h_p_zero
  -- `p² ∣ p` is impossible for a prime `p`.
  have hp2 : p ^ 2 ≤ p := Nat.le_of_dvd hp.1.pos h_p_zero
  nlinarith [hp.1.two_le]

/--
Helper: the semidirect product transport from H ⋊ K to C_{p²} ⋊ C_p
-/
private lemma semidirect_transport
    {H K : Subgroup G} [H.Normal] (hc : H.IsComplement' K)
    (e₁ : H ≃* CyclicGroup (p ^ 2)) (e₂ : K ≃* CyclicGroup p) :
    ∃ ψ' : CyclicGroup p →* MulAut (CyclicGroup (p ^ 2)),
      Nonempty (G ≃* CyclicGroup (p ^ 2) ⋊[ψ'] CyclicGroup p) := by
  let ψ : K →* MulAut H :=
    H.normalizerMonoidHom.comp (Subgroup.inclusion Subgroup.le_normalizer_of_normal)
  let ψ' : CyclicGroup p →* MulAut (CyclicGroup (p ^ 2)) :=
    (MulAut.congr e₁).toMonoidHom.comp (ψ.comp e₂.symm.toMonoidHom)
  refine ⟨ψ', ?_⟩
  have f := (SemidirectProduct.mulEquivSubgroup hc).symm
  refine ⟨f.trans ?_⟩
  exact {
    toFun := fun x => ⟨e₁ x.left, e₂ x.right⟩
    invFun := fun x => ⟨e₁.symm x.left, e₂.symm x.right⟩
    left_inv := fun x => by cases x; simp [SemidirectProduct.ext_iff]
    right_inv := fun x => by cases x; simp [SemidirectProduct.ext_iff]
    map_mul' := fun x y => by
      cases x with | mk xl xr =>
      cases y with | mk yl yr =>
      simp only [SemidirectProduct.mul_def]
      ext
      · -- left: e₁ (xl * (ψ xr) yl) = e₁ xl * (ψ' (e₂ xr)) (e₁ yl)
        change e₁ (xl * (ψ xr) yl) = e₁ xl * (ψ' (e₂ xr)) (e₁ yl)
        rw [map_mul]
        congr 1
        simp [ψ', MulAut.congr]
      · exact map_mul e₂ xr yr
  }

/--
Helper: if ψ induces a commutative semidirect product, then G is abelian
-/
private lemma semidirect_trivial_implies_abelian
    (ψ : CyclicGroup p →* MulAut (CyclicGroup (p ^ 2)))
    (hψ_trivial : ψ = 1)
    (f : G ≃* CyclicGroup (p ^ 2) ⋊[ψ] CyclicGroup p) :
    ∀ x y : G, x * y = y * x := by
  intro x y
  apply f.injective
  simp only [map_mul]
  have comm : ∀ (a b : CyclicGroup (p ^ 2) ⋊[ψ] CyclicGroup p), a * b = b * a := by
    intro a b
    cases a with | mk al ar =>
    cases b with | mk bl br =>
    simp only [SemidirectProduct.mul_def]
    ext
    · simp [hψ_trivial, mul_comm]
    · simp [mul_comm]
  exact comm (f x) (f y)

/--
Case B2 odd: a non-abelian group of order p³ with elements of order p² and p
    is isomorphic to C_{p²} ⋊[cpSqAction p] C_p
-/
theorem case_B2_odd_isom (hp_odd : p ≠ 2)
    (a b : G) (ha : orderOf a = p ^ 2) (hb : orderOf b = p)
    (hab : a * b ≠ b * a) (hcard : Nat.card G = p ^ 3) :
    Nonempty (G ≃* CyclicGroup (p ^ 2) ⋊[cpSqAction p] CyclicGroup p) := by
  set H := Subgroup.zpowers a
  set K := Subgroup.zpowers b
  have hH_normal : H.Normal :=
    zpowers_normal_of_order_p_sq a ha hcard
  have hH_complement : H.IsComplement' K :=
    zpowers_complement' a b ha hb hab hcard
  -- Get isomorphisms H ≃* CyclicGroup (p^2) and K ≃* CyclicGroup p
  have hH_card : Nat.card H = p ^ 2 := by rw [Nat.card_zpowers, ha]
  have hK_card : Nat.card K = p := by rw [Nat.card_zpowers, hb]
  have hH_cyclic : IsCyclic H :=
    ⟨⟨⟨a, Subgroup.mem_zpowers a⟩, fun x => by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x.2
      exact ⟨n, Subtype.ext hn⟩⟩⟩
  have e₁ : H ≃* CyclicGroup (p ^ 2) := by
    have := (MulEquiv.symm <| zmodCyclicMulEquiv hH_cyclic)
    rw [hH_card] at this; exact this
  have e₂ : K ≃* CyclicGroup p := by
    have := (MulEquiv.symm <| zmodCyclicMulEquiv (inferInstance : IsCyclic K))
    rw [hK_card] at this; exact this
  -- Get the semidirect product decomposition
  obtain ⟨ψ, hψ⟩ := semidirect_transport hH_complement e₁ e₂
  -- Show ψ is non-trivial
  have hψ_nontrivial : ψ ≠ 1 := by
    intro hψ_trivial
    obtain ⟨f⟩ := hψ
    exact hab (semidirect_trivial_implies_abelian ψ hψ_trivial f a b)
  -- Apply uniqueness
  have hψ_iso := semidirect_unique_of_nontrivial hp_odd ψ (cpSqAction p)
    hψ_nontrivial (cpSqAction_nontrivial hp_odd)
  exact hψ.elim fun e => hψ_iso.elim fun e' => ⟨e.trans e'⟩

end MainTheorem
