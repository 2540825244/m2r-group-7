import Mathlib
import «M2rGroup7».CpSqAction

set_option maxHeartbeats 3200000

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

/-
⟨a⟩ and ⟨b⟩ are disjoint when b has prime order and b ∉ ⟨a⟩
-/
lemma zpowers_disjoint_of_not_comm (a b : G) (hb : orderOf b = p)
    (hab : a * b ≠ b * a) :
    Disjoint (Subgroup.zpowers a) (Subgroup.zpowers b) := by
  -- Since the order of $x$ divides $p$, we have $orderOf x = p$.
  have h_order_eq_p : ∀ x ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers b, x = 1 ∨ orderOf x = p := by
    intro x hx
    have h_order_div_p : orderOf x ∣ p := by
      exact hb ▸ orderOf_dvd_of_mem_zpowers hx.2;
    rw [ Nat.dvd_prime hp.1 ] at h_order_div_p ; aesop;
  -- If $orderOf x = p$, then $zpowers x = zpowers b$.
  have h_zpowers_eq : ∀ x ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers b, orderOf x = p → Subgroup.zpowers x = Subgroup.zpowers b := by
    intro x hx hx_order
    have h_card_eq : Nat.card (Subgroup.zpowers x) = Nat.card (Subgroup.zpowers b) := by
      rw [ Nat.card_zpowers, Nat.card_zpowers, hx_order, hb ];
    apply SetLike.coe_injective;
    apply Set.eq_of_subset_of_ncard_le;
    · exact fun y hy => Subgroup.zpowers_le.mpr hx.2 hy;
    · convert h_card_eq.ge using 1;
    · have h_finite : Finite (Subgroup.zpowers b) := by
        have h_card : Nat.card (Subgroup.zpowers b) = p := by
          rw [ Nat.card_zpowers, hb ]
        exact Nat.finite_of_card_ne_zero ( h_card.symm ▸ hp.1.ne_zero );
      exact Set.finite_coe_iff.mp h_finite;
  simp_all +decide [ Subgroup.disjoint_def ];
  intro x hx₁ hx₂; specialize h_order_eq_p x hx₁ hx₂; specialize h_zpowers_eq x hx₁ hx₂; rcases h_order_eq_p with ( rfl | h ) <;> simp_all +decide ;
  have h_contradiction : b ∈ Subgroup.zpowers a := by
    exact Subgroup.zpowers_le.mpr hx₁ ( h_zpowers_eq.symm ▸ Subgroup.mem_zpowers b );
  exact False.elim ( b_not_mem_zpowers_a a b hab h_contradiction )

/-- ⟨a⟩ and ⟨b⟩ are complementary subgroups -/
lemma zpowers_complement' (a b : G) (ha : orderOf a = p ^ 2) (hb : orderOf b = p)
    (hab : a * b ≠ b * a) (hcard : Nat.card G = p ^ 3) :
    (Subgroup.zpowers a).IsComplement' (Subgroup.zpowers b) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 (Nat.Prime.ne_zero hp.out))
  exact Subgroup.isComplement'_of_card_mul_and_disjoint
    (by rw [Nat.card_zpowers, Nat.card_zpowers, ha, hb, hcard]; ring)
    (zpowers_disjoint_of_not_comm a b hb hab)

end BasicLemmas

section Uniqueness

/-
In a cyclic group, two subgroups of the same finite cardinality are equal
-/
lemma IsCyclic.eq_subgroup_of_card_eq {A : Type*} [Group A] [IsCyclic A]
    (H K : Subgroup A) (hHK : Nat.card H = Nat.card K)
    (hH : Nat.card H ≠ 0) : H = K := by
  -- Let $g$ be a generator of the cyclic group $A$.
  obtain ⟨g, hg⟩ : ∃ g : A, ∀ x : A, x ∈ Subgroup.zpowers g := by
    exact IsCyclic.exists_generator;
  -- Since $H$ and $K$ are both subgroups of a cyclic group, they are also cyclic. Therefore, $H = \langle g^m \rangle$ and $K = \langle g^n \rangle$ for some integers $m$ and $n$.
  obtain ⟨m, hm⟩ : ∃ m : ℕ, H = Subgroup.zpowers (g ^ m) := by
    -- Since $H$ is a subgroup of a cyclic group, it is also cyclic.
    have hH_cyclic : ∃ h : A, H = Subgroup.zpowers h := by
      have h_cyclic : IsCyclic H := by
        exact inferInstance;
      obtain ⟨ x, hx ⟩ := h_cyclic.exists_generator;
      refine' ⟨ x, le_antisymm _ _ ⟩;
      · exact fun y hy => by obtain ⟨ n, hn ⟩ := hx ⟨ y, hy ⟩ ; exact ⟨ n, by simpa [ Subtype.ext_iff ] using hn ⟩ ;
      · aesop;
    obtain ⟨ h, rfl ⟩ := hH_cyclic; obtain ⟨ m, rfl ⟩ := hg h; use Int.natAbs m; cases' Int.eq_nat_or_neg m with hm hm ; aesop;
  obtain ⟨n, hn⟩ : ∃ n : ℕ, K = Subgroup.zpowers (g ^ n) := by
    obtain ⟨ k, hk ⟩ := IsCyclic.exists_generator ( α := K );
    -- Since $k$ is a generator of $K$, we have $K = \langle k \rangle$.
    have hK_gen : K = Subgroup.zpowers (k : A) := by
      refine' le_antisymm _ _ <;> simp_all +decide [ Subgroup.zpowers_le ];
      exact fun x hx => by obtain ⟨ n, hn ⟩ := hk x hx; exact ⟨ n, by simpa [ Subtype.ext_iff ] using hn ⟩ ;
    obtain ⟨ n, hn ⟩ := hg k;
    cases' Int.eq_nat_or_neg n with hn hn ; aesop;
  by_cases hm0 : m = 0 <;> by_cases hn0 : n = 0 <;> simp_all +decide [ Nat.card_eq_zero ];
  · rw [ eq_comm, orderOf_eq_one_iff ] at hHK ; aesop;
  · have h_eq : Nat.gcd (orderOf g) m = Nat.gcd (orderOf g) n := by
      simp_all +decide [ orderOf_pow' ];
      rw [ Nat.div_eq_iff_eq_mul_left ( Nat.gcd_pos_of_pos_left _ ( Nat.pos_of_ne_zero ( by aesop ) ) ) ] at hHK;
      · nlinarith [ Nat.div_mul_cancel ( Nat.gcd_dvd_left ( orderOf g ) n ), Nat.div_mul_cancel ( Nat.gcd_dvd_left ( orderOf g ) m ), Nat.pos_of_ne_zero ( show orderOf g ≠ 0 from hH.orderOf_pos.ne' ) ];
      · exact Nat.gcd_dvd_left _ _;
    have h_eq_subgroup : Subgroup.zpowers (g ^ m) = Subgroup.zpowers (g ^ Nat.gcd (orderOf g) m) ∧ Subgroup.zpowers (g ^ n) = Subgroup.zpowers (g ^ Nat.gcd (orderOf g) n) := by
      constructor <;> refine' le_antisymm _ _ <;> simp +decide [ Subgroup.zpowers_le ];
      · obtain ⟨ k, hk ⟩ := Nat.gcd_dvd_right ( orderOf g ) m;
        rw [ hk, pow_mul ];
        rw [ ← hk ] ; exact Subgroup.pow_mem _ ( Subgroup.mem_zpowers _ ) _;
      · have := Nat.gcd_eq_gcd_ab ( orderOf g ) m;
        replace this := congr_arg ( fun x : ℤ => g ^ x ) this ; simp_all +decide [ zpow_add, zpow_mul ] ;
      · have h_eq_subgroup : ∃ k : ℕ, n = k * Nat.gcd (orderOf g) n := by
          exact exists_eq_mul_left_of_dvd ( Nat.gcd_dvd_right _ _ );
        obtain ⟨ k, hk ⟩ := h_eq_subgroup; rw [ hk ] ; simp +decide [ pow_mul' ] ;
        rw [ ← hk ];
        exact Subgroup.pow_mem _ ( Subgroup.mem_zpowers _ ) _;
      · have := Nat.gcd_eq_gcd_ab ( orderOf g ) n;
        simp_all +decide [ ← zpow_natCast, ← zpow_mul ];
        simp +decide [ zpow_add, zpow_mul, pow_orderOf_eq_one ];
    grind

/-
Non-trivial hom from C_p (p prime) to a group sends the generator to
    an element of order p
-/
lemma order_image_of_nontrivial_hom {A : Type*} [Group A]
    (φ : CyclicGroup p →* A) (hφ : φ ≠ 1) :
    orderOf (φ (Multiplicative.ofAdd (1 : ZMod p))) = p := by
  have h_order : orderOf (φ (Multiplicative.ofAdd 1)) ∣ p := by
    convert orderOf_map_dvd _ _;
    convert ( ZMod.addOrderOf_one p ).symm;
  contrapose! hφ;
  have h_kernel : ∀ b : CyclicGroup p, φ b = 1 := by
    intro b
    have hb : ∃ k : ℤ, b = (Multiplicative.ofAdd 1)^k := by
      have h_gen : ∀ b : CyclicGroup p, ∃ k : ℤ, b = (Multiplicative.ofAdd 1) ^ k := by
        intro b
        have h_gen : ∃ k : ℤ, b = (Multiplicative.ofAdd 1) ^ k := by
          have h_gen : ∀ b : ZMod p, ∃ k : ℤ, b = k • (1 : ZMod p) := by
            exact fun b => ⟨ b.val, by simp +decide ⟩
          convert h_gen ( Multiplicative.toAdd b ) using 1
        exact h_gen;
      exact h_gen b
    obtain ⟨k, hk⟩ := hb
    rw [hk]
    simp [pow_mul];
    rw [ orderOf_dvd_iff_pow_eq_one ] at h_order;
    have := orderOf_dvd_iff_pow_eq_one.mpr h_order; simp_all +decide [ Nat.dvd_prime hp.1 ] ;
  exact MonoidHom.ext h_kernel

/-
Given two elements of the same prime order in a cyclic group,
    one is a power of the other
-/
lemma exists_pow_eq_of_same_order_in_cyclic {A : Type*} [Group A] [IsCyclic A]
    {σ τ : A} (hσ : orderOf σ = p) (hτ : orderOf τ = p) :
    ∃ k : ℕ, σ = τ ^ k := by
  -- By IsCyclic.eq_subgroup_of_card_eq, zpowers σ = zpowers τ.
  have h_subgroup : Subgroup.zpowers σ = Subgroup.zpowers τ := by
    apply IsCyclic.eq_subgroup_of_card_eq;
    · rw [ Nat.card_zpowers, Nat.card_zpowers, hσ, hτ ];
    · simp +decide [ Nat.card_eq_fintype_card, Fintype.card_zpowers, hσ, hτ, hp.1.ne_zero ];
  have := Subgroup.mem_zpowers_iff.mp ( h_subgroup ▸ Subgroup.mem_zpowers σ );
  obtain ⟨ k, hk ⟩ := this;
  refine' ⟨ Int.toNat ( k % p ), _ ⟩;
  rw [ ← hk, ← zpow_mod_orderOf, hτ ];
  rw [ ← zpow_natCast, Int.toNat_of_nonneg ( Int.emod_nonneg _ ( Nat.cast_ne_zero.mpr hp.1.ne_zero ) ) ]

/-
Key uniqueness lemma: for any two non-trivial homomorphisms φ₁ φ₂ : C_p →* Aut(C_{p²}),
    the semidirect products are isomorphic.
-/
lemma semidirect_unique_of_nontrivial (hp_odd : p ≠ 2)
    (φ₁ φ₂ : CyclicGroup p →* MulAut (CyclicGroup (p ^ 2)))
    (h₁ : φ₁ ≠ 1) (h₂ : φ₂ ≠ 1) :
    Nonempty (CyclicGroup (p ^ 2) ⋊[φ₁] CyclicGroup p ≃*
              CyclicGroup (p ^ 2) ⋊[φ₂] CyclicGroup p) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.gcd k p = 1 ∧ φ₁ (Multiplicative.ofAdd 1) = φ₂ (Multiplicative.ofAdd (k : ZMod p)) := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, φ₁ (Multiplicative.ofAdd 1) = φ₂ (Multiplicative.ofAdd (k : ZMod p)) := by
      -- Since the automorphism group is cyclic, any two elements of order p are conjugate. This means there exists a k such that σ₁ = σ₂^k.
      have h_conj : ∃ k : ℕ, φ₁ (Multiplicative.ofAdd 1) = (φ₂ (Multiplicative.ofAdd 1)) ^ k := by
        have h_order : orderOf (φ₁ (Multiplicative.ofAdd 1)) = p ∧ orderOf (φ₂ (Multiplicative.ofAdd 1)) = p := by
          exact ⟨ order_image_of_nontrivial_hom φ₁ h₁, order_image_of_nontrivial_hom φ₂ h₂ ⟩;
        convert exists_pow_eq_of_same_order_in_cyclic h_order.1 h_order.2 using 1;
        obtain ⟨ f ⟩ := aut_of_cyclic_p2 ( h_p_prime := hp );
        exact isCyclic_of_surjective f.symm f.symm.surjective;
      obtain ⟨ k, hk ⟩ := h_conj; use k; simp_all +decide [ ← map_pow ] ;
      erw [ ← ofAdd_nsmul ] ; norm_num;
    refine' ⟨ k, _, hk ⟩;
    refine' Nat.Coprime.symm ( hp.1.coprime_iff_not_dvd.mpr _ );
    contrapose! h₁; have := order_image_of_nontrivial_hom φ₁; simp_all +decide [ pow_eq_one_iff ] ;
    obtain ⟨ m, rfl ⟩ := h₁; simp_all +decide [ pow_mul, orderOf_eq_iff ] ;
    exact Classical.not_not.1 fun h => hp.1.ne_one <| this h ▸ rfl;
  -- Define the automorphism `fg` of `CyclicGroup p` that sends `gen` to `gen^k`.
  obtain ⟨fg, hfg⟩ : ∃ fg : CyclicGroup p ≃* CyclicGroup p, fg (Multiplicative.ofAdd 1) = Multiplicative.ofAdd (k : ZMod p) := by
    -- Since $k$ is coprime to $p$, multiplication by $k$ is an automorphism of $ZMod p$.
    have h_mul_k_aut : ∃ fg : (ZMod p) ≃+ (ZMod p), fg 1 = k := by
      have h_mul_k_aut : ∃ fg : (ZMod p) →+ (ZMod p), fg 1 = k ∧ Function.Bijective fg := by
        refine' ⟨ AddMonoidHom.mk' ( fun x => k * x ) _, _, _ ⟩ <;> simp_all +decide [ Function.Bijective ];
        · exact fun a b => mul_add _ _ _;
        · have h_mul_k_aut : IsUnit (k : ZMod p) := by
            rw [ ZMod.isUnit_iff_coprime ] ; aesop;
          exact ⟨ fun x y hxy => by simpa [ h_mul_k_aut.mul_right_inj ] using hxy, fun x => by obtain ⟨ y, hy ⟩ := h_mul_k_aut.exists_right_inv; exact ⟨ y * x, by linear_combination' hy * x ⟩ ⟩;
      exact ⟨ AddEquiv.ofBijective h_mul_k_aut.choose h_mul_k_aut.choose_spec.2, h_mul_k_aut.choose_spec.1 ⟩;
    exact ⟨ h_mul_k_aut.choose.toMultiplicative, by simpa using congr_arg Multiplicative.ofAdd h_mul_k_aut.choose_spec ⟩;
  -- By definition of `fg`, we have `φ₁ = φ₂ ∘ fg`.
  have h_phi_eq : φ₁ = φ₂.comp fg.toMonoidHom := by
    ext x;
    obtain ⟨ n, rfl ⟩ := ( show ∃ n : ℤ, x = ( Multiplicative.ofAdd 1 : CyclicGroup p ) ^ n from by
                            have h_gen : ∀ x : CyclicGroup p, ∃ n : ℤ, x = (Multiplicative.ofAdd 1 : CyclicGroup p) ^ n := by
                              intro x
                              have h_gen : ∃ n : ℤ, x = (Multiplicative.ofAdd 1 : CyclicGroup p) ^ n := by
                                have h_gen : ∀ x : ZMod p, ∃ n : ℤ, x = n • (1 : ZMod p) := by
                                  exact fun x => ⟨ x.val, by simp +decide ⟩
                                convert h_gen (Multiplicative.toAdd x) using 1
                              exact h_gen;
                            exact h_gen x );
    simp_all +decide [ zpow_mul ];
  refine' ⟨ _ ⟩;
  refine' { Equiv.ofBijective ( fun x => ⟨ x.1, fg x.2 ⟩ ) ⟨ fun x y hxy => _, fun x => _ ⟩ with .. } <;> simp_all +decide [ funext_iff, SemidirectProduct.ext_iff ];
  exact ⟨ ⟨ x.1, fg.symm x.2 ⟩, rfl, by simp +decide ⟩

end Uniqueness

section MainTheorem

/-
Case B2 odd: a non-abelian group of order p³ with elements of order p² and p
    is isomorphic to C_{p²} ⋊[cpSqAction p] C_p
-/
theorem case_B2_odd_isom (hp_odd : p ≠ 2)
    (a b : G) (ha : orderOf a = p ^ 2) (hb : orderOf b = p)
    (hab : a * b ≠ b * a) (hcard : Nat.card G = p ^ 3) :
    Nonempty (G ≃* CyclicGroup (p ^ 2) ⋊[cpSqAction p] CyclicGroup p) := by
  -- Set up the semidirect product decomposition.
  set H := Subgroup.zpowers a
  set K := Subgroup.zpowers b
  have hH_normal : H.Normal :=
    zpowers_normal_of_order_p_sq a ha hcard
  have hH_complement : H.IsComplement' K :=
    zpowers_complement' a b ha hb hab hcard
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : H ≃* CyclicGroup (p ^ 2), True := by
    have hH_card : Nat.card H = p ^ 2 := by
      rw [ Nat.card_zpowers, ha ];
    have hH_iso : H ≃* Multiplicative (ZMod (Nat.card H)) := by
      convert ( MulEquiv.symm <| zmodCyclicMulEquiv <| show IsCyclic H from ?_ ) using 1;
      exact ⟨ ⟨ a, Subgroup.mem_zpowers a ⟩, fun x => by obtain ⟨ n, hn ⟩ := Subgroup.mem_zpowers_iff.mp x.2; exact ⟨ n, Subtype.ext hn ⟩ ⟩;
    rw [ hH_card ] at hH_iso;
    exact ⟨ hH_iso.trans ( MulEquiv.refl _ ), trivial ⟩
  obtain ⟨e₂, he₂⟩ : ∃ e₂ : K ≃* CyclicGroup p, True := by
    have hK_iso : Nonempty (K ≃* Multiplicative (ZMod (Nat.card K))) := by
      refine' ⟨ _ ⟩;
      convert ( MulEquiv.symm <| zmodCyclicMulEquiv <| show IsCyclic K from inferInstance ) using 1;
    have hK_card : Nat.card K = p := by
      rw [ Nat.card_zpowers, hb ];
    exact ⟨ hK_iso.some.trans ( by rw [ hK_card ] ; exact MulEquiv.refl _ ), trivial ⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : CyclicGroup p →* MulAut (CyclicGroup (p ^ 2)), Nonempty (G ≃* CyclicGroup (p ^ 2) ⋊[ψ] CyclicGroup p) := by
    obtain ⟨ψ, hψ⟩ : ∃ ψ : K →* MulAut H, Nonempty (G ≃* H ⋊[ψ] K) := by
      exact ⟨ _, ⟨ ( SemidirectProduct.mulEquivSubgroup hH_complement ).symm ⟩ ⟩;
    refine' ⟨ _, _ ⟩;
    refine' MonoidHom.comp ( MulEquiv.toMonoidHom ( MulAut.congr e₁ ) ) ( MonoidHom.comp ψ ( e₂.symm.toMonoidHom ) );
    refine' ⟨ hψ.some.trans _ ⟩;
    refine' { Equiv.ofBijective ( fun x => ⟨ e₁ x.1, e₂ x.2 ⟩ ) ⟨ fun x y hxy => _, fun x => _ ⟩ with .. } <;> simp_all +decide [ Function.Injective, Function.Surjective ];
    · simp_all +decide [ SemidirectProduct.ext_iff ];
    · refine' ⟨ ⟨ e₁.symm x.1, e₂.symm x.2 ⟩, _ ⟩ ; simp +decide [ SemidirectProduct.ext_iff ];
    · simp +decide [ SemidirectProduct.ext_iff ];
  -- Since ψ is non-trivial, we can apply the uniqueness lemma to conclude that ψ is isomorphic to cpSqAction p.
  have hψ_nontrivial : ψ ≠ 1 := by
    obtain ⟨ f ⟩ := hψ;
    intro hψ_trivial
    have hG_abelian : ∀ x y : G, x * y = y * x := by
      intro x y; rw [ ← f.injective.eq_iff ] ; simp +decide [ hψ_trivial ] ;
      simp +decide [ hψ_trivial, SemidirectProduct.ext_iff ];
      exact ⟨ mul_comm _ _, mul_comm _ _ ⟩;
    exact hab ( hG_abelian a b )
  have hψ_iso : Nonempty (CyclicGroup (p ^ 2) ⋊[ψ] CyclicGroup p ≃* CyclicGroup (p ^ 2) ⋊[cpSqAction p] CyclicGroup p) := by
    apply semidirect_unique_of_nontrivial hp_odd ψ (cpSqAction p) hψ_nontrivial (by
    intro h;
    replace h := congr_arg ( fun f => f ( Multiplicative.ofAdd 1 ) ) h ; simp_all +decide [ cpSqAction ];
    have h_order : orderOf ((Classical.choice (aut_of_cyclic_p2 (h_p_prime := hp))).symm (Multiplicative.ofAdd 1) ^ (p - 1)) = p := by
      have h_order : orderOf (Multiplicative.ofAdd 1 : CyclicGroup (p * (p - 1))) = p * (p - 1) := by
        simp +decide [ orderOf_eq_iff ];
      rw [ orderOf_pow ] ; simp +decide [ h_order, hp.1.ne_zero ];
      rw [ Nat.mul_div_cancel _ ( Nat.sub_pos_of_lt hp.1.one_lt ) ];
    simp_all +decide [ cyclicHom ];
    simp_all +decide [ ZMod.lift ];
    simp_all +decide [ AddMonoidHom.liftOfRightInverse ];
    simp_all +decide [ AddMonoidHom.liftOfRightInverseAux ];
    simp_all +decide [ AddMonoidHom.toMultiplicativeLeft ];
    rcases p with ( _ | _ | p ) <;> simp_all +decide [ ZMod.cast, ZMod.val ])
  exact hψ.elim fun e => hψ_iso.elim fun e' => ⟨e.trans e'⟩

end MainTheorem
