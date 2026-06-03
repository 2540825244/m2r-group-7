import Mathlib
import «M2rGroup7».UT3
import «M2rGroup7».SmallGroupsLibrary

set_option maxHeartbeats 800000

/-!
# Case A (odd prime): Both generators have order p → UT₃(p)

We prove that a non-abelian group G of order p³ (p an odd prime) with two
non-commuting elements of order p is isomorphic to UT₃(p).
-/

open scoped commutatorElement

variable {G : Type*} [Group G] (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ## Part 1: Center of G has order p -/

/-
A non-abelian group of order p³ has center of order p.
-/
lemma center_card_of_prime_cube (hcard : Nat.card G = p ^ 3)
    (hnonab : ∃ a b : G, a * b ≠ b * a) :
    Nat.card (Subgroup.center G) = p := by
  obtain ⟨a, b, hne⟩ : ∃ a b : G, a * b ≠ b * a := hnonab
  have h_center_nontrivial : Nat.card (Subgroup.center G) ≠ 1 := by
    have h_center_nontrivial : IsPGroup p G := by
      exact?;
    convert h_center_nontrivial.bot_lt_center.ne' using 1;
    · simp +decide [ Subgroup.eq_bot_iff_forall ];
    · exact ⟨ a, b, by aesop ⟩;
    · exact Nat.finite_of_card_ne_zero ( hcard.symm ▸ pow_ne_zero 3 hp.1.ne_zero )
  have h_center_bound : Nat.card (Subgroup.center G) ∣ p^3 := by
    convert Subgroup.card_subgroup_dvd_card ( Subgroup.center G ) using 1 ; aesop ( simp_config := { singlePass := true } ) ;
  have h_center_cases : Nat.card (Subgroup.center G) = p ∨ Nat.card (Subgroup.center G) = p^2 ∨ Nat.card (Subgroup.center G) = p^3 := by
    rw [ Nat.dvd_prime_pow hp.1 ] at h_center_bound;
    rcases h_center_bound with ⟨ k, hk₁, hk₂ ⟩ ; interval_cases k <;> simp_all +decide ;
  have h_center_not_p2_p3 : Nat.card (Subgroup.center G) ≠ p^2 ∧ Nat.card (Subgroup.center G) ≠ p^3 := by
    constructor <;> intro h <;> simp_all +decide [ pow_succ' ];
    · -- If $|Z(G)| = p^2$, then $G/Z(G)$ is cyclic.
      have h_cyclic : IsCyclic (G ⧸ Subgroup.center G) := by
        have h_cyclic : Nat.card (G ⧸ Subgroup.center G) = p := by
          have := Subgroup.card_eq_card_quotient_mul_card_subgroup ( Subgroup.center G );
          nlinarith [ hp.1.two_le ];
        exact isCyclic_of_prime_card h_cyclic;
      -- If $G/Z(G)$ is cyclic, then $G$ is abelian.
      have h_abelian : ∀ g h : G, g * h = h * g := by
        -- If $G/Z(G)$ is cyclic, then there exists some $g \in G$ such that every element of $G$ can be written as $g^k z$ for some $z \in Z(G)$ and integer $k$.
        obtain ⟨g, hg⟩ : ∃ g : G, ∀ x : G, ∃ k : ℤ, ∃ z : ↥(Subgroup.center G), x = g^k * z := by
          obtain ⟨ g, hg ⟩ := h_cyclic.exists_generator;
          obtain ⟨ g, rfl ⟩ := QuotientGroup.mk_surjective g; use g; intro x; obtain ⟨ k, hk ⟩ := hg ( QuotientGroup.mk x ) ; use k; simp_all +decide [ QuotientGroup.eq ] ;
          exact ⟨ ( g ^ k ) ⁻¹ * x, by erw [ QuotientGroup.eq ] at hk; aesop ⟩;
        intro x y; obtain ⟨ k₁, z₁, rfl ⟩ := hg x; obtain ⟨ k₂, z₂, rfl ⟩ := hg y; group; simp +decide [ Subgroup.mem_center_iff.mp z₁.2, Subgroup.mem_center_iff.mp z₂.2 ] ;
        group;
        rw [ Subgroup.mem_center_iff.mp z₁.2 _ ];
      exact hne ( h_abelian a b );
    · have h_center_eq : Subgroup.center G = ⊤ := by
        have h_center_eq_G : Finite G := by
          exact Nat.finite_of_card_ne_zero ( by rw [ hcard ] ; exact mul_ne_zero hp.1.ne_zero ( mul_ne_zero hp.1.ne_zero hp.1.ne_zero ) );
        exact Subgroup.eq_top_of_card_eq _ ( by aesop )
      generalize_proofs at *; simp_all +decide [ Subgroup.mem_center_iff ] ;
      exact hne ( Subgroup.mem_center_iff.mp ( h_center_eq.symm ▸ Subgroup.mem_top _ ) _ )
  aesop

/-! ## Part 2: The commutator z = [a,b] is central -/

/-
In a group of order p³, the commutator of any two elements lies in the center.
-/
lemma commutatorElement_mem_center (hcard : Nat.card G = p ^ 3)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (x y : G) :
    ⁅x, y⁆ ∈ Subgroup.center G := by
  have h_quotient : IsPGroup p (G ⧸ Subgroup.center G) := by
    have h_quotient : Nat.card (G ⧸ Subgroup.center G) = p ^ 2 := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup ( Subgroup.center G );
      have := center_card_of_prime_cube ( p := p ) hcard hnonab; simp_all +decide [ pow_succ, mul_assoc ] ;
      nlinarith [ hp.1.two_le ];
    exact?;
  have h_quotient_abelian : ∀ x y : G ⧸ Subgroup.center G, x * y = y * x := by
    have h_quotient_abelian : Nat.card (G ⧸ Subgroup.center G) = p ^ 2 := by
      have h_center_card : Nat.card (Subgroup.center G) = p := by
        apply center_card_of_prime_cube p hcard hnonab;
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup ( Subgroup.center G );
      nlinarith [ hp.1.two_le ];
    have h_quotient_abelian : IsPGroup p (G ⧸ Subgroup.center G) → Nat.card (G ⧸ Subgroup.center G) = p ^ 2 → ∀ x y : G ⧸ Subgroup.center G, x * y = y * x := by
      exact?;
    exact h_quotient_abelian h_quotient ‹_›;
  simp_all +decide [ ← QuotientGroup.eq_one_iff, commutatorElement_def ]

/-- The commutator z = ⁅a, b⁆ commutes with everything. -/
lemma commutator_central (a b g : G) (hcard : Nat.card G = p ^ 3)
    (hnonab : ∃ x y : G, x * y ≠ y * x) :
    g * ⁅a, b⁆ = ⁅a, b⁆ * g := by
  exact Subgroup.mem_center_iff.mp (commutatorElement_mem_center p hcard hnonab a b) g

/-! ## Part 3: Order of the commutator -/

/-
The commutator of two non-commuting elements in a group of order p³ has order p.
-/
lemma commutator_order (a b : G) (hcard : Nat.card G = p ^ 3)
    (hnonab : ∃ x y : G, x * y ≠ y * x)
    (hab : a * b ≠ b * a) :
    orderOf ⁅a, b⁆ = p := by
  -- Since ⁅a,b⁆ ∈ Z(G) by commutatorElement_mem_center, and Z(G) has order p by center_card_of_prime_cube, orderOf ⁅a,b⁆ divides p (Lagrange).
  have h_divides : orderOf ⁅a, b⁆ ∣ p := by
    have h_center : ⁅a, b⁆ ∈ Subgroup.center G := by
      exact?;
    have h_order_div : orderOf ⁅a, b⁆ ∣ Nat.card (Subgroup.center G) := by
      exact?;
    rwa [ center_card_of_prime_cube p hcard hnonab ] at h_order_div;
  simp_all +decide [ commutatorElement_def, Nat.dvd_prime hp.1 ];
  simp_all +decide [ mul_inv_eq_iff_eq_mul ]

/-! ## Part 4: Commutation relation -/

/-- Key relation: a * b = ⁅a,b⁆ * b * a -/
lemma mul_comm_rel (a b : G) :
    a * b = ⁅a, b⁆ * b * a := by
  simp [commutatorElement_def, mul_assoc]

/-
Commuting b past a: a^m * b = ⁅a,b⁆^m * b * a^m when ⁅a,b⁆ is central.
-/
lemma comm_rearrange_one (a b : G) (m : ℕ)
    (hz : ∀ g : G, g * ⁅a, b⁆ = ⁅a, b⁆ * g) :
    a ^ m * b = ⁅a, b⁆ ^ m * b * a ^ m := by
  induction' m with m ih;
  · simp +decide;
  · simp_all +decide [ mul_assoc, pow_succ ];
    simp +decide [ ← mul_assoc, ← ih, hz ];
    rw [ ← hz ] ; group;

/-
Full commutation: a^m * b^n = ⁅a,b⁆^(m*n) * b^n * a^m when ⁅a,b⁆ is central.
-/
lemma comm_rearrange (a b : G) (m n : ℕ)
    (hz : ∀ g : G, g * ⁅a, b⁆ = ⁅a, b⁆ * g) :
    a ^ m * b ^ n = ⁅a, b⁆ ^ (m * n) * b ^ n * a ^ m := by
  induction' n with n ih;
  · simp +decide;
  · simp +decide only [pow_succ, ← mul_assoc, ih];
    have h_comm : a ^ m * b = ⁅a, b⁆ ^ m * b * a ^ m := by
      convert comm_rearrange_one a b m hz using 1;
    simp_all +decide [ mul_assoc, pow_add, pow_mul ];
    -- Since ⁅a, b⁆ is central, we can commute it with any element.
    have h_comm : ∀ g : G, g * ⁅a, b⁆ ^ m = ⁅a, b⁆ ^ m * g := by
      exact fun g => Nat.recOn m ( by simp +decide ) fun n ihn => by rw [ pow_succ', ← mul_assoc, hz, mul_assoc, ihn, mul_assoc ] ;
    simp +decide only [← mul_assoc, h_comm]

/-! ## Part 5: ZMod power lemmas -/

/-
g^(i+j).val = g^i.val * g^j.val when orderOf g = p
-/
lemma pow_zmod_val_add (g : G) (hord : orderOf g = p) (i j : ZMod p) :
    g ^ (i + j).val = g ^ i.val * g ^ j.val := by
  rw [ ← pow_add, ZMod.val_add ];
  rw [ ← Nat.mod_add_div ( i.val + j.val ) p, pow_add, pow_mul ] ; aesop

/-
g^(i*j).val = (g^i.val)^j.val when orderOf g = p
-/
lemma pow_zmod_val_mul (g : G) (hord : orderOf g = p) (i j : ZMod p) :
    g ^ (i * j).val = (g ^ i.val) ^ j.val := by
  rw [ ← pow_mul, mul_comm, ZMod.val_mul ];
  rw [ mul_comm, ← Nat.mod_add_div ( i.val * j.val ) p ] ; simp +decide [ pow_add, pow_mul, hord.symm ] ;

/-! ## Part 6: The isomorphism UT₃(p) → G -/

/-- The map UT₃(p) → G sending (α, β, γ) ↦ b^γ * a^α * z^β
    where z = ⁅a,b⁆. -/
noncomputable def ut3ToG (a b : G) : UT3 p → G :=
  fun x => b ^ x.c.val * a ^ x.a.val * ⁅a, b⁆ ^ x.b.val

/-- ut3ToG sends 1 to 1 -/
lemma ut3ToG_one (a b : G) : ut3ToG p a b (1 : UT3 p) = 1 := by
  simp [ut3ToG]

/-
ut3ToG is multiplicative
-/
lemma ut3ToG_mul (a b : G) (hcard : Nat.card G = p ^ 3)
    (hnonab : ∃ x y : G, x * y ≠ y * x)
    (hab : a * b ≠ b * a)
    (ha : orderOf a = p) (hb : orderOf b = p) (x y : UT3 p) :
    ut3ToG p a b (x * y) = ut3ToG p a b x * ut3ToG p a b y := by
  -- By commutativity of the commutator with $a$ and $b$, we can rearrange the terms in the product.
  have h_comm : ∀ g : G, g * ⁅a, b⁆ = ⁅a, b⁆ * g := by
    exact?;
  -- Use the commutativity of the commutator with $a$ and $b$ to rearrange the terms in the product.
  have h_rearrange : b ^ x.c.val * a ^ x.a.val * b ^ y.c.val * a ^ y.a.val = b ^ x.c.val * b ^ y.c.val * a ^ x.a.val * a ^ y.a.val * ⁅a, b⁆ ^ (x.a.val * y.c.val) := by
    have h_rearrange : ∀ m n : ℕ, a ^ m * b ^ n = ⁅a, b⁆ ^ (m * n) * b ^ n * a ^ m := by
      exact?;
    simp +decide [ mul_assoc, h_rearrange ];
    induction' x.a.val * y.c.val with n ih <;> simp +decide [ *, pow_succ, mul_assoc ];
    simp +decide only [← mul_assoc, h_comm];
  convert congr_arg ( fun g : G => g * ⁅a, b⁆ ^ ( x.b.val + y.b.val ) ) h_rearrange.symm using 1;
  · simp +decide [ ut3ToG, mul_assoc ];
    simp +decide [ ← mul_assoc, ← pow_add, pow_zmod_val_add, pow_zmod_val_mul, ha, hb ];
    rw [ add_comm, ZMod.val_add ];
    rw [ ← Nat.mod_add_div ( x.a.val * y.c.val + ( x.b.val + y.b.val ) ) p ] ; simp +decide [ pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod ] ;
    rw [ show ⁅a, b⁆ ^ p = 1 from by rw [ ← commutator_order p a b hcard hnonab hab, pow_orderOf_eq_one ] ] ; simp +decide [ pow_add, pow_mul ];
    simp +decide [ ZMod.val_add, ZMod.val_mul ];
  · simp +decide [ mul_assoc, pow_add, ut3ToG ];
    induction' x.b.val with n ih <;> simp +decide [ *, pow_succ', mul_assoc ];
    simp +decide only [← mul_assoc, h_comm]

/-- The MonoidHom from UT₃(p) to G -/
noncomputable def ut3HomToG (a b : G) (hcard : Nat.card G = p ^ 3)
    (hnonab : ∃ x y : G, x * y ≠ y * x)
    (hab : a * b ≠ b * a)
    (ha : orderOf a = p) (hb : orderOf b = p) : UT3 p →* G where
  toFun := ut3ToG p a b
  map_one' := ut3ToG_one p a b
  map_mul' := ut3ToG_mul p a b hcard hnonab hab ha hb

/-! ## Part 7: Injectivity -/

/-
The map ut3ToG is injective
-/
lemma ut3ToG_injective (a b : G) (hcard : Nat.card G = p ^ 3)
    (hnonab : ∃ x y : G, x * y ≠ y * x)
    (hab : a * b ≠ b * a)
    (ha : orderOf a = p) (hb : orderOf b = p) :
    Function.Injective (ut3ToG p a b) := by
  -- Since $ut3ToG$ is a group homomorphism from $UT3(p)$ of size $p^3$ to $G$ of size $p^3$, it suffices to show that the kernel is trivial.
  have h_kernel_trivial : ∀ (x : UT3 p), ut3ToG p a b x = 1 → x = 1 := by
    intro x hx
    have h_b : b ^ x.c.val * a ^ x.a.val * ⁅a, b⁆ ^ x.b.val = 1 := by
      exact hx;
    -- If $x.c.val \neq 0$, then $b^{x.c.val} = a^{-x.a.val} * z^{-x.b.val}$, which implies $b \in \langle a, z \rangle$.
    by_cases hc : x.c.val ≠ 0;
    · have h_b_in_subgroup : b ∈ Subgroup.closure {a, ⁅a, b⁆} := by
        have h_b_in_subgroup : b ^ x.c.val ∈ Subgroup.closure {a, ⁅a, b⁆} := by
          have h_b_in_subgroup : b ^ x.c.val = (a ^ x.a.val * ⁅a, b⁆ ^ x.b.val)⁻¹ := by
            exact eq_inv_of_mul_eq_one_left ( by simpa [ mul_assoc ] using h_b );
          exact h_b_in_subgroup.symm ▸ Subgroup.inv_mem _ ( Subgroup.mul_mem _ ( Subgroup.pow_mem _ ( Subgroup.subset_closure ( Set.mem_insert _ _ ) ) _ ) ( Subgroup.pow_mem _ ( Subgroup.subset_closure ( Set.mem_insert_of_mem _ ( Set.mem_singleton _ ) ) ) _ ) );
        -- Since $x.c.val \neq 0$, we can find an integer $k$ such that $k * x.c.val \equiv 1 \pmod{p}$.
        obtain ⟨k, hk⟩ : ∃ k : ℕ, k * x.c.val ≡ 1 [MOD p] := by
          have := Nat.exists_mul_mod_eq_one_of_coprime ( show Nat.Coprime ( x.c.val ) p from Nat.Coprime.symm <| hp.1.coprime_iff_not_dvd.mpr <| by rw [ Nat.dvd_iff_mod_eq_zero ] ; exact fun h => hc <| Nat.eq_zero_of_dvd_of_lt ( Nat.dvd_of_mod_eq_zero h ) <| ZMod.val_lt _ );
          exact Exists.elim ( this hp.1.one_lt ) fun k hk => ⟨ k, by rw [ mul_comm, ← hk.2, Nat.ModEq, Nat.mod_mod ] ⟩;
        convert Subgroup.pow_mem _ h_b_in_subgroup k using 1;
        rw [ ← pow_mul, mul_comm, ← Nat.mod_add_div ( k * x.c.val ) p, hk ] ; simp +decide [ pow_add, pow_mul, hb.symm ];
      -- Since $a$ and $⁅a, b⁆$ commute, the subgroup generated by $a$ and $⁅a, b⁆$ is abelian.
      have h_abelian : ∀ x y : G, x ∈ Subgroup.closure {a, ⁅a, b⁆} → y ∈ Subgroup.closure {a, ⁅a, b⁆} → x * y = y * x := by
        have h_comm : a * ⁅a, b⁆ = ⁅a, b⁆ * a := by
          exact commutator_central p a b a hcard hnonab
        intro x y hx hy; induction hx using Subgroup.closure_induction ; induction hy using Subgroup.closure_induction ; aesop;
        all_goals simp_all +decide [ mul_assoc, eq_inv_mul_iff_mul_eq ];
        · grind;
        · simp_all +decide [ ← mul_assoc ];
          simp_all +decide [ mul_inv_eq_iff_eq_mul ];
        · simp +decide only [← mul_assoc, *];
        · rw [ inv_mul_eq_iff_eq_mul, ← mul_assoc, ‹ ( _ : G ) * y = y * _ ›, mul_assoc, mul_inv_cancel, mul_one ];
      exact False.elim ( hab ( h_abelian _ _ ( Subgroup.subset_closure ( Set.mem_insert _ _ ) ) h_b_in_subgroup ) );
    · -- If $x.a.val \neq 0$, then $a^{x.a.val} = z^{-x.b.val}$, which implies $a \in \langle z \rangle$.
      by_cases ha : x.a.val ≠ 0;
      · have h_a : a ^ x.a.val = ⁅a, b⁆ ^ (-x.b.val : ℤ) := by
          simp_all +decide [ mul_eq_one_iff_eq_inv ];
          rw [ ← zpow_natCast, ZMod.cast_eq_val ];
        have h_a_central : a ^ x.a.val ∈ Subgroup.center G := by
          exact h_a.symm ▸ Subgroup.zpow_mem _ ( commutatorElement_mem_center p hcard hnonab a b ) _;
        have h_a_central : a ∈ Subgroup.center G := by
          have h_a_central : ∃ k : ℕ, k * x.a.val ≡ 1 [MOD p] := by
            have := Nat.exists_mul_mod_eq_one_of_coprime ( show Nat.Coprime ( x.a.val ) p from Nat.Coprime.symm <| hp.1.coprime_iff_not_dvd.mpr <| Nat.not_dvd_of_pos_of_lt ( Nat.pos_of_ne_zero ha ) <| ZMod.val_lt _ );
            exact Exists.elim ( this hp.1.one_lt ) fun k hk => ⟨ k, by rw [ mul_comm, ← hk.2, Nat.ModEq, Nat.mod_mod ] ⟩;
          obtain ⟨ k, hk ⟩ := h_a_central;
          have h_a_central : a ^ (k * x.a.val) = a := by
            rw [ ← Nat.mod_add_div ( k * x.a.val ) p, hk ];
            simp +decide [ pow_add, pow_mul, ‹orderOf a = p›.symm, pow_orderOf_eq_one ];
          rw [ ← h_a_central, pow_mul' ];
          exact Subgroup.pow_mem _ ‹_› _;
        exact False.elim ( hab ( by rw [ Subgroup.mem_center_iff.mp h_a_central b ] ) );
      · -- If $x.b.val \neq 0$, then $z^{x.b.val} = 1$, which implies $x.b.val = 0$.
        have hb : x.b.val = 0 := by
          have hb : ⁅a, b⁆ ^ x.b.val = 1 := by
            aesop;
          have := orderOf_dvd_iff_pow_eq_one.mpr hb;
          rw [ commutator_order p a b hcard hnonab hab ] at this;
          exact Nat.eq_zero_of_dvd_of_lt this ( ZMod.val_lt _ );
        cases x ; aesop;
  intro x y hxy;
  have := h_kernel_trivial ( x * y⁻¹ ) ?_;
  · simpa using eq_inv_of_mul_eq_one_left this;
  · have := ut3ToG_mul p a b hcard hnonab hab ha hb x y⁻¹;
    have := ut3ToG_mul p a b hcard hnonab hab ha hb y y⁻¹; simp_all +decide ;
    exact this ▸ ut3ToG_one p a b

/-! ## Part 8: Main theorem -/

/-- Case A (odd prime): A non-abelian group of order p³ with two non-commuting
    elements of order p is isomorphic to UT₃(p). -/
theorem case_A_odd_isom (a b : G)
    (ha : orderOf a = p) (hb : orderOf b = p)
    (hab : a * b ≠ b * a) (hcard : Nat.card G = p ^ 3) :
    Nonempty (G ≃* UT3 p) := by
  have hnonab : ∃ x y : G, x * y ≠ y * x := ⟨a, b, hab⟩
  have hinj := ut3ToG_injective p a b hcard hnonab hab ha hb
  have hfin_G : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 (Nat.Prime.ne_zero hp.out))
  have hcard_UT3 : Nat.card (UT3 p) = p ^ 3 := UT3.card_eq
  have hsurj : Function.Surjective (ut3ToG p a b) := by
    haveI : Fintype G := Fintype.ofFinite G
    have e : UT3 p ≃ G :=
      Fintype.equivOfCardEq (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
        hcard_UT3, hcard])
    exact hinj.surjective_of_finite e
  exact ⟨(MulEquiv.ofBijective
    (ut3HomToG p a b hcard hnonab hab ha hb) ⟨hinj, hsurj⟩).symm⟩
