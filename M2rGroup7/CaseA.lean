import Mathlib

/-!
# Case A: Both generators have order 2 → D₄

We prove that a non-abelian group G of order 8 with two non-commuting
elements of order 2 is isomorphic to DihedralGroup 4.
-/

variable {G : Type*} [Group G]

/-- If a² = 1, b² = 1, then ba = (ab)⁻¹. -/
lemma ba_eq_inv_ab {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    b * a = (a * b)⁻¹ := by
  simp_all +decide [ mul_eq_one_iff_inv_eq, sq ]

/-- If a² = 1, b² = 1, and ab ≠ ba, then (ab)² ≠ 1 -/
lemma ab_sq_ne_one {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : a * b ≠ b * a) : (a * b) ^ 2 ≠ 1 := by
  intro h
  have h_eq : a * b = b * a := by
    simp_all +decide [ sq, mul_eq_one_iff_inv_eq ]
  contradiction

/-- Conjugation: a * (ab)^k * a = (ab)⁻¹ ^ k when a² = 1, b² = 1 -/
lemma conj_ab_pow {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (k : ℕ) : a * (a * b) ^ k * a = (a * b)⁻¹ ^ k := by
  induction k <;> simp_all +decide [ pow_succ', mul_assoc ];
  simp_all +decide [ ← mul_assoc, ← ‹_› ];
  rw [ inv_eq_of_mul_eq_one_right hb ]

/-
If a² = 1, b² = 1, ab ≠ ba, and |G| = 8, then orderOf (a*b) = 4
-/
lemma orderOf_ab_eq_four {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : a * b ≠ b * a) (hcard : Nat.card G = 8) : orderOf (a * b) = 4 := by
  -- Since |G| = 8, orderOf(ab) | 8 (by orderOf_dvd_natCard). The divisors of 8 are 1, 2, 4, 8.
  have h_div : orderOf (a * b) ∣ 8 := by
    convert Subgroup.card_subgroup_dvd_card ( Subgroup.zpowers ( a * b ) ) using 1;
    · rw [ Nat.card_zpowers ];
    · exact hcard.symm;
  have := Nat.le_of_dvd ( by decide ) h_div; interval_cases _ : orderOf ( a * b ) <;> simp_all +decide;
  · simp_all +decide [ mul_eq_one_iff_eq_inv ];
  · exact ab_sq_ne_one ha hb hab ( by rw [ ← ‹orderOf ( a * b ) = 2›, pow_orderOf_eq_one ] );
  · -- If orderOf (a * b) = 8, then G is cyclic (isCyclic_of_card_le_orderOf), hence commutative, contradicting hab.
    have h_cyclic : IsCyclic G := by
      have h_cyclic : Nat.card G ≤ orderOf (a * b) := by
        linarith;
      apply_rules [ isCyclic_of_card_le_orderOf ];
      exact Nat.finite_of_card_ne_zero ( hcard.symm ▸ by decide );
    exact hab ( by obtain ⟨ g, hg ⟩ := h_cyclic; obtain ⟨ m, rfl ⟩ := hg a; obtain ⟨ n, rfl ⟩ := hg b; group )

/-
g^(val(i+j)) = g^(val i) * g^(val j) when orderOf g = 4
-/
lemma pow_val_add (g : G) (hord : orderOf g = 4) (i j : ZMod 4) :
    g ^ (i + j).val = g ^ i.val * g ^ j.val := by
  -- Since $i$ and $j$ are elements of $ZMod 4$, their values are between $0$ and $3$. The sum $i + j$ is also an element of $ZMod 4$, so its value is $(i.val + j.val) \mod 4$.
  have h_mod : ((i + j).val : ℕ) % 4 = (i.val + j.val) % 4 := by
    decide +revert;
  rw [ ← pow_add, ← Nat.mod_add_div ( ( i + j ).val ) 4, h_mod ];
  simp +decide [ pow_add, pow_mul, hord.symm, pow_orderOf_eq_one ]

/-
g^(val(j-i)) = (g⁻¹)^(val i) * g^(val j) when orderOf g = 4
-/
lemma pow_val_sub (g : G) (hord : orderOf g = 4) (i j : ZMod 4) :
    g ^ (j - i).val = (g⁻¹) ^ i.val * g ^ j.val := by
  -- Since $g$ has order 4, we can rewrite $g⁻¹^i.val$ as $g^(4 - i.val)$.
  have h_inv : g⁻¹ ^ i.val = g ^ (4 - i.val) := by
    simp +decide [ ← hord, pow_succ, pow_mul, inv_mul_eq_iff_eq_mul ];
    rw [ inv_eq_of_mul_eq_one_right ];
    rw [ ← pow_add, add_tsub_cancel_of_le ( show i.val ≤ orderOf g from hord.symm ▸ by fin_cases i <;> decide ), pow_orderOf_eq_one ];
  have h_exp : g ^ (j - i).val = g ^ ((4 - i.val + j.val) % 4) := by
    all_goals rfl;
  rw [ h_exp, h_inv, ← pow_add ];
  simp +decide [ ← hord ]

/-- The function DihedralGroup 4 → G sending r(i) ↦ (ab)^i.val and sr(i) ↦ a*(ab)^i.val -/
noncomputable def dihedralToG (a b : G) : DihedralGroup 4 → G
  | DihedralGroup.r i => (a * b) ^ i.val
  | DihedralGroup.sr i => a * (a * b) ^ i.val

/-
The map dihedralToG is a group homomorphism when a² = 1, b² = 1, and ab ≠ ba
-/
lemma dihedralToG_mul (a b : G) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : a * b ≠ b * a) (hcard : Nat.card G = 8) (x y : DihedralGroup 4) :
    dihedralToG a b (x * y) = dihedralToG a b x * dihedralToG a b y := by
  rcases x with ⟨ i ⟩ | ⟨ i ⟩ <;> rcases y with ⟨ j ⟩ | ⟨ j ⟩ <;> simp +decide [ dihedralToG ];
  · have hord : orderOf ( a * b ) = 4 := orderOf_ab_eq_four ha hb hab hcard; exact pow_val_add ( a * b ) hord i j;
  · have h_pow_val_sub : (a * b) ^ (j - i).val = (a * b)⁻¹ ^ i.val * (a * b) ^ j.val := by
      convert pow_val_sub ( a * b ) ( orderOf_ab_eq_four ha hb hab hcard ) i j using 1;
    have h_conj_ab_pow : a * (a * b) ^ i.val * a = (a * b)⁻¹ ^ i.val := by
      exact conj_ab_pow ha hb i.val;
    simp_all +decide [ mul_assoc, pow_succ ];
    simp +decide [ ← mul_assoc, ← h_conj_ab_pow ];
    exact ha;
  · simp +decide [ mul_assoc, pow_val_add ( a * b ) ( orderOf_ab_eq_four ha hb hab hcard ) ];
  · convert pow_val_sub ( a * b ) _ i j using 1;
    · have := conj_ab_pow ha hb i.val; simp_all +decide [ ← mul_assoc, pow_succ ] ;
    · exact orderOf_ab_eq_four ha hb hab hcard

/-- dihedralToG sends 1 to 1 -/
lemma dihedralToG_one (a b : G) : dihedralToG a b 1 = 1 := by
  change dihedralToG a b (DihedralGroup.r 0) = 1
  simp [dihedralToG]

/-- The MonoidHom from DihedralGroup 4 to G -/
noncomputable def dihedralHomToG (a b : G) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : a * b ≠ b * a) (hcard : Nat.card G = 8) : DihedralGroup 4 →* G where
  toFun := dihedralToG a b
  map_one' := dihedralToG_one a b
  map_mul' := dihedralToG_mul a b ha hb hab hcard

/-
The map is injective
-/
lemma dihedralToG_injective (a b : G) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : a * b ≠ b * a) (hcard : Nat.card G = 8) :
    Function.Injective (dihedralToG a b) := by
  -- To show injectivity, we consider the kernel of the homomorphism.
  have hkernel : MonoidHom.ker (dihedralHomToG a b ha hb hab hcard) = ⊥ := by
    refine' eq_bot_iff.mpr fun x hx => _;
    rcases x with ( _ | _ | _ | _ | _ | _ | _ | _ | x ) <;> norm_num [ dihedralHomToG ] at hx ⊢;
    all_goals norm_cast at *;
    · rename_i i; fin_cases i <;> simp_all +decide [ dihedralToG ] ;
      · simp_all +decide [ ZMod.val ];
        simp_all +decide [ sq, mul_eq_one_iff_inv_eq ];
        simp_all +decide [ inv_eq_iff_mul_eq_one ];
      · exact absurd hx ( by erw [ pow_two ] ; exact fun h => hab <| by simp_all +decide [ sq, mul_eq_one_iff_inv_eq ] );
      · have := orderOf_ab_eq_four ha hb hab hcard; simp_all +decide [ pow_succ ] ;
        exact absurd ( orderOf_dvd_iff_pow_eq_one.mpr hx ) ( by simp +decide [ this ] );
    · simp_all +decide [ dihedralToG ];
      simp_all [ZMod.val]
    · simp_all +decide [ dihedralToG ];
      simp_all +decide [ ZMod.val ];
      simp_all +decide [ ← mul_assoc, sq ];
    · simp_all +decide [ dihedralToG ];
      simp_all +decide [ ZMod.val, pow_succ' ];
      grind +splitImp;
    · simp_all +decide [ dihedralToG ];
      simp_all +decide [ ZMod.val, pow_succ, mul_assoc ];
      grind +qlia;
  convert ( MonoidHom.ker_eq_bot_iff _ ).mp hkernel using 1

/-- Main theorem: G ≅ DihedralGroup 4 -/
theorem case_A_isom (a b : G) (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : a * b ≠ b * a) (hcard : Nat.card G = 8) :
    Nonempty (G ≃* DihedralGroup 4) := by
  have ha2 : a ^ 2 = 1 := by rw [← orderOf_dvd_iff_pow_eq_one]; rw [ha]
  have hb2 : b ^ 2 = 1 := by rw [← orderOf_dvd_iff_pow_eq_one]; rw [hb]
  have hinj := dihedralToG_injective a b ha2 hb2 hab hcard
  have hfin_G : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hcard_D4 : Nat.card (DihedralGroup 4) = 8 := DihedralGroup.nat_card
  have hsurj : Function.Surjective (dihedralToG a b) := by
    haveI : Fintype (DihedralGroup 4) := Fintype.ofFinite _
    haveI : Fintype G := Fintype.ofFinite G
    have e : DihedralGroup 4 ≃ G :=
      Fintype.equivOfCardEq (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
        hcard_D4, hcard])
    exact hinj.surjective_of_finite e
  exact ⟨(MulEquiv.ofBijective (dihedralHomToG a b ha2 hb2 hab hcard) ⟨hinj, hsurj⟩).symm⟩
