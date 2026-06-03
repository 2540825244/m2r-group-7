import Mathlib
import «M2rGroup7».SmallGroupsLibrary

/-!
# Case B: One generator has order 4, other has order 2 → D₄

We prove that a non-abelian group G of order 8 with a non-commuting pair
where one element has order 4 and the other has order 2 is isomorphic to DihedralGroup 4.
-/

variable {G : Type*} [Group G]

/-
The subgroup ⟨a⟩ is normal in G when orderOf a = 4 and |G| = 8 (index 2).
-/
lemma zpowers_a_normal {a : G} (ha : orderOf a = 4) (hcard : Nat.card G = 8) :
    (Subgroup.zpowers a).Normal := by
      convert Subgroup.normal_of_index_eq_two _;
      have := Subgroup.index_mul_card ( Subgroup.zpowers a );
      rw [ Nat.card_zpowers, ha ] at this ; nlinarith

/-
Key structural lemma: b * a * b⁻¹ = a⁻¹
-/
lemma conj_inv_of_orders {a b : G} (ha : orderOf a = 4) (hb : orderOf b = 2)
    (hab : a * b ≠ b * a) (hcard : Nat.card G = 8) :
    b * a * b⁻¹ = a⁻¹ := by
      -- From normality, b * a * b⁻¹ ∈ ⟨a⟩, so ∃ k, b * a * b⁻¹ = a ^ k.
      obtain ⟨k, hk⟩ : ∃ k : ℤ, b * a * b⁻¹ = a ^ k := by
        have h_normal : Subgroup.Normal (Subgroup.zpowers a) := by
          apply zpowers_a_normal ha hcard
        generalize_proofs at *; (
        simpa [ eq_comm ] using Subgroup.mem_zpowers_iff.mp ( h_normal.conj_mem _ ( Subgroup.mem_zpowers a ) b ))
      generalize_proofs at *; (
      -- Since $b * a * b⁻¹ = a ^ k$, we know that $k$ must be either $1$ or $3$ (since $a$ has order $4$).
      have hk_cases : k % 4 = 1 ∨ k % 4 = 3 := by
        -- Since $a$ has order 4, we know that $a^{k^2 - 1} = 1$, which implies $4 \mid (k^2 - 1)$.
        have h_div : 4 ∣ (k^2 - 1) := by
          have h_exp : a ^ (k ^ 2) = a := by
            have h_order : b * (b * a * b⁻¹) * b⁻¹ = a := by
              simp +decide [ mul_assoc ];
              simp +decide [ ← mul_assoc, ← pow_two, ← hb, pow_orderOf_eq_one ];
            simp_all +decide [ sq, mul_assoc, zpow_mul ];
            simp_all +decide [ ← mul_assoc, ← hk ]
          generalize_proofs at *; (
          have h_div : a ^ (k ^ 2 - 1) = 1 := by
            rw [ zpow_sub_one ] ; aesop;
          generalize_proofs at *; (
          have := orderOf_dvd_iff_zpow_eq_one.mpr h_div; simp_all +decide ;))
        generalize_proofs at *; (
        obtain ⟨ m, hm ⟩ := h_div; replace hm := congr_arg ( · % 4 ) hm; norm_num [ sq, Int.add_emod, Int.sub_emod, Int.mul_emod ] at hm; have := Int.emod_nonneg k four_pos.ne'; have := Int.emod_lt_of_pos k four_pos; interval_cases k % 4 <;> trivial;);
      rcases hk_cases with ( hk_cases | hk_cases ) <;> rw [ ← Int.emod_add_mul_ediv k 4, hk_cases ] at hk <;> simp_all +decide [ zpow_add, zpow_mul ];
      · simp_all +decide [ mul_inv_eq_iff_eq_mul, zpow_ofNat, orderOf_eq_iff ];
      · norm_cast ; simp_all +decide [ pow_succ, orderOf_eq_iff ];
        exact eq_inv_of_mul_eq_one_left ha.1)

/-
Conjugation generalizes to powers: b * a^k * b = a⁻¹ ^ k
-/
lemma conj_pow_inv {a b : G} (h : b * a * b⁻¹ = a⁻¹) (hb2 : b ^ 2 = 1)
    (k : ℕ) : b * a ^ k * b = a⁻¹ ^ k := by
      induction k <;> simp_all +decide [ pow_succ', mul_assoc ];
      simp +decide [ ← mul_assoc, ← h, ← ‹b * ( a ^ _ * b ) = ( a ^ _ ) ⁻¹› ]

/-
g^(val(i+j)) = g^(val i) * g^(val j) when orderOf g = 4
-/
lemma pow_val_add_4 (g : G) (hord : orderOf g = 4) (i j : ZMod 4) :
    g ^ (i + j).val = g ^ i.val * g ^ j.val := by
      have h_exp : ∀ k : ℕ, g^k = g^(k % 4) := by
        exact fun k => by rw [ ← hord, pow_mod_orderOf ] ;
      rw [ ← pow_add, h_exp, h_exp ] ; norm_num [ Nat.add_mod ] ;
      fin_cases i <;> fin_cases j <;> simp +decide [ h_exp ];
      all_goals rfl;

/-
g^(val(j-i)) = (g⁻¹)^(val i) * g^(val j) when orderOf g = 4
-/
lemma pow_val_sub_4 (g : G) (hord : orderOf g = 4) (i j : ZMod 4) :
    g ^ (j - i).val = (g⁻¹) ^ i.val * g ^ j.val := by
      -- Since $j - i = (j - i).val$, we can rewrite the exponentiation.
      have h_exp : g ^ j.val = (g ^ i.val) * (g ^ (j - i).val) := by
        convert pow_val_add_4 g hord i ( j - i ) using 1;
        simp +decide;
      simp +decide [ h_exp ]

/-- The function DihedralGroup 4 → G sending r(i) ↦ a^i.val and sr(i) ↦ b*a^i.val -/
noncomputable def dihedralToG_B (a b : G) : DihedralGroup 4 → G
  | DihedralGroup.r i => a ^ i.val
  | DihedralGroup.sr i => b * a ^ i.val

/-- The map sends 1 to 1 -/
lemma dihedralToG_B_one (a b : G) : dihedralToG_B a b 1 = 1 := by
  change dihedralToG_B a b (DihedralGroup.r 0) = 1
  simp [dihedralToG_B]

/-
The map is a homomorphism
-/
lemma dihedralToG_B_mul (a b : G) (ha : orderOf a = 4) (hb : orderOf b = 2)
    (hab : a * b ≠ b * a) (hcard : Nat.card G = 8) (x y : DihedralGroup 4) :
    dihedralToG_B a b (x * y) = dihedralToG_B a b x * dihedralToG_B a b y := by
      obtain hx | hx := x;
      · obtain hy | hy := y;
        · convert pow_val_add_4 a ha hx hy using 1;
        · have h_inv : a ^ hx.val * b = b * (a⁻¹) ^ hx.val := by
            have h_conj : b * a * b⁻¹ = a⁻¹ := by
              apply conj_inv_of_orders ha hb hab hcard;
            simp +decide [ ← h_conj, mul_assoc ];
            simp +decide [ ← mul_assoc, ← pow_two, hb.symm ];
            rw [ inv_eq_of_mul_eq_one_right ] ; rw [ ← pow_two, ← hb, pow_orderOf_eq_one ];
          have h_pow : a ^ (hy - hx).val = (a⁻¹) ^ hx.val * a ^ hy.val := by
            convert pow_val_sub_4 a ha hx hy using 1;
          unfold dihedralToG_B; simp +decide [ h_inv, h_pow ] ;
          simp +decide [ ← mul_assoc, h_inv ];
      · obtain hy | hy := y; simp_all +decide [ dihedralToG_B ] ;
        · simp +decide [ mul_assoc, pow_val_add_4 a ha ];
        · -- By definition of dihedral group multiplication, we have:
          simp [dihedralToG_B];
          -- Using the fact that $b * a * b⁻¹ = a⁻¹$, we can simplify the expression.
          have h_conj : b * a ^ hx.val * b = a⁻¹ ^ hx.val := by
            apply conj_pow_inv;
            · apply conj_inv_of_orders ha hb hab hcard;
            · rw [ ← hb, pow_orderOf_eq_one ];
          simp_all +decide [ ← mul_assoc, pow_val_sub_4 ]

/-- The MonoidHom from DihedralGroup 4 to G -/
noncomputable def dihedralHomToG_B (a b : G) (ha : orderOf a = 4) (hb : orderOf b = 2)
    (hab : a * b ≠ b * a) (hcard : Nat.card G = 8) : DihedralGroup 4 →* G where
  toFun := dihedralToG_B a b
  map_one' := dihedralToG_B_one a b
  map_mul' := dihedralToG_B_mul a b ha hb hab hcard

/-
The map is injective
-/
lemma dihedralToG_B_injective (a b : G) (ha : orderOf a = 4) (hb : orderOf b = 2)
    (hab : a * b ≠ b * a) (hcard : Nat.card G = 8) :
    Function.Injective (dihedralToG_B a b) := by
      intros x y hxy;
      rcases x with ( x | x ) <;> rcases y with ( y | y ) <;> simp_all +decide [];
      · have h_eq : a ^ x.val = a ^ y.val := by
          exact hxy;
        rw [ pow_eq_pow_iff_modEq ] at h_eq;
        fin_cases x <;> fin_cases y <;> simp_all +decide only [Nat.ModEq];
      · -- From $a^x.val = b * a^y.val$, we get $b = a^{x.val - y.val}$.
        have hb_eq : b = a ^ (x.val - y.val : ℤ) := by
          simp_all +decide [ zpow_sub, dihedralToG_B ];
          simp_all +decide [ ZMod.cast, ZMod.val ];
        simp_all +decide [];
        exact hab ( by group );
      · -- If $b * a^x = a^y$, then $b = a^{y-x}$.
        have h_b_eq_a_pow : b = a ^ (y.val - x.val : ℤ) := by
          have h_b_eq_a_pow : b * a ^ x.val = a ^ y.val := by
            exact hxy;
          convert congr_arg ( · * ( a ^ x.val ) ⁻¹ ) h_b_eq_a_pow using 1 ; group;
        simp_all +decide [ zpow_sub, mul_assoc ];
        group at * ; aesop;
      · unfold dihedralToG_B at hxy; simp_all +decide [ mul_assoc ] ;
        rw [ pow_eq_pow_iff_modEq ] at hxy;
        fin_cases x <;> fin_cases y <;> simp_all +decide only [Nat.ModEq]

/-- Main theorem: G ≅ DihedralGroup 4 when one element has order 4,
    another has order 2, and they don't commute, in a group of order 8 -/
theorem case_B_isom (a b : G) (ha : orderOf a = 4) (hb : orderOf b = 2)
    (hab : a * b ≠ b * a) (hcard : Nat.card G = 8) :
    Nonempty (G ≃* DihedralGroup 4) := by
  have ha2 : a ^ 4 = 1 := by rw [← orderOf_dvd_iff_pow_eq_one]; rw [ha]
  have hb2 : b ^ 2 = 1 := by rw [← orderOf_dvd_iff_pow_eq_one]; rw [hb]
  have hinj := dihedralToG_B_injective a b ha hb hab hcard
  have hfin_G : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hcard_D4 : Nat.card (DihedralGroup 4) = 8 := DihedralGroup.nat_card
  have hsurj : Function.Surjective (dihedralToG_B a b) := by
    haveI : Fintype (DihedralGroup 4) := Fintype.ofFinite _
    haveI : Fintype G := Fintype.ofFinite G
    have e : DihedralGroup 4 ≃ G :=
      Fintype.equivOfCardEq (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
        hcard_D4, hcard])
    exact hinj.surjective_of_finite e
  exact ⟨(MulEquiv.ofBijective (dihedralHomToG_B a b ha hb hab hcard) ⟨hinj, hsurj⟩).symm⟩
