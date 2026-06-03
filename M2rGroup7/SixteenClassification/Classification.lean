import «M2rGroup7».SixteenClassification.Preliminary
import «M2rGroup7».SixteenClassification.Blueprints
import «M2rGroup7».SixteenClassification.Lemma3

namespace OrderSixteen

lemma exists_normal_C8_or_C4_C2
    {G : Type*} [Group G]
    (hn : Nat.card G = 16)
    (h_non_iso : IsEmpty (G ≃* CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2)) :
    (∃ H : Subgroup G, H.Normal ∧ Nonempty (H ≃* CyclicGroup 8)) ∨
    (∃ H : Subgroup G, H.Normal ∧ Nonempty (H ≃* CyclicGroup 4 × CyclicGroup 2)) := by
  by_cases h_order_8 : ∃ x : G , orderOf x = 8
  · -- There is element of order 8, then C8 ◃ G
    left
    obtain ⟨x, hx⟩ := h_order_8
    let H := Subgroup.zpowers x
    use H
    have h_card : Nat.card H = 8 := by
      simp only [H, Nat.card_zpowers, hx]
    have hi : H.index = 2 := by
      have := Subgroup.index_mul_card H
      rw [h_card, hn] at this
      omega
    haveI : H.Normal := Subgroup.normal_of_index_eq_two hi
    haveI : IsCyclic H := Subgroup.isCyclic_zpowers x
    let iso : H ≃* CyclicGroup 8 := mulEquivOfCyclicCardEq (
        by simp only [h_card, card_cyclicGroup]
      )
    tauto
  · -- There are no elements of order 8, then K8 ◃ G
    right
    have h_max_order : ∃ z : G , orderOf z = 4 := by
      haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hn]; decide)
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hpg : IsPGroup 2 G := IsPGroup.of_card (n := 4) (by rw [hn]; rfl)
      by_contra h_no4
      simp only [not_exists] at h_no4
      -- Every element has order dividing 16, order ∈ {1, 2, 4, 8, 16}.
      -- Order 8 ruled out by h_order_8.
      -- Order 16 ruled out: if x has order 16, x² has order 8.
      -- Order 4 ruled out by h_no4.
      -- So every element has order 1 or 2.
      have h_sq : ∀ x : G, x ^ 2 = 1 := by
        intro x
        -- orderOf x is a power of 2 (since G is a 2-group), ≤ 16
        have h_pp : ∃ k, orderOf x = 2 ^ k :=
          (IsPGroup.iff_orderOf (p := 2) (G := G)).mp hpg x
        obtain ⟨k, hk⟩ := h_pp
        have hx_dvd : orderOf x ∣ 16 := by rw [← hn]; exact orderOf_dvd_natCard x
        rw [hk] at hx_dvd
        -- 2^k ∣ 16 = 2^4, so k ≤ 4
        have hk_le : k ≤ 4 := by
          by_contra h
          have h5 : 5 ≤ k := Nat.lt_of_not_le h
          have : (2 : ℕ) ^ 5 ∣ 2 ^ k := pow_dvd_pow 2 h5
          have : (2 : ℕ) ^ 5 ∣ 16 := this.trans hx_dvd
          exact absurd this (by decide)
        -- k ∈ {0, 1, 2, 3, 4}; rule out 2 (no order 4), 3 (no order 8), 4 (no order 16)
        interval_cases k
        · -- orderOf x = 1
          rw [orderOf_eq_one_iff.mp hk]; group
        · -- orderOf x = 2
          have : (2 : ℕ) = orderOf x := hk.symm
          rw [this]; exact pow_orderOf_eq_one x
        · -- orderOf x = 4
          exfalso; exact h_no4 x hk
        · -- orderOf x = 8
          exfalso; exact h_order_8 ⟨x, hk⟩
        · -- orderOf x = 16
          exfalso; apply h_order_8
          refine ⟨x ^ 2, ?_⟩
          rw [orderOf_pow, hk]; decide
      -- Now G is abelian with exponent 2; |G| = 16; build iso to C₂⁴
      obtain ⟨n, ⟨e⟩⟩ := mulEquiv_pi_cyclicTwo_of_sq_eq_one h_sq
      -- |G| = 2^n = 16, so n = 4
      have hn_eq : n = 4 := by
        have hcard := Nat.card_congr e.toEquiv
        rw [hn, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n),
          Fintype.card_fin, card_cyclicGroup] at hcard
        have h2 : (2 : ℕ) ^ n = 2 ^ 4 := by rw [← hcard]; rfl
        exact Nat.pow_right_injective (by decide) h2
      subst hn_eq
      -- Build (Fin 4 → C₂) ≃* C₂ × C₂ × C₂ × C₂
      let pi_iso : (Fin 4 → CyclicGroup 2) ≃*
          CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2 :=
        { toFun := fun f => (f 0, f 1, f 2, f 3)
          invFun := fun p i => match i with
            | ⟨0, _⟩ => p.1
            | ⟨1, _⟩ => p.2.1
            | ⟨2, _⟩ => p.2.2.1
            | ⟨3, _⟩ => p.2.2.2
          left_inv := fun f => by ext i; fin_cases i <;> rfl
          right_inv := fun p => rfl
          map_mul' := fun f g => by ext <;> rfl }
      exact h_non_iso.false (e.trans pi_iso)
    obtain ⟨z, hz, hz_center⟩ : ∃ z : G, orderOf z = 2 ∧ z ∈ Subgroup.center G := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hn]; decide)
      have h_dvd : 2 ∣ Nat.card (Subgroup.center G) :=
        prime_dvd_card_center Nat.prime_two (n := 4) (by rw [hn]; rfl) (by decide)
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center G) 2 h_dvd
      exact ⟨(z : G), by rw [Subgroup.orderOf_coe]; exact hz, z.2⟩
    let H := Subgroup.zpowers z
    haveI : H.Normal := by
      refine ⟨fun n hn_mem g => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn_mem
      have hzc : ∀ y : G, z * y = y * z := fun y =>
        (Subgroup.mem_center_iff.mp hz_center y).symm
      have hcomm : Commute z g := hzc g
      have hzkc : z ^ k * g = g * z ^ k := (hcomm.zpow_left k).eq
      rw [show g * z ^ k * g⁻¹ = z ^ k by rw [← hzkc, mul_assoc, mul_inv_cancel, mul_one]]
      exact H.zpow_mem (Subgroup.mem_zpowers z) k
    by_cases hx : ∃ x : G , orderOf x = 4 ∧ x^2 ≠ z
    · -- There is x of order 4 such that x^2 ≠ z
      obtain ⟨x, hxord, hxsq⟩ := hx
      let L := Subgroup.zpowers x
      have h_disj : H ⊓ L = ⊥ := by
        haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hn]; decide)
        rw [Subgroup.eq_bot_iff_forall]
        rintro y hy
        obtain ⟨hy_H, hy_L⟩ := Subgroup.mem_inf.mp hy
        by_contra hy_ne
        -- y ∈ ⟨z⟩, y ≠ 1, so y has order 2 (since orderOf z = 2)
        have hy_ord : orderOf y = 2 := by
          have hy_dvd : orderOf y ∣ orderOf z := orderOf_dvd_of_mem_zpowers hy_H
          rw [hz] at hy_dvd
          rcases (Nat.dvd_prime Nat.prime_two).mp hy_dvd with h1 | h2
          · exact absurd (orderOf_eq_one_iff.mp h1) hy_ne
          · exact h2
        -- y = x^j for some j; y² = 1, so 4 ∣ 2j, so 2 ∣ j, so y = x^(2m) = (x²)^m
        -- Since y has order 2, m must be odd, so y = x²
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hy_L
        have hy_sq : y ^ (2 : ℤ) = 1 := by
          rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, ← hy_ord]
          exact pow_orderOf_eq_one y
        have h_xord : (orderOf x : ℤ) ∣ 2 * j := by
          rw [orderOf_dvd_iff_zpow_eq_one, show (2 * j : ℤ) = j * 2 by ring,
            zpow_mul, hj, hy_sq]
        rw [hxord] at h_xord
        -- 4 ∣ 2j, so 2 ∣ j. Write j = 2m.
        have h2j : (2 : ℤ) ∣ j := by omega
        obtain ⟨m, rfl⟩ := h2j
        -- y = x^(2m). Now y has order 2, and x^(2m) = (x²)^m. x² has order 2 in ⟨x⟩.
        have hy_eq : y = (x ^ 2) ^ m := by
          rw [← hj, show ((2 * m : ℤ)) = 2 * m by ring, zpow_mul]
          congr 1; norm_cast
        -- x² has order 2 (since orderOf x = 4)
        have hx2_ord : orderOf (x ^ 2) = 2 := by
          rw [orderOf_pow, hxord]; decide
        -- y = (x²)^m has order 2 iff m is odd (since orderOf x² = 2)
        -- For any m, (x²)^m is either 1 (m even) or x² (m odd).
        -- Since y ≠ 1, m is odd, so y = x².
        -- Helper: (x²)^m for odd/even m
        have hx2_sq : (x ^ 2) ^ (2 : ℤ) = 1 := by
          rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]
          have : (x ^ 2) ^ orderOf (x ^ 2) = 1 := pow_orderOf_eq_one _
          rw [hx2_ord] at this; exact this
        have hz_sq : z ^ (2 : ℤ) = 1 := by
          rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, ← hz]
          exact pow_orderOf_eq_one z
        -- m is even or odd
        rcases Int.even_or_odd m with hm | hm
        · -- Even m: y = (x²)^m = 1, contradiction
          exfalso; apply hy_ne
          obtain ⟨n, rfl⟩ := hm
          rw [hy_eq, show ((n + n : ℤ)) = 2 * n by ring, zpow_mul, hx2_sq, one_zpow]
        · -- Odd m: y = (x²)^m = x²
          obtain ⟨n, rfl⟩ := hm
          have hy_eq2 : y = x ^ 2 := by
            rw [hy_eq, show ((2 * n + 1 : ℤ)) = 2 * n + 1 by ring, zpow_add, zpow_mul,
              hx2_sq, one_zpow, one_mul, zpow_one]
          -- y ∈ ⟨z⟩, y has order 2, so y = z (else y = 1)
          have hy_eq_z : y = z := by
            obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy_H
            rcases Int.even_or_odd k with ⟨n', rfl⟩ | ⟨n', rfl⟩
            · exfalso; apply hy_ne
              rw [← hk, show ((n' + n' : ℤ)) = 2 * n' by ring, zpow_mul, hz_sq, one_zpow]
            · rw [← hk, show ((2 * n' + 1 : ℤ)) = 2 * n' + 1 by ring, zpow_add, zpow_mul,
                hz_sq, one_zpow, one_mul, zpow_one]
          exact hxsq (hy_eq2.symm.trans hy_eq_z)
      -- K = ⟨x, z⟩ = ⟨x⟩ ⊔ ⟨z⟩ = L ⊔ H
      have hK_eq : Subgroup.closure {x, z} = L ⊔ H := by
        change Subgroup.closure {x, z} = Subgroup.zpowers x ⊔ Subgroup.zpowers z
        rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
          ← Subgroup.closure_union]
        congr 1
      -- Commutativity: z is in center so commutes with everything (incl. L)
      have h_comm : ∀ a ∈ L, ∀ b ∈ H, a * b = b * a := by
        intro a _ b hb
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        have hzc : ∀ y : G, z * y = y * z := fun y =>
          (Subgroup.mem_center_iff.mp hz_center y).symm
        have hcomm : Commute z a := hzc a
        exact ((hcomm.zpow_left k).symm).eq
      have h_disj' : L ⊓ H = ⊥ := by rw [inf_comm]; exact h_disj
      let K := Subgroup.closure {x, z}
      use K
      have h_K_card : Nat.card K = 8 := by
        have h_LH_card : Nat.card ↥(L ⊔ H) = 8 := by
          have := mulEquiv_sup_of_disjoint_comm L H h_disj' h_comm
          have hLH := Nat.card_congr this.toEquiv
          rw [Nat.card_prod] at hLH
          have hLc : Nat.card L = 4 := by simp only [L, Nat.card_zpowers, hxord]
          have hHc : Nat.card H = 2 := by simp only [H, Nat.card_zpowers, hz]
          rw [hLc, hHc] at hLH
          omega
        rw [show K = L ⊔ H from hK_eq]
        exact h_LH_card
      haveI : K.Normal := by
        have h_idx : K.index = 2 := by
          have := Subgroup.index_mul_card K
          rw [h_K_card, hn] at this
          omega
        exact Subgroup.normal_of_index_eq_two h_idx
      let iso : K ≃* CyclicGroup 4 × CyclicGroup 2 := by
        have h_card : Nat.card H = 2 := by
          simp only [H, Nat.card_zpowers, hz]
        letI iH : H ≃* CyclicGroup 2 := mulEquivOfCyclicCardEq (
            by simp only [h_card, card_cyclicGroup]
          )
        have l_card : Nat.card L = 4 := by
          simp only [L, Nat.card_zpowers, hxord]
        letI iL : L ≃* CyclicGroup 4 := mulEquivOfCyclicCardEq (
            by simp only [l_card, card_cyclicGroup]
          )
        let prod_iso : L × H ≃* ↑(L ⊔ H) :=
          mulEquiv_sup_of_disjoint_comm L H h_disj' h_comm
        have hK_subgroup_eq : K = L ⊔ H := hK_eq
        -- K ≃* ↑(L ⊔ H) via the equality of subgroups
        let eq_iso : K ≃* ↑(L ⊔ H) :=
          MulEquiv.subgroupCongr hK_subgroup_eq
        exact eq_iso.trans (prod_iso.symm.trans (iL.prodCongr iH))
      tauto
    · -- Every x of order 4 has x^2 = z
      have hx : ∀ x : G, orderOf x = 4 → x^2 = z := by simp_all
      haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hn]; decide)
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hpg : IsPGroup 2 G := IsPGroup.of_card (n := 4) (by rw [hn]; rfl)
      -- Pick x of order 4
      obtain ⟨x, hxord⟩ := h_max_order
      have hxsq : x ^ 2 = z := hx x hxord
      -- z = x^2 ∈ ⟨x⟩
      have hz_mem_zpow : z ∈ Subgroup.zpowers x := by
        rw [← hxsq]
        refine ⟨(2 : ℤ), ?_⟩
        change x ^ (2 : ℤ) = x ^ 2
        rw [zpow_two, sq]
      -- Every element g satisfies g^2 ∈ H = ⟨z⟩
      have hg_sq_mem_H : ∀ g : G, g ^ 2 ∈ H := by
        intro g
        have h_pp : ∃ k, orderOf g = 2 ^ k :=
          (IsPGroup.iff_orderOf (p := 2) (G := G)).mp hpg g
        obtain ⟨k, hk⟩ := h_pp
        have hg_dvd : orderOf g ∣ 16 := by rw [← hn]; exact orderOf_dvd_natCard g
        rw [hk] at hg_dvd
        have hk_le : k ≤ 4 := by
          by_contra hl
          have h5 : 5 ≤ k := Nat.lt_of_not_le hl
          have : (2 : ℕ) ^ 5 ∣ 2 ^ k := pow_dvd_pow 2 h5
          have : (2 : ℕ) ^ 5 ∣ 16 := this.trans hg_dvd
          exact absurd this (by decide)
        interval_cases k
        · -- orderOf g = 1, g = 1, g^2 = 1
          rw [orderOf_eq_one_iff.mp hk, one_pow]; exact H.one_mem
        · -- orderOf g = 2, g^2 = 1
          have : g ^ 2 = 1 := by
            rw [show (2 : ℕ) = orderOf g from hk.symm]
            exact pow_orderOf_eq_one g
          rw [this]; exact H.one_mem
        · -- orderOf g = 4, g^2 = z by hx
          have hgsq : g ^ 2 = z := hx g hk
          rw [hgsq]; exact Subgroup.mem_zpowers z
        · -- orderOf g = 8: contradiction
          exact absurd ⟨g, hk⟩ h_order_8
        · -- orderOf g = 16: g^2 has order 8, contradiction
          exfalso; apply h_order_8
          refine ⟨g ^ 2, ?_⟩
          rw [orderOf_pow, hk]; decide
      -- Conjugates of x lie in {x, z*x}
      -- Because G/H is abelian (every q^2 = 1 in G/H), g*x*g⁻¹ * x⁻¹ ∈ H
      have h_conj_in_Hx : ∀ g : G, g * x * g⁻¹ * x⁻¹ ∈ H := by
        intro g
        -- It suffices to show in Q = G/H, (gx g⁻¹) * x⁻¹ = 1
        -- Q has exponent 2 (from hg_sq_mem_H), hence abelian
        have hQ_sq : ∀ q : G ⧸ H, q ^ 2 = 1 := by
          intro q
          induction q using QuotientGroup.induction_on with
          | H g =>
            change (QuotientGroup.mk (g ^ 2) : G ⧸ H) = 1
            rw [QuotientGroup.eq_one_iff]
            exact hg_sq_mem_H g
        haveI : IsMulCommutative (G ⧸ H) := isMulCommutative_of_sq_eq_one hQ_sq
        -- In Q, gxg⁻¹ = x, so gxg⁻¹ * x⁻¹ ∈ H
        rw [← QuotientGroup.eq_one_iff]
        change ((g * x * g⁻¹ * x⁻¹ : G) : G ⧸ H) = 1
        have hcomm : (QuotientGroup.mk g : G ⧸ H) * (QuotientGroup.mk x : G ⧸ H) =
            (QuotientGroup.mk x : G ⧸ H) * (QuotientGroup.mk g : G ⧸ H) :=
          mul_comm _ _
        calc ((g : G ⧸ H) * (x : G ⧸ H) * (g : G ⧸ H)⁻¹ * (x : G ⧸ H)⁻¹)
            = (g : G ⧸ H) * (x : G ⧸ H) * ((x : G ⧸ H) * (g : G ⧸ H))⁻¹ := by group
          _ = (g : G ⧸ H) * (x : G ⧸ H) * ((g : G ⧸ H) * (x : G ⧸ H))⁻¹ := by rw [← hcomm]
          _ = 1 := by group
      -- Therefore, for any g, g*x*g⁻¹ ∈ {x, z*x}
      have h_conj_pair : ∀ g : G, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = z * x := by
        intro g
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (h_conj_in_Hx g)
        -- hk : z ^ k = g * x * g⁻¹ * x⁻¹
        -- z has order 2, so z^k ∈ {1, z}
        have hz_sq : z ^ (2 : ℤ) = 1 := by
          rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, ← hz]
          exact pow_orderOf_eq_one z
        rcases Int.even_or_odd k with ⟨n, rfl⟩ | ⟨n, rfl⟩
        · -- k = n + n = 2n, so z^k = 1
          left
          have hzpow_one : z ^ (n + n : ℤ) = 1 := by
            rw [show ((n + n : ℤ)) = 2 * n by ring, zpow_mul, hz_sq, one_zpow]
          rw [hzpow_one] at hk
          -- hk : 1 = g * x * g⁻¹ * x⁻¹
          have heq : g * x * g⁻¹ * x⁻¹ = 1 := hk.symm
          have : g * x * g⁻¹ = x := by
            have : g * x * g⁻¹ * x⁻¹ * x = 1 * x := by rw [heq]
            simpa using this
          exact this
        · -- k = 2n+1, z^k = z
          right
          have h_zk : z ^ ((2 * n + 1 : ℤ)) = z := by
            rw [zpow_add, zpow_mul, hz_sq, one_zpow, one_mul, zpow_one]
          rw [h_zk] at hk
          -- hk : z = g * x * g⁻¹ * x⁻¹
          have : g * x * g⁻¹ = z * x := by
            have hk' : g * x * g⁻¹ * x⁻¹ = z := hk.symm
            calc g * x * g⁻¹ = g * x * g⁻¹ * x⁻¹ * x := by group
              _ = z * x := by rw [hk']
          exact this
      -- The conjugacy orbit of x has cardinality ≤ 2
      -- Conclude centralizer of x has Nat.card ≥ 8
      set Cx : Subgroup G := Subgroup.centralizer {x} with hCx_def
      have hCx_ge_8 : Nat.card Cx ≥ 8 := by
        -- Use action of ConjAct G on G directly
        have h_orbit_stab : Nat.card (MulAction.orbit (ConjAct G) x) *
            Nat.card (MulAction.stabilizer (ConjAct G) x) = Nat.card G := by
          classical
          haveI : Fintype G := Fintype.ofFinite G
          simp only [Nat.card_eq_fintype_card]
          exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) x
        rw [hn] at h_orbit_stab
        have h_orbit_le : Nat.card (MulAction.orbit (ConjAct G) x) ≤ 2 := by
          have h_sub : (MulAction.orbit (ConjAct G) x) ⊆ ({x, z * x} : Set G) := by
            intro a ha
            obtain ⟨c, hc⟩ := ha
            -- hc : c • x = a, where • is ConjAct on G
            have hc' : (ConjAct.ofConjAct c) * x * (ConjAct.ofConjAct c)⁻¹ = a := by
              have hh : c • x = a := hc
              rw [ConjAct.smul_def] at hh
              exact hh
            rcases h_conj_pair (ConjAct.ofConjAct c) with h1 | h2
            · left
              rw [← hc', h1]
            · right
              rw [Set.mem_singleton_iff, ← hc', h2]
          have h_finite_set : Set.Finite ({x, z * x} : Set G) :=
            (Set.finite_singleton _).insert _
          have h_card_le := Nat.card_mono h_finite_set h_sub
          have h2' : Nat.card ({x, z * x} : Set G) ≤ 2 := by
            classical
            rw [Nat.card_coe_set_eq]
            have := Set.ncard_insert_le x ({z * x} : Set G)
            rw [Set.ncard_singleton] at this
            exact this
          exact h_card_le.trans h2'
        have h_stab_eq : Nat.card (MulAction.stabilizer (ConjAct G) x) =
            Nat.card Cx := by
          rw [hCx_def]
          exact (Subgroup.nat_card_centralizer_nat_card_stabilizer x).symm
        rw [h_stab_eq] at h_orbit_stab
        have h_orbit_pos : 0 < Nat.card (MulAction.orbit (ConjAct G) x) := by
          haveI : Nonempty (MulAction.orbit (ConjAct G) x) :=
            ⟨⟨x, MulAction.mem_orbit_self _⟩⟩
          exact Nat.card_pos
        nlinarith [h_orbit_le, h_orbit_pos, h_orbit_stab]
      -- ⟨x⟩ ≤ Cx (x commutes with itself)
      have hxC : Subgroup.zpowers x ≤ Cx := by
        intro a ha
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        rw [hCx_def, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact ((Commute.refl x).zpow_right k).eq
      -- |Cx| ≥ 8 > 4 = |⟨x⟩|, so ⟨x⟩ < Cx properly
      have h_not_le : ¬ (Cx ≤ Subgroup.zpowers x) := by
        intro hle
        have := Subgroup.card_le_of_le hle
        rw [Nat.card_zpowers, hxord] at this
        omega
      -- Get y ∈ Cx, y ∉ ⟨x⟩
      obtain ⟨y, hy_C, hy_not⟩ : ∃ y ∈ Cx, y ∉ Subgroup.zpowers x := by
        by_contra hno
        push Not at hno
        exact h_not_le hno
      -- y commutes with x
      have hyx_comm : y * x = x * y := by
        have := (Subgroup.mem_centralizer_iff.mp hy_C) x (Set.mem_singleton x)
        exact this.symm
      -- orderOf y is a power of 2, ≤ 16, ≠ 8, ≠ 16, ≠ 1 (since y ∉ ⟨x⟩ and 1 ∈ ⟨x⟩)
      have hy_ne_one : y ≠ 1 := fun h => hy_not (h ▸ Subgroup.one_mem _)
      have hy_pp : ∃ k, orderOf y = 2 ^ k :=
        (IsPGroup.iff_orderOf (p := 2) (G := G)).mp hpg y
      obtain ⟨k, hk⟩ := hy_pp
      have hy_dvd : orderOf y ∣ 16 := by rw [← hn]; exact orderOf_dvd_natCard y
      rw [hk] at hy_dvd
      have hk_le : k ≤ 4 := by
        by_contra hl
        have h5 : 5 ≤ k := Nat.lt_of_not_le hl
        have : (2 : ℕ) ^ 5 ∣ 2 ^ k := pow_dvd_pow 2 h5
        have : (2 : ℕ) ^ 5 ∣ 16 := this.trans hy_dvd
        exact absurd this (by decide)
      have hy_ord_2_or_4 : orderOf y = 2 ∨ orderOf y = 4 := by
        interval_cases k
        · exfalso; exact hy_ne_one (orderOf_eq_one_iff.mp hk)
        · left; exact hk
        · right; exact hk
        · exfalso; exact h_order_8 ⟨y, hk⟩
        · exfalso; apply h_order_8
          refine ⟨y ^ 2, ?_⟩; rw [orderOf_pow, hk]; decide
      -- Define w to be y if orderOf y = 2 (and y ≠ z), else x*y (order 2)
      -- In both cases we get w of order 2, w ≠ z (since w ∉ ⟨x⟩ ∋ z), w commutes with x
      have hxz_in_zpowers : z ∈ Subgroup.zpowers x := hz_mem_zpow
      have : ∃ w : G, orderOf w = 2 ∧ w ∉ Subgroup.zpowers x ∧ w * x = x * w := by
        rcases hy_ord_2_or_4 with h2 | h4
        · exact ⟨y, h2, hy_not, hyx_comm⟩
        · -- orderOf y = 4, so y^2 = z. Take w = x*y, orderOf w = 2
          have hysq : y ^ 2 = z := hx y h4
          have hxy_sq : (x * y) ^ 2 = 1 := by
            have hzz : z * z = 1 := by
              have : z ^ 2 = 1 := by
                rw [show (2 : ℕ) = orderOf z from hz.symm]; exact pow_orderOf_eq_one z
              rw [sq] at this; exact this
            calc (x * y) ^ 2 = x * y * (x * y) := sq (x*y)
              _ = x * (y * x) * y := by group
              _ = x * (x * y) * y := by rw [hyx_comm]
              _ = (x * x) * (y * y) := by group
              _ = x^2 * y^2 := by rw [← sq, ← sq]
              _ = z * z := by rw [hxsq, hysq]
              _ = 1 := hzz
          have hxy_ne_one : x * y ≠ 1 := by
            intro h
            apply hy_not
            have : y = x⁻¹ := by
              have hk : x * y = 1 := h
              have : x⁻¹ * (x * y) = x⁻¹ * 1 := by rw [hk]
              simpa using this
            rw [this]
            exact (Subgroup.zpowers x).inv_mem (Subgroup.mem_zpowers x)
          have hxy_ord : orderOf (x * y) = 2 := by
            have hxy_dvd : orderOf (x * y) ∣ 2 := orderOf_dvd_of_pow_eq_one hxy_sq
            rcases (Nat.dvd_prime Nat.prime_two).mp hxy_dvd with h1 | h2
            · exact absurd (orderOf_eq_one_iff.mp h1) hxy_ne_one
            · exact h2
          have hxy_not : x * y ∉ Subgroup.zpowers x := by
            intro hin
            -- if x*y ∈ ⟨x⟩, then y = x⁻¹*(x*y) ∈ ⟨x⟩, contradiction
            have : y ∈ Subgroup.zpowers x := by
              have : y = x⁻¹ * (x * y) := by group
              rw [this]
              exact (Subgroup.zpowers x).mul_mem
                ((Subgroup.zpowers x).inv_mem (Subgroup.mem_zpowers x)) hin
            exact hy_not this
          have hxy_comm : (x * y) * x = x * (x * y) := by
            calc (x * y) * x = x * (y * x) := by group
              _ = x * (x * y) := by rw [hyx_comm]
          exact ⟨x * y, hxy_ord, hxy_not, hxy_comm⟩
      obtain ⟨w, hwo, hw_not, hwx_comm⟩ := this
      -- Now build K = ⟨x⟩ ⊔ ⟨w⟩ ≅ C₄ × C₂
      let L := Subgroup.zpowers x
      let M := Subgroup.zpowers w
      -- L ⊓ M = ⊥
      have h_disj : L ⊓ M = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        rintro u hu
        obtain ⟨huL, huM⟩ := Subgroup.mem_inf.mp hu
        by_contra hu_ne
        -- u ∈ ⟨w⟩ with orderOf w = 2, u ≠ 1, so u = w
        have hu_eq_w : u = w := by
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp huM
          have hw_sq : w ^ (2 : ℤ) = 1 := by
            rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, ← hwo]
            exact pow_orderOf_eq_one w
          rcases Int.even_or_odd k with ⟨n, rfl⟩ | ⟨n, rfl⟩
          · exfalso; apply hu_ne
            rw [← hk, show ((n + n : ℤ)) = 2 * n by ring, zpow_mul, hw_sq, one_zpow]
          · rw [← hk, show ((2 * n + 1 : ℤ)) = 2 * n + 1 by ring, zpow_add, zpow_mul,
              hw_sq, one_zpow, one_mul, zpow_one]
        rw [hu_eq_w] at huL
        exact hw_not huL
      have h_comm : ∀ a ∈ L, ∀ b ∈ M, a * b = b * a := by
        intro a ha b hb
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        have hcomm : Commute x w := hwx_comm.symm
        exact ((hcomm.zpow_zpow i j)).eq
      let K := Subgroup.closure {x, w}
      use K
      have hK_eq : K = L ⊔ M := by
        change Subgroup.closure {x, w} = Subgroup.zpowers x ⊔ Subgroup.zpowers w
        rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
          ← Subgroup.closure_union]
        congr 1
      have h_K_card : Nat.card K = 8 := by
        have h_LM_card : Nat.card ↥(L ⊔ M) = 8 := by
          have := mulEquiv_sup_of_disjoint_comm L M h_disj h_comm
          have hLM := Nat.card_congr this.toEquiv
          rw [Nat.card_prod] at hLM
          have hLc : Nat.card L = 4 := by simp only [L, Nat.card_zpowers, hxord]
          have hMc : Nat.card M = 2 := by simp only [M, Nat.card_zpowers, hwo]
          rw [hLc, hMc] at hLM
          omega
        rw [show K = L ⊔ M from hK_eq]
        exact h_LM_card
      haveI : K.Normal := by
        have h_idx : K.index = 2 := by
          have := Subgroup.index_mul_card K
          rw [h_K_card, hn] at this
          omega
        exact Subgroup.normal_of_index_eq_two h_idx
      refine ⟨‹K.Normal›, ⟨?_⟩⟩
      have l_card : Nat.card L = 4 := by simp only [L, Nat.card_zpowers, hxord]
      have m_card : Nat.card M = 2 := by simp only [M, Nat.card_zpowers, hwo]
      letI iL : L ≃* CyclicGroup 4 := mulEquivOfCyclicCardEq (
          by simp only [l_card, card_cyclicGroup]
        )
      letI iM : M ≃* CyclicGroup 2 := mulEquivOfCyclicCardEq (
          by simp only [m_card, card_cyclicGroup]
        )
      let prod_iso : L × M ≃* ↑(L ⊔ M) :=
        mulEquiv_sup_of_disjoint_comm L M h_disj h_comm
      let eq_iso : K ≃* ↑(L ⊔ M) := MulEquiv.subgroupCongr hK_eq
      exact eq_iso.trans (prod_iso.symm.trans (iL.prodCongr iM))

theorem realise_ext_type_if_not_iso_to_C2_4
    {G : Type*} [Group G]
    (hn : Nat.card G = 16)
    (h_non_iso : IsEmpty (G ≃* CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2)) :
    Nonempty (RealiseExtType G ext_16_1) ∨
    Nonempty (RealiseExtType G ext_16_2) ∨
    Nonempty (RealiseExtType G ext_16_3) ∨
    Nonempty (RealiseExtType G ext_16_4) ∨
    Nonempty (RealiseExtType G ext_16_5) ∨
    Nonempty (RealiseExtType G ext_16_6) ∨
    Nonempty (RealiseExtType G ext_16_7) ∨
    Nonempty (RealiseExtType G ext_16_8) ∨
    Nonempty (RealiseExtType G ext_16_9) ∨
    Nonempty (RealiseExtType G ext_16_10) ∨
    Nonempty (RealiseExtType G ext_16_11) ∨
    Nonempty (RealiseExtType G ext_16_12) ∨
    Nonempty (RealiseExtType G ext_16_13) := by
  rcases exists_normal_C8_or_C4_C2 hn h_non_iso with
    ⟨H, hN, h_iso⟩ | ⟨H, hN, h_iso⟩
  · haveI := hN
    have := realise_with_normal_C8 hn H h_iso
    tauto
  · haveI := hN
    have := realise_with_normal_K8 hn H h_iso
    tauto

end OrderSixteen
