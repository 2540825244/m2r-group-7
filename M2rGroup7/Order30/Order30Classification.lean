import Mathlib
import «M2rGroup7».CyclicGroup
import «M2rGroup7».Lemmas.GroupTheoryLemmas
import «M2rGroup7».Lemmas.ClassificationUtils
import «M2rGroup7».P2qClassification.PqClassification

/-!
# Classification of groups of order 30

Every group of order 30 is isomorphic to one of:
- `CyclicGroup 30`
- `SemidirectProduct (CyclicGroup 15) (CyclicGroup 2) (canonicalC2OnC15Pow k _)` for
  `k ∈ {4, 11, 14}`, the three non-trivial square roots of `1` mod `15` other than `1` itself.

The proof finds a normal subgroup `N` of order `15` (via `pqr_group_has_normal_subgroup_card_qr`),
applies Schur–Zassenhaus to split `G ≅ N ⋊ K` with `K` of order `2`, identifies `N ≅ CyclicGroup 15`
(via `pq_classification`, ruling out the non-cyclic branch since `3 ∤ 4`) and `K ≅ CyclicGroup 2`,
and finally shows that any action `CyclicGroup 2 →* MulAut (CyclicGroup 15)` is a power map
`x ↦ x ^ k` with `k² ≡ 1 [MOD 15]`.
-/

private lemma pow_eq_self_of_C15 {m : ℕ} (hm : m % 15 = 1) (x : CyclicGroup 15) : x ^ m = x := by
  have h15 : x ^ 15 = 1 := by
    have h := pow_card_eq_one' (G := CyclicGroup 15) (x := x)
    rwa [card_cyclicGroup] at h
  conv_lhs => rw [← Nat.div_add_mod m 15, pow_add, pow_mul, h15, one_pow, one_mul, hm, pow_one]

private lemma pow_pow_eq_self_C15 {k : ℕ} (hk : (k * k) % 15 = 1) (x : CyclicGroup 15) :
    (x ^ k) ^ k = x := by rw [← pow_mul]; exact pow_eq_self_of_C15 hk x

/-- The automorphism `x ↦ x ^ k` of `CyclicGroup 15`, valid when `k² ≡ 1 [MOD 15]`. -/
def powAutC15 (k : ℕ) (hk : (k * k) % 15 = 1) : MulAut (CyclicGroup 15) where
  toFun := (· ^ k)
  invFun := (· ^ k)
  left_inv := pow_pow_eq_self_C15 hk
  right_inv := pow_pow_eq_self_C15 hk
  map_mul' a b := mul_pow a b k

private lemma powAutC15_sq (k : ℕ) (hk : (k * k) % 15 = 1) : (powAutC15 k hk) ^ 2 = 1 := by
  ext x; change (x ^ k) ^ k = x; exact pow_pow_eq_self_C15 hk x

/-- The canonical (computable) action `CyclicGroup 2 →* MulAut (CyclicGroup 15)` sending the
    generator of `CyclicGroup 2` to the power map `x ↦ x ^ k`. -/
def canonicalC2OnC15Pow (k : ℕ) (hk : (k * k) % 15 = 1) :
    CyclicGroup 2 →* MulAut (CyclicGroup 15) :=
  cyclicHom 2 (powAutC15 k hk) (powAutC15_sq k hk)

private lemma cyclicGroup_eq_zpow_gen {n : ℕ} [NeZero n] (x : CyclicGroup n) :
    ∃ m : ℤ, x = (Multiplicative.ofAdd (1 : ZMod n)) ^ m := by
  refine ⟨((Multiplicative.toAdd x).val : ℤ), ?_⟩
  rw [zpow_natCast, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]

private lemma cyclicGroup_generated {n : ℕ} [NeZero n] (x : CyclicGroup n) :
    x ∈ Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod n)) :=
  let ⟨m, hm⟩ := cyclicGroup_eq_zpow_gen x
  Subgroup.mem_zpowers_iff.mpr ⟨m, hm.symm⟩

private lemma cyclicHom_apply_gen {n : ℕ} [NeZero n] {G : Type*} [Group G] (a : G) (h : a ^ n = 1) :
    cyclicHom n a h (Multiplicative.ofAdd (1 : ZMod n)) = a := by
  change Additive.toMul ((ZMod.lift n
      ⟨zmultiplesHom (Additive G) (Additive.ofMul a),
        by change (n : ℤ) • Additive.ofMul a = 0
           rw [← ofMul_zpow, zpow_natCast, h, ofMul_one]⟩)
      (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod n))))
    = a
  rw [toAdd_ofAdd, show (1 : ZMod n) = ((1 : ℤ) : ZMod n) by norm_cast,
      ZMod.lift_coe, zmultiplesHom_apply, one_zsmul, toMul_ofMul]

private lemma orderOf_gen_C15 : orderOf (Multiplicative.ofAdd (1 : ZMod 15)) = 15 := by
  rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

private lemma mulAut_C15_eq_pow (σ : MulAut (CyclicGroup 15)) :
    ∃ k : ℕ, k < 15 ∧ ∀ x : CyclicGroup 15, σ x = x ^ k := by
  refine ⟨(Multiplicative.toAdd (σ (Multiplicative.ofAdd (1 : ZMod 15)))).val, ZMod.val_lt _,
    fun x => ?_⟩
  have heq : σ.toMonoidHom =
      powMonoidHom (Multiplicative.toAdd (σ (Multiplicative.ofAdd (1 : ZMod 15)))).val :=
    monoidHom_eq_of_generator_eq cyclicGroup_generated (by
      change σ (Multiplicative.ofAdd (1 : ZMod 15))
        = (Multiplicative.ofAdd (1 : ZMod 15))
            ^ (Multiplicative.toAdd (σ (Multiplicative.ofAdd (1 : ZMod 15)))).val
      rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, ofAdd_toAdd])
  exact DFunLike.congr_fun heq x

theorem classification_30 [Group G] (h : Nat.card G = 30) :
    Nonempty (G ≃* CyclicGroup 30) ∨
    Nonempty (G ≃* SemidirectProduct (CyclicGroup 15) (CyclicGroup 2)
                    (canonicalC2OnC15Pow 4 (by decide))) ∨
    Nonempty (G ≃* SemidirectProduct (CyclicGroup 15) (CyclicGroup 2)
                    (canonicalC2OnC15Pow 11 (by decide))) ∨
    Nonempty (G ≃* SemidirectProduct (CyclicGroup 15) (CyclicGroup 2)
                    (canonicalC2OnC15Pow 14 (by decide))) := by
  haveI : Finite G := by apply Nat.finite_of_card_ne_zero; rw [h]; omega
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h30 : Nat.card G = 2 * 3 * 5 := by omega
  obtain ⟨N, hN_card, hN_normal⟩ :=
    pqr_group_has_normal_subgroup_card_qr (G := G) (p := 2) (q := 3) (r := 5)
      (by norm_num) (by norm_num) h30
  haveI := hN_normal
  have hN_index : N.index = 2 := by
    have hcard := Subgroup.card_mul_index N
    rw [hN_card, h] at hcard; omega
  obtain ⟨U, hU⟩ := Subgroup.exists_right_complement'_of_coprime (N := N)
    (by rw [hN_card, hN_index]; norm_num)
  have h_iso_g_n_u := SemidirectProduct.mulEquivSubgroup hU
  let φ : ↥U →* MulAut ↥N :=
    N.normalizerMonoidHom.comp (Subgroup.inclusion (by simp [Subgroup.normalizer_eq_top]))
  have hU_card : Nat.card ↥U = 2 := by
    have h1 : Nat.card G = Nat.card ↥N * Nat.card ↥U := by
      have heq := Nat.card_congr h_iso_g_n_u.toEquiv
      rw [SemidirectProduct.card] at heq; exact heq.symm
    rw [hN_card, h] at h1; omega
  have eN : Nonempty (↥N ≃* CyclicGroup 15) := by
    rcases pq_classification (p := 3) (q := 5) (by norm_num) hN_card with ⟨e⟩ | ⟨hr, -⟩
    · exact e
    · exfalso
      have hndvd : ¬ (3 : ℕ) ∣ (5 - 1) := by norm_num
      have hfact : (5 - 1 : ℕ).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd hndvd
      have := (Nat.le_min.mp hr).2
      omega
  have eU : Nonempty (↥U ≃* CyclicGroup 2) := prime_classification_of_group hU_card
  obtain ⟨eN'⟩ := eN
  obtain ⟨eU'⟩ := eU
  let φ' : CyclicGroup 2 →* MulAut (CyclicGroup 15) :=
    (MulAut.congr eN').toMonoidHom.comp (φ.comp eU'.symm.toMonoidHom)
  have h_bridge : ↥N ⋊[φ] ↥U ≃* SemidirectProduct (CyclicGroup 15) (CyclicGroup 2) φ' :=
    SemidirectProduct.congr' (φ₁ := φ) (fn := eN') (fg := eU')
  have h_g_iso : G ≃* SemidirectProduct (CyclicGroup 15) (CyclicGroup 2) φ' :=
    h_iso_g_n_u.symm.trans h_bridge
  by_cases hφ_triv : φ' = 1
  · refine Or.inl ⟨h_g_iso.trans ((SemidirectProduct.mulEquivOfTrivialAction hφ_triv).trans
      (CyclicGroup.prodMulEquiv (by norm_num : Nat.Coprime 15 2)))⟩
  · have hg₂_sq := pow_card_eq_one' (G := CyclicGroup 2) (x := Multiplicative.ofAdd (1 : ZMod 2))
    rw [card_cyclicGroup] at hg₂_sq
    have hσ_sq : (φ' (Multiplicative.ofAdd (1 : ZMod 2))) ^ 2 = 1 := by
      rw [← map_pow, hg₂_sq, map_one]
    have hσ_ne : φ' (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := fun hσ1 =>
      hφ_triv (monoidHom_eq_of_generator_eq cyclicGroup_generated
        (by rw [hσ1, MonoidHom.one_apply]))
    obtain ⟨k, hk_lt, hpow⟩ := mulAut_C15_eq_pow (φ' (Multiplicative.ofAdd (1 : ZMod 2)))
    have hk_ne_one : k ≠ 1 := fun hk1 =>
      hσ_ne (MulEquiv.ext fun x => by rw [hpow x, hk1, pow_one]; rfl)
    have hsqmod : (k * k) % 15 = 1 := by
      have hgen_sq : φ' (Multiplicative.ofAdd (1 : ZMod 2))
          (φ' (Multiplicative.ofAdd (1 : ZMod 2)) (Multiplicative.ofAdd (1 : ZMod 15)))
          = Multiplicative.ofAdd (1 : ZMod 15) := by
        have heq2 := DFunLike.congr_fun hσ_sq (Multiplicative.ofAdd (1 : ZMod 15))
        simp only [pow_two] at heq2
        exact heq2
      have step1 := hpow (Multiplicative.ofAdd (1 : ZMod 15))
      have step2 :=
        hpow (φ' (Multiplicative.ofAdd (1 : ZMod 2)) (Multiplicative.ofAdd (1 : ZMod 15)))
      have key := step2.symm.trans hgen_sq
      rw [step1] at key
      rw [← pow_mul] at key
      have hpow2 := key.trans (pow_one _).symm
      have hfin : IsOfFinOrder (Multiplicative.ofAdd (1 : ZMod 15)) :=
        orderOf_pos_iff.mp (by rw [orderOf_gen_C15]; norm_num)
      have hmod : k * k ≡ 1 [MOD orderOf (Multiplicative.ofAdd (1 : ZMod 15))] :=
        hfin.pow_eq_pow_iff_modEq.mp hpow2
      rw [orderOf_gen_C15] at hmod
      unfold Nat.ModEq at hmod
      omega
    have hk_cases : k = 4 ∨ k = 11 ∨ k = 14 := by
      have aux : ∀ m : ℕ, m < 15 → (m * m) % 15 = 1 → m ≠ 1 → m = 4 ∨ m = 11 ∨ m = 14 := by decide
      exact aux k hk_lt hsqmod hk_ne_one
    have hσ_eq : φ' (Multiplicative.ofAdd (1 : ZMod 2)) = powAutC15 k hsqmod :=
      MulEquiv.ext fun x => (hpow x).trans rfl
    have hφ'_eq : φ' = canonicalC2OnC15Pow k hsqmod :=
      monoidHom_eq_of_generator_eq cyclicGroup_generated
        (hσ_eq.trans (cyclicHom_apply_gen (powAutC15 k hsqmod) (powAutC15_sq k hsqmod)).symm)
    have h_g_iso' : G ≃* SemidirectProduct (CyclicGroup 15) (CyclicGroup 2)
        (canonicalC2OnC15Pow k hsqmod) := hφ'_eq ▸ h_g_iso
    rcases hk_cases with rfl | rfl | rfl <;>
    · tauto
