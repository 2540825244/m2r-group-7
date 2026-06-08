import Mathlib.GroupTheory.Sylow
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SemidirectProduct
import «M2rGroup7».Classification
import «M2rGroup7».Lemmas.SylowUtils

/-- A group of order `24` has either `1` or `4` Sylow 3-subgroups. -/
lemma sylow3_24 {G : Type*} [Group G] (h : Nat.card G = 24) :
    Nat.card (Sylow 3 G) = 1 ∨ Nat.card (Sylow 3 G) = 4 := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; decide)
  have h_mod : Nat.card (Sylow 3 G) % 3 = 1 % 3 := card_sylow_modEq_one 3 G
  have h_dvd : Nat.card (Sylow 3 G) ∣ 24 := by
    rw [← h]
    exact (Sylow.card_dvd_index (default : Sylow 3 G)).trans (Subgroup.index_dvd_card _)
  have h_pos : 0 < Nat.card (Sylow 3 G) := Nat.card_pos
  have h_le : Nat.card (Sylow 3 G) ≤ 24 := Nat.le_of_dvd (by decide) h_dvd
  interval_cases (Nat.card (Sylow 3 G)) <;> omega

/-- Trivial-action branch of the normal-Sylow-3 classification: given a direct-product
    iso `G ≃* CyclicGroup 3 × Q` with `|Q| = 8`, dispatch on `order8_classification` of `Q`
    to identify `G` as one of the 5 trivial-action targets. -/
private lemma order24_1_sylow3_trivial
    {G Q : Type*} [Group G] [Group Q]
    (h_iso : G ≃* CyclicGroup 3 × Q) (hQ_card : Nat.card Q = 8) :
    Nonempty (G ≃* CyclicGroup 3 × CyclicGroup 8) ∨
    Nonempty (G ≃* CyclicGroup 3 × (CyclicGroup 4 × CyclicGroup 2)) ∨
    Nonempty (G ≃* CyclicGroup 3 × (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2)) ∨
    Nonempty (G ≃* CyclicGroup 3 × DihedralGroup 4) ∨
    Nonempty (G ≃* CyclicGroup 3 × QuaternionGroup 2) := by
  rcases order8_classification (G := Q) hQ_card with hC8 | hC4C2 | hC2sq3 | hD4 | hQ8
  · obtain ⟨e⟩ := hC8
    let : G ≃* CyclicGroup 3 × CyclicGroup 8 :=
      h_iso.trans ((MulEquiv.refl (CyclicGroup 3)).prodCongr e)
    tauto
  · obtain ⟨e⟩ := hC4C2
    let : G ≃* CyclicGroup 3 × (CyclicGroup 4 × CyclicGroup 2) :=
      h_iso.trans ((MulEquiv.refl (CyclicGroup 3)).prodCongr e)
    tauto
  · obtain ⟨e⟩ := hC2sq3
    let : G ≃* CyclicGroup 3 × (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) :=
      h_iso.trans ((MulEquiv.refl (CyclicGroup 3)).prodCongr e)
    tauto
  · obtain ⟨e⟩ := hD4
    let : G ≃* CyclicGroup 3 × DihedralGroup 4 :=
      h_iso.trans ((MulEquiv.refl (CyclicGroup 3)).prodCongr e)
    tauto
  · obtain ⟨e⟩ := hQ8
    let : G ≃* CyclicGroup 3 × QuaternionGroup 2 :=
      h_iso.trans ((MulEquiv.refl (CyclicGroup 3)).prodCongr e)
    tauto

/-- Step 2 (factor split): in a semidirect product whose action factors through the first
    projection `A × B → A`, the `B` factor splits off as a direct factor. -/
private def sdp_prodEquivOfFstAction
    {N A B : Type*} [Group N] [Group A] [Group B] (ψ : A →* MulAut N) :
    N ⋊[ψ.comp (MonoidHom.fst A B)] (A × B) ≃* (N ⋊[ψ] A) × B where
  toFun x := (⟨x.left, x.right.1⟩, x.right.2)
  invFun y := ⟨y.1.left, (y.1.right, y.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- `CyclicGroup 2` has only two elements: `1` and `ofAdd 1`. -/
private lemma cyclicGroup_two_cases (k : CyclicGroup 2) :
    k = 1 ∨ k = Multiplicative.ofAdd (1 : ZMod 2) := by
  change Multiplicative.ofAdd (Multiplicative.toAdd k) = 1 ∨
    Multiplicative.ofAdd (Multiplicative.toAdd k) = Multiplicative.ofAdd (1 : ZMod 2)
  generalize Multiplicative.toAdd k = m
  fin_cases m <;> [exact Or.inl rfl; exact Or.inr rfl]

/-- A hom out of `CyclicGroup n` is determined by its value at the generator `ofAdd 1`. -/
private lemma cyclicHom_ext
    {n : Nat} [NeZero n] {G : Type*} [Group G]
    (ψ : CyclicGroup n →* G) {a : G} (ha : a ^ n = 1)
    (h_gen : ψ (Multiplicative.ofAdd (1 : ZMod n)) = a) :
    ψ = cyclicHom n a ha := by
  refine MonoidHom.ext fun x => ?_
  rw [cyclicHom_apply_eq_zpow, ← h_gen, ← ψ.map_zpow]
  congr 1
  change Multiplicative.ofAdd (Multiplicative.toAdd x) =
    Multiplicative.ofAdd (((Multiplicative.toAdd x).val : ℤ) • (1 : ZMod n))
  congr 1
  rw [zsmul_eq_mul, mul_one]
  exact_mod_cast (ZMod.natCast_zmod_val _).symm

/-- `MulAut (CyclicGroup 3)` has exactly two elements: identity and inversion. -/
private lemma mulAut_cyclicGroup_three_cases (a : MulAut (CyclicGroup 3)) :
    a = 1 ∨ a = MulEquiv.inv (CyclicGroup 3) := by
  revert a; decide

/-- Step 3 (dihedral identification): `C₃ ⋊_inv C₂ ≃* D₃`.
The map: `(c, 1) ↦ r(toAdd c)`, `(c, k) ↦ sr(-toAdd c)` for `k ≠ 1`. -/
private def dihedralThree_iso_sdp :
    CyclicGroup 3 ⋊[c2OnCqInv 3] CyclicGroup 2 ≃* DihedralGroup 3 where
  toFun x :=
    if x.right = 1 then
      DihedralGroup.r (Multiplicative.toAdd x.left)
    else
      DihedralGroup.sr (-Multiplicative.toAdd x.left)
  invFun d :=
    match d with
    | DihedralGroup.r i => ⟨Multiplicative.ofAdd i, 1⟩
    | DihedralGroup.sr i =>
        ⟨Multiplicative.ofAdd (-i), Multiplicative.ofAdd (1 : ZMod 2)⟩
  left_inv := by
    rintro ⟨c, k⟩
    rcases cyclicGroup_two_cases k with hk | hk <;> subst hk
    · rfl
    · ext
      · change Multiplicative.ofAdd (-(-Multiplicative.toAdd c)) = c
        rw [neg_neg]; rfl
      · rfl
  right_inv := by
    rintro (i | i)
    · rfl
    · change DihedralGroup.sr (-(-i)) = DihedralGroup.sr i
      rw [neg_neg]
  map_mul' := by
    rintro ⟨c₁, k₁⟩ ⟨c₂, k₂⟩
    have h_inv : ∀ c : CyclicGroup 3,
        (c2OnCqInv 3) (Multiplicative.ofAdd (1 : ZMod 2)) c = c⁻¹ := fun c => by
      rw [c2OnCqInv_apply]; rfl
    rcases cyclicGroup_two_cases k₁ with hk1 | hk1 <;>
      rcases cyclicGroup_two_cases k₂ with hk2 | hk2 <;>
      subst hk1 <;> subst hk2 <;>
      simp only [SemidirectProduct.mul_def, h_inv, map_one, MulAut.one_apply,
        mul_one, one_mul]
    · rfl
    · change DihedralGroup.sr (-(Multiplicative.toAdd c₁ + Multiplicative.toAdd c₂)) =
          DihedralGroup.sr (-Multiplicative.toAdd c₂ - Multiplicative.toAdd c₁)
      congr 1; ring
    · change DihedralGroup.sr
              (-(Multiplicative.toAdd c₁ + -Multiplicative.toAdd c₂)) =
          DihedralGroup.sr (-Multiplicative.toAdd c₁ + Multiplicative.toAdd c₂)
      congr 1; ring
    · change DihedralGroup.r (Multiplicative.toAdd c₁ + -Multiplicative.toAdd c₂) =
          DihedralGroup.r (-Multiplicative.toAdd c₂ - -Multiplicative.toAdd c₁)
      congr 1; ring

/-- The canonical iso `CyclicGroup 2 ≃* MulAut (CyclicGroup 3)`, sending the generator
to inversion. Built by upgrading `c2OnCqInv 3` via bijectivity. -/
private def c2_mulEquiv_mulAutC3 : CyclicGroup 2 ≃* MulAut (CyclicGroup 3) := by
  sorry

/-- For any non-trivial action `φ : (C₂)³ →* MulAut(C₃)`, the basis-change automorphism
of `(C₂)³` that lines `ker φ` up with the standard `{1} × (C₂)²` hyperplane. -/
private def c3_sdp_c2cubed_basis_change
    {φ : (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) →* MulAut (CyclicGroup 3)}
    (h : φ ≠ 1) :
    (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) ≃*
      (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) := by
  sorry

/-- The basis change transports `φ` to `(c2OnCqInv 3) ∘ fst`. -/
private lemma c3_sdp_c2cubed_basis_change_eq
    {φ : (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) →* MulAut (CyclicGroup 3)}
    (h : φ ≠ 1) :
    ((c2OnCqInv 3).comp
        (MonoidHom.fst (CyclicGroup 2) (CyclicGroup 2 × CyclicGroup 2))).comp
      (c3_sdp_c2cubed_basis_change h).toMonoidHom = φ := by
  sorry

/-- Step 1 (basis change): any non-trivial action `φ` of `(C₂)³` on `C₃` produces a
    semidirect product isomorphic to the same with the standard "first-coord-then-inv"
    action `(c2OnCqInv 3).comp (MonoidHom.fst ..)`. -/
private def c3_sdp_c2cubed_iso_standard
    {φ : (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) →* MulAut (CyclicGroup 3)}
    (h_nontriv : φ ≠ 1) :
    CyclicGroup 3 ⋊[φ] (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) ≃*
      CyclicGroup 3 ⋊[(c2OnCqInv 3).comp
                      (MonoidHom.fst (CyclicGroup 2) (CyclicGroup 2 × CyclicGroup 2))]
                    (CyclicGroup 2 × (CyclicGroup 2 × CyclicGroup 2)) :=
  SemidirectProduct.congr (MulEquiv.refl _) (c3_sdp_c2cubed_basis_change h_nontriv) (by
    intro g
    have h := DFunLike.ext_iff.mp (c3_sdp_c2cubed_basis_change_eq h_nontriv) g
    ext n
    simp only [MulEquiv.trans_apply, MulEquiv.refl_apply]
    exact (congrArg (fun a : MulAut _ => a n) h).symm)

/-- Any non-trivial action `φ` of `C₂³` on `C₃` gives `C₃ ⋊[φ] C₂³` isomorphic to `D₃ × V`. -/
private def c3_sdp_c2cubed_nontrivial
    {φ : (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) →* MulAut (CyclicGroup 3)}
    (h_nontriv : φ ≠ 1) :
    CyclicGroup 3 ⋊[φ] (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) ≃*
      DihedralGroup 3 × (CyclicGroup 2 × CyclicGroup 2) :=
  -- Step 1: transport `φ` into "first-coord-then-inv" form
  (c3_sdp_c2cubed_iso_standard h_nontriv).trans <|
  -- Step 2: split off the trailing `C₂ × C₂` as a direct factor
  (sdp_prodEquivOfFstAction (c2OnCqInv 3)).trans <|
  -- Step 3: identify the surviving `C₃ ⋊_inv C₂` as `D₃`
  dihedralThree_iso_sdp.prodCongr (MulEquiv.refl _)

/-- The only non-trivial homomorphism `CyclicGroup 8 →* MulAut (CyclicGroup 3)` is
    `c8OnCqInv 3` (inversion on the generator). -/
private lemma c8_to_mulAutC3_nontrivial_eq
    {ψ : CyclicGroup 8 →* MulAut (CyclicGroup 3)} (h_nontriv : ψ ≠ 1) :
    ψ = c8OnCqInv 3 := by
  have h_inv_pow : (MulEquiv.inv (CyclicGroup 3)) ^ 8 = 1 := by
    change MulEquiv.inv (CyclicGroup 3) ^ (2 * 4) = 1
    rw [pow_mul, inv_aut_pow_two_eq_one]; exact one_pow 4
  have h_gen : ψ (Multiplicative.ofAdd (1 : ZMod 8)) = MulEquiv.inv (CyclicGroup 3) := by
    rcases mulAut_cyclicGroup_three_cases (ψ (Multiplicative.ofAdd (1 : ZMod 8))) with h1 | hinv
    · refine absurd (?_ : ψ = 1) h_nontriv
      rw [cyclicHom_ext ψ (one_pow 8) h1]; ext x
      rw [cyclicHom_apply_eq_zpow]; simp
    · exact hinv
  rw [cyclicHom_ext ψ h_inv_pow h_gen]; rfl

/-- Non-trivial-action branch of the normal-Sylow-3 classification. Given a
    semidirect-product iso `↥P ⋊[φ] ↥K ≃* G` with `|P| = 3` and `|K| = 8`,
    dispatch on `order8_classification` of `K`. Six of the seven possible
    iso classes are now named:
    - `K = C_8`                       →  `C_3 ⋊ C_8`
    - `K = C_4 × C_2`, `ker φ = C_4`  →  `D_3 × C_4`
    - `K = C_4 × C_2`, `ker φ = V_4`  →  `C_2 × Q_12`
    - `K = C_2^3`,    `ker φ = V_4`  →  `D_3 × V_4`
    - `K = D_4`,      `ker φ = C_4`  →  `D_12`
    - `K = Q_8`,      `ker φ = C_4`  →  `Q_24`

    The remaining target — `(C_6 × C_2) ⋊ C_2` from `K = D_4` with kernel V_4 —
    has no Mathlib name and needs a new def in `SmallGroupsLibrary`; for now it
    sits under the trailing `True`. -/
private lemma order24_1_sylow3_nontrivial
    {G : Type*} [Group G]
    {P K : Subgroup G} (h_P_card : Nat.card ↥P = 3) (hK_card : Nat.card ↥K = 8)
    {φ : ↥K →* MulAut ↥P} (h_iso : ↥P ⋊[φ] ↥K ≃* G) (h_phi_nontriv : φ ≠ 1) :
    Nonempty (G ≃* CyclicGroup 3 ⋊[c8OnCqInv 3] CyclicGroup 8) ∨
    Nonempty (G ≃* DihedralGroup 3 × CyclicGroup 4) ∨
    Nonempty (G ≃* CyclicGroup 2 × QuaternionGroup 3) ∨
    Nonempty (G ≃* DihedralGroup 3 × (CyclicGroup 2 × CyclicGroup 2)) ∨
    Nonempty (G ≃* DihedralGroup 12) ∨
    Nonempty (G ≃* QuaternionGroup 6) ∨
    True := by
  haveI : IsCyclic ↥P := isCyclic_of_prime_card h_P_card
  have eP : ↥P ≃* CyclicGroup 3 :=
    mulEquivOfCyclicCardEq (h_P_card.trans (card_cyclicGroup 3).symm)
  rcases order8_classification (G := ↥K) hK_card with hC8 | hC4C2 | hC2sq3 | hD4 | hQ8
  · -- K ≃* C_8: target `C_3 ⋊[c8OnCqInv 3] C_8`
    obtain ⟨eK⟩ := hC8
    have h_psi_eq := c8_to_mulAutC3_nontrivial_eq
      (transported_action_ne_one eP eK h_phi_nontriv)
    let : G ≃* CyclicGroup 3 ⋊[c8OnCqInv 3] CyclicGroup 8 :=
      h_iso.symm.trans (h_psi_eq ▸ SemidirectProduct.congr' eP eK)
    tauto
  · -- K ≃* C_4 × C_2: two sub-cases by `ker φ`
    --   ker = C_4  → D_3 × C_4
    --   ker = V_4  → C_2 × Q_12
    sorry
  · -- K ≃* C_2^3: target `D_3 × V_4`
    obtain ⟨eK⟩ := hC2sq3
    let : G ≃* DihedralGroup 3 × (CyclicGroup 2 × CyclicGroup 2) :=
      h_iso.symm.trans <|
      (SemidirectProduct.congr' eP eK).trans <|
      c3_sdp_c2cubed_nontrivial (transported_action_ne_one eP eK h_phi_nontriv)
    tauto
  · -- K ≃* D_4: two sub-cases by `ker φ`
    --   ker = rotation C_4  → D_12
    --   ker = reflection V_4 → (C_6 × C_2) ⋊ C_2 (needs def; lands in True)
    sorry
  · -- K ≃* Q_8: target Q_24
    sorry

/-- A group of order `24` with a unique Sylow 3-subgroup is isomorphic to one of
    the 12 normal-Sylow-3 groups (5 from a trivial conjugation action, 7 from a
    non-trivial action). The precondition is equivalent to having a normal Sylow
    3-subgroup.

    The 5 trivial-action targets are wired up via `order24_1_sylow3_trivial`; the
    7 non-trivial-action targets are stubbed in `order24_1_sylow3_nontrivial` (6
    named + 1 under a trailing `True` placeholder). -/
lemma order24_1_sylow3 {G : Type*} [Group G] (h : Nat.card G = 24)
    (h_n3 : Nat.card (Sylow 3 G) = 1) :
    (Nonempty (G ≃* CyclicGroup 3 × CyclicGroup 8) ∨
     Nonempty (G ≃* CyclicGroup 3 × (CyclicGroup 4 × CyclicGroup 2)) ∨
     Nonempty (G ≃* CyclicGroup 3 × (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2)) ∨
     Nonempty (G ≃* CyclicGroup 3 × DihedralGroup 4) ∨
     Nonempty (G ≃* CyclicGroup 3 × QuaternionGroup 2)) ∨
    (Nonempty (G ≃* CyclicGroup 3 ⋊[c8OnCqInv 3] CyclicGroup 8) ∨
     Nonempty (G ≃* DihedralGroup 3 × CyclicGroup 4) ∨
     Nonempty (G ≃* CyclicGroup 2 × QuaternionGroup 3) ∨
     Nonempty (G ≃* DihedralGroup 3 × (CyclicGroup 2 × CyclicGroup 2)) ∨
     Nonempty (G ≃* DihedralGroup 12) ∨
     Nonempty (G ≃* QuaternionGroup 6) ∨
     True) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; decide)
  -- The unique Sylow 3-subgroup is normal in G
  haveI : Subsingleton (Sylow 3 G) := (Nat.card_eq_one_iff_unique.mp h_n3).1
  let P : Sylow 3 G := default
  haveI hPnormal : (↑P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
  -- |P| = 3 and [G : P] = 8
  have h_P_card : Nat.card ↥(P : Subgroup G) = 3 := by
    have := sylow_card_eq (p := 3) (q := 2) (by decide)
      (show Nat.card G = 3 ^ 1 * 2 ^ 3 by rw [h]; ring) P
    simpa using this
  have h_P_idx : (↑P : Subgroup G).index = 8 := by
    have := sylow_index_eq (p := 3) (q := 2) (by decide)
      (show Nat.card G = 3 ^ 1 * 2 ^ 3 by rw [h]; ring) P
    simpa using this
  -- Schur-Zassenhaus: a complement K of order 8 exists
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime
    (N := (↑P : Subgroup G)) (by rw [h_P_card, h_P_idx]; decide)
  -- Isomorphism `P ⋊[conjugation] K ≃* G`
  have h_iso := SemidirectProduct.mulEquivSubgroup hK
  -- |K| = 8
  have hK_card : Nat.card ↥K = 8 := by
    have h1 : Nat.card G = Nat.card ↥(↑P : Subgroup G) * Nat.card ↥K := by
      have heq := Nat.card_congr h_iso.toEquiv
      rw [SemidirectProduct.card] at heq
      exact heq.symm
    rw [h_P_card, h] at h1
    omega
  -- Conjugation action φ : K →* MulAut P
  let φ : ↥K →* MulAut ↥(↑P : Subgroup G) :=
    (↑P : Subgroup G).normalizerMonoidHom.comp
      (Subgroup.inclusion (by simp [Subgroup.normalizer_eq_top]))
  classical
  by_cases h_triv : φ = 1
  · -- Trivial action: extract `G ≃* C_3 × K`, dispatch via the trivial sub-lemma
    have h_iso_one :
        ((↑P : Subgroup G) ⋊[(1 : ↥K →* MulAut ↥(↑P : Subgroup G))] ↥K) ≃* G := by
      rw [← h_triv]
      exact h_iso
    have h_g_to_prod : G ≃* ↥(↑P : Subgroup G) × ↥K :=
      (SemidirectProduct.mulEquivProd.symm.trans h_iso_one).symm
    haveI : IsCyclic ↥(↑P : Subgroup G) := isCyclic_of_prime_card h_P_card
    have hP_iso : ↥(↑P : Subgroup G) ≃* CyclicGroup 3 :=
      mulEquivOfCyclicCardEq (h_P_card.trans (card_cyclicGroup 3).symm)
    have h_g_clean : G ≃* CyclicGroup 3 × ↥K :=
      h_g_to_prod.trans (hP_iso.prodCongr (MulEquiv.refl _))
    exact Or.inl (order24_1_sylow3_trivial h_g_clean hK_card)
  · -- Non-trivial action: pass setup state to the sub-lemma
    exact Or.inr (order24_1_sylow3_nontrivial h_P_card hK_card h_iso h_triv)

/-- A group of order `24` with four Sylow 3-subgroups is isomorphic to some group.
    The precondition is equivalent to not having a normal Sylow 3-subgroup. -/
lemma order24_4_sylow3 {G : Type*} [Group G] (h : Nat.card G = 24)
    (h_n3 : Nat.card (Sylow 3 G) = 4) : True := by
  sorry

/-- A group of order `24` is isomorphic to some group. -/
theorem order24_classification {G : Type*} [Group G] (h : Nat.card G = 24) :
    True := by
  rcases sylow3_24 h with h_n3_1 | h_n3_4
  · -- order24_1_sylow3 returns `(5-way trivial) ∨ (5-way Mathlib non-trivial ∨ True)`
    rcases order24_1_sylow3 h h_n3_1 with
      (_ | _ | _ | _ | _) | (_ | _ | _ | _ | _ | _ | _) <;> trivial
  · exact order24_4_sylow3 h h_n3_4
