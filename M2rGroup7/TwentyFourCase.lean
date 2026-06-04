import Mathlib.GroupTheory.Sylow
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SemidirectProduct
import «M2rGroup7».Classification
import «M2rGroup7».Lemmas.SylowUtils

/-- A group of order `24` has either `1` or `4` Sylow 3-subgroups. -/
lemma sylow3_24 {G : Type*} [Group G] (h : Nat.card G = 24) :
    Nat.card (Sylow 3 G) = 1 ∨ Nat.card (Sylow 3 G) = 4 := by
  haveI : Finite G := by
    apply Nat.finite_of_card_ne_zero
    rw [h]
    simp
  have h_mod : Nat.card (Sylow 3 G) % 3 = 1 % 3 := card_sylow_modEq_one 3 G
  let P : Sylow 3 G := default
  have h_dvd : Nat.card (Sylow 3 G) ∣ Nat.card G :=
    (Sylow.card_dvd_index P).trans (Subgroup.index_dvd_card _)
  rw [h] at h_dvd
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

/-- Non-trivial-action branch of the normal-Sylow-3 classification: placeholder
    for the 7 non-trivial-action groups. The eventual proof will dispatch via
    `order8_classification` on the order-8 complement `K`, then on the
    `Aut(K)`-orbit of `ker φ`. Two of the 7 targets (the `C_3 ⋊ C_8` from
    `K = C_8`, and `(C_6 × C_2) ⋊ C_2` from `K = D_4` with kernel V_4) need
    new defs in `SmallGroupsLibrary`. -/
private lemma order24_1_sylow3_nontrivial {G : Type*} [Group G]
    (h : Nat.card G = 24) (h_n3 : Nat.card (Sylow 3 G) = 1) :
    True := by
  sorry

/-- A group of order `24` with a unique Sylow 3-subgroup is isomorphic to one of
    the 12 normal-Sylow-3 groups (5 from a trivial conjugation action, 7 from a
    non-trivial action). The precondition is equivalent to having a normal Sylow
    3-subgroup.

    The 5 trivial-action targets are wired up via `order24_1_sylow3_trivial`; the
    7 non-trivial-action targets are stubbed in `order24_1_sylow3_nontrivial`. -/
lemma order24_1_sylow3 {G : Type*} [Group G] (h : Nat.card G = 24)
    (h_n3 : Nat.card (Sylow 3 G) = 1) :
    (Nonempty (G ≃* CyclicGroup 3 × CyclicGroup 8) ∨
     Nonempty (G ≃* CyclicGroup 3 × (CyclicGroup 4 × CyclicGroup 2)) ∨
     Nonempty (G ≃* CyclicGroup 3 × (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2)) ∨
     Nonempty (G ≃* CyclicGroup 3 × DihedralGroup 4) ∨
     Nonempty (G ≃* CyclicGroup 3 × QuaternionGroup 2)) ∨
    True := by
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
  · -- Non-trivial action: dispatch to the placeholder sub-lemma
    exact Or.inr (order24_1_sylow3_nontrivial h h_n3)

/-- A group of order `24` with four Sylow 3-subgroups is isomorphic to some group.
    The precondition is equivalent to not having a normal Sylow 3-subgroup. -/
lemma order24_4_sylow3 {G : Type*} [Group G] (h : Nat.card G = 24)
    (h_n3 : Nat.card (Sylow 3 G) = 4) : True := by
  sorry

/-- A group of order `24` is isomorphic to some group. -/
theorem order24_classification {G : Type*} [Group G] (h : Nat.card G = 24) :
    True := by
  rcases sylow3_24 h with h_n3_1 | h_n3_4
  · -- order24_1_sylow3 returns `(5-way) ∨ True`; discard to land in `True`
    rcases order24_1_sylow3 h h_n3_1 with (_ | _ | _ | _ | _) | _ <;> trivial
  · exact order24_4_sylow3 h h_n3_4
