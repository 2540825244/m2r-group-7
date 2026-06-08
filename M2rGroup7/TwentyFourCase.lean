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
  revert k; decide

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
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

/-- The canonical iso `CyclicGroup 2 ≃* MulAut (CyclicGroup 3)`, sending the generator
to inversion. -/
private noncomputable def c2_mulEquiv_mulAutC3 : CyclicGroup 2 ≃* MulAut (CyclicGroup 3) := by
  have h_gen : c2OnCqInv 3 (Multiplicative.ofAdd 1) = MulEquiv.inv (CyclicGroup 3) := by
    rw [c2OnCqInv_apply]; rfl
  have h_inv_ne : (MulEquiv.inv (CyclicGroup 3)) ≠ 1 := fun h =>
    absurd (DFunLike.ext_iff.mp h (Multiplicative.ofAdd (1 : ZMod 3))) (by decide)
  refine MulEquiv.ofBijective (c2OnCqInv 3) ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    rcases cyclicGroup_two_cases x with rfl | rfl
    · rfl
    · exact absurd (h_gen.symm.trans hx) h_inv_ne
  · intro a
    rcases mulAut_cyclicGroup_three_cases a with h | h
    · exact ⟨1, by rw [map_one, h]⟩
    · exact ⟨Multiplicative.ofAdd 1, by rw [h_gen, h]⟩

/-- Two homomorphisms out of `(C₂)³` agreeing on the three standard generators are equal. -/
private lemma c2_3_hom_ext {H : Type*} [Group H]
    {f g : (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) →* H}
    (h1 : f (Multiplicative.ofAdd 1, 1, 1) = g (Multiplicative.ofAdd 1, 1, 1))
    (h2 : f (1, Multiplicative.ofAdd 1, 1) = g (1, Multiplicative.ofAdd 1, 1))
    (h3 : f (1, 1, Multiplicative.ofAdd 1) = g (1, 1, Multiplicative.ofAdd 1)) :
    f = g := by
  ext ⟨x, y, z⟩
  have key : (x, y, z) =
      ((x, 1, 1) : CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) * (1, y, 1) * (1, 1, z) := by
    ext <;> simp
  have h_one : ((1, 1, 1) : CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) = 1 := rfl
  rw [key, f.map_mul, f.map_mul, g.map_mul, g.map_mul]
  rcases cyclicGroup_two_cases x with rfl | rfl <;>
    rcases cyclicGroup_two_cases y with rfl | rfl <;>
    rcases cyclicGroup_two_cases z with rfl | rfl <;>
    simp [h_one, f.map_one, g.map_one, h1, h2, h3]

/-- Swap the first two coordinates of `(C₂)³`. -/
private def c2_3_swap_12 :
    (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) ≃*
      (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) where
  toFun := fun ⟨x, y, z⟩ => ⟨y, x, z⟩
  invFun := fun ⟨x, y, z⟩ => ⟨y, x, z⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Swap the first and third coordinates of `(C₂)³`. -/
private def c2_3_swap_13 :
    (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) ≃*
      (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) where
  toFun := fun ⟨x, y, z⟩ => ⟨z, y, x⟩
  invFun := fun ⟨x, y, z⟩ => ⟨z, y, x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Add the second coordinate to the first in `(C₂)³`. -/
private def c2_3_add_2_to_1 :
    (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) ≃*
      (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) where
  toFun := fun ⟨x, y, z⟩ => ⟨x * y, y, z⟩
  invFun := fun ⟨x, y, z⟩ => ⟨x * y, y, z⟩
  left_inv _ := by simp [mul_assoc, sq_eq_one_cyclicGroup2]
  right_inv _ := by simp [mul_assoc, sq_eq_one_cyclicGroup2]
  map_mul' _ _ := by ext <;> simp [mul_mul_mul_comm]

/-- Add the third coordinate to the first in `(C₂)³`. -/
private def c2_3_add_3_to_1 :
    (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) ≃*
      (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) where
  toFun := fun ⟨x, y, z⟩ => ⟨x * z, y, z⟩
  invFun := fun ⟨x, y, z⟩ => ⟨x * z, y, z⟩
  left_inv _ := by simp [mul_assoc, sq_eq_one_cyclicGroup2]
  right_inv _ := by simp [mul_assoc, sq_eq_one_cyclicGroup2]
  map_mul' _ _ := by ext <;> simp [mul_mul_mul_comm]

/-- Core linear-algebra fact: any non-trivial `χ : (C₂)³ →* C₂` admits a basis-change
automorphism `α` of `(C₂)³` such that `fst ∘ α = χ`. -/
private lemma fst_basis_change_exists
    {χ : (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) →* CyclicGroup 2}
    (h : χ ≠ 1) :
    ∃ α : (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) ≃*
          (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2),
      (MonoidHom.fst (CyclicGroup 2) (CyclicGroup 2 × CyclicGroup 2)).comp
        α.toMonoidHom = χ := by
  obtain ⟨a, ha⟩ : ∃ a, a = χ (Multiplicative.ofAdd 1, 1, 1) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = χ (1, Multiplicative.ofAdd 1, 1) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = χ (1, 1, Multiplicative.ofAdd 1) := ⟨_, rfl⟩
  -- Reusable: given α matching (a, b, c) on the three generators (verified by `rfl`),
  -- package the existential.
  have close (α : (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) ≃*
                  (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2))
      (h1 : (α (Multiplicative.ofAdd 1, 1, 1)).1 = a := by rfl)
      (h2 : (α (1, Multiplicative.ofAdd 1, 1)).1 = b := by rfl)
      (h3 : (α (1, 1, Multiplicative.ofAdd 1)).1 = c := by rfl) :
      ∃ β : (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) ≃*
            (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2),
        (MonoidHom.fst (CyclicGroup 2) (CyclicGroup 2 × CyclicGroup 2)).comp β.toMonoidHom = χ :=
    ⟨α, c2_3_hom_ext
      (f := (MonoidHom.fst (CyclicGroup 2) (CyclicGroup 2 × CyclicGroup 2)).comp α.toMonoidHom)
      (h1.trans ha) (h2.trans hb) (h3.trans hc)⟩
  rcases cyclicGroup_two_cases a with rfl | rfl <;>
    rcases cyclicGroup_two_cases b with rfl | rfl <;>
    rcases cyclicGroup_two_cases c with rfl | rfl
  · exact absurd (c2_3_hom_ext ha.symm hb.symm hc.symm) h
  · exact close c2_3_swap_13
  · exact close c2_3_swap_12
  · exact close (c2_3_swap_13.trans c2_3_add_2_to_1)
  · exact close (MulEquiv.refl _)
  · exact close c2_3_add_3_to_1
  · exact close c2_3_add_2_to_1
  · exact close (c2_3_add_3_to_1.trans c2_3_add_2_to_1)

/-- Reduces to `fst_basis_change_exists` via post-composition with the iso
`c2_mulEquiv_mulAutC3.symm`. -/
private lemma c3_sdp_c2cubed_basis_change_exists
    {φ : (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) →* MulAut (CyclicGroup 3)}
    (h : φ ≠ 1) :
    ∃ α : (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) ≃*
          (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2),
      ((c2OnCqInv 3).comp
          (MonoidHom.fst (CyclicGroup 2) (CyclicGroup 2 × CyclicGroup 2))).comp
        α.toMonoidHom = φ := by
  obtain ⟨α, hα⟩ := fst_basis_change_exists
    (χ := c2_mulEquiv_mulAutC3.symm.toMonoidHom.comp φ)
    fun heq => h <| MonoidHom.ext fun p =>
      c2_mulEquiv_mulAutC3.symm.map_eq_one_iff.mp (DFunLike.ext_iff.mp heq p)
  refine ⟨α, ?_⟩
  rw [MonoidHom.comp_assoc, hα]
  exact MonoidHom.ext fun p => c2_mulEquiv_mulAutC3.apply_symm_apply (φ p)

/-- The basis-change automorphism (chosen non-constructively from
`c3_sdp_c2cubed_basis_change_exists`). -/
private noncomputable def c3_sdp_c2cubed_basis_change
    {φ : (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) →* MulAut (CyclicGroup 3)}
    (h : φ ≠ 1) :
    (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) ≃*
      (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) :=
  (c3_sdp_c2cubed_basis_change_exists h).choose

/-- The basis change transports `φ` to `(c2OnCqInv 3) ∘ fst`. -/
private lemma c3_sdp_c2cubed_basis_change_eq
    {φ : (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) →* MulAut (CyclicGroup 3)}
    (h : φ ≠ 1) :
    ((c2OnCqInv 3).comp
        (MonoidHom.fst (CyclicGroup 2) (CyclicGroup 2 × CyclicGroup 2))).comp
      (c3_sdp_c2cubed_basis_change h).toMonoidHom = φ :=
  (c3_sdp_c2cubed_basis_change_exists h).choose_spec

/-- Step 1 (basis change): any non-trivial action `φ` of `(C₂)³` on `C₃` produces a
    semidirect product isomorphic to the same with the standard "first-coord-then-inv"
    action `(c2OnCqInv 3).comp (MonoidHom.fst ..)`. -/
private noncomputable def c3_sdp_c2cubed_iso_standard
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
private noncomputable def c3_sdp_c2cubed_nontrivial
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

/-- The standard non-trivial action `Q_8 →* MulAut (C_3)`: sends `a i` to identity and
`xa i` to inversion. Its kernel is `⟨a⟩ ≃ C_4`. -/
private def q8OnC3Inv : QuaternionGroup 2 →* MulAut (CyclicGroup 3) where
  toFun := fun
    | .a _ => 1
    | .xa _ => MulEquiv.inv (CyclicGroup 3)
  map_one' := rfl
  map_mul' p q := by
    rcases p with i | i <;> rcases q with j | j <;> ext c <;> revert c i j <;> decide

/-- Two homomorphisms out of `Q_8` agreeing on the generators `a 1` and `xa 0` are equal.
(`Q_8` is generated by these two elements.) -/
private lemma q8_hom_ext {H : Type*} [Group H]
    {f g : QuaternionGroup 2 →* H}
    (h1 : f (.a 1) = g (.a 1))
    (h2 : f (.xa 0) = g (.xa 0)) :
    f = g := by
  have hpow : ∀ i : ZMod 4, (.a i : QuaternionGroup 2) = .a 1 ^ i.val := by decide
  have hxa : ∀ i : ZMod 4, (.xa i : QuaternionGroup 2) = .xa 0 * .a 1 ^ i.val := by decide
  ext x
  rcases x with i | i
  · rw [hpow, f.map_pow, g.map_pow, h1]
  · rw [hxa, f.map_mul, g.map_mul, f.map_pow, g.map_pow, h1, h2]

/-- The Aut of `Q_8` swapping the `a` and `xa 0` axes (involution sending `a 1 ↔ xa 0`).

`a 0 ↦ a 0, a 1 ↦ xa 0, a 2 ↦ a 2, a 3 ↦ xa 2,
 xa 0 ↦ a 1, xa 1 ↦ xa 3, xa 2 ↦ a 3, xa 3 ↦ xa 1` -/
private def q8_swap_a_xa : QuaternionGroup 2 ≃* QuaternionGroup 2 :=
  let f : QuaternionGroup 2 → QuaternionGroup 2
    | .a 0 => .a 0  | .a 1 => .xa 0 | .a 2 => .a 2  | .a 3 => .xa 2
    | .xa 0 => .a 1 | .xa 1 => .xa 3 | .xa 2 => .a 3 | .xa 3 => .xa 1
  { toFun := f, invFun := f, left_inv := by decide, right_inv := by decide,
    map_mul' := by decide }

/-- The order-4 Aut of `Q_8` sending `a 1 ↦ xa 1` and fixing `xa 0`.

`a 0 ↦ a 0, a 1 ↦ xa 1, a 2 ↦ a 2, a 3 ↦ xa 3,
 xa 0 ↦ xa 0, xa 1 ↦ a 3, xa 2 ↦ xa 2, xa 3 ↦ a 1` -/
private def q8_a_to_xa1 : QuaternionGroup 2 ≃* QuaternionGroup 2 where
  toFun
    | .a 0 => .a 0  | .a 1 => .xa 1 | .a 2 => .a 2  | .a 3 => .xa 3
    | .xa 0 => .xa 0 | .xa 1 => .a 3 | .xa 2 => .xa 2 | .xa 3 => .a 1
  invFun
    | .a 0 => .a 0  | .a 1 => .xa 3 | .a 2 => .a 2  | .a 3 => .xa 1
    | .xa 0 => .xa 0 | .xa 1 => .a 1 | .xa 2 => .xa 2 | .xa 3 => .a 3
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

/-- Existence of a basis-change automorphism of `Q_8` transporting any non-trivial
`φ : Q_8 →* MulAut(C_3)` to the standard `q8OnC3Inv`. -/
private lemma q8_basis_change_exists
    {φ : QuaternionGroup 2 →* MulAut (CyclicGroup 3)} (h : φ ≠ 1) :
    ∃ α : QuaternionGroup 2 ≃* QuaternionGroup 2,
      q8OnC3Inv.comp α.toMonoidHom = φ := by
  obtain ⟨a, ha⟩ : ∃ a, a = φ (.a 1) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = φ (.xa 0) := ⟨_, rfl⟩
  have close (α : QuaternionGroup 2 ≃* QuaternionGroup 2)
      (h1 : q8OnC3Inv (α (.a 1)) = a := by rfl)
      (h2 : q8OnC3Inv (α (.xa 0)) = b := by rfl) :
      ∃ β : QuaternionGroup 2 ≃* QuaternionGroup 2, q8OnC3Inv.comp β.toMonoidHom = φ :=
    ⟨α, q8_hom_ext (f := q8OnC3Inv.comp α.toMonoidHom) (h1.trans ha) (h2.trans hb)⟩
  rcases mulAut_cyclicGroup_three_cases a with rfl | rfl <;>
    rcases mulAut_cyclicGroup_three_cases b with rfl | rfl
  · -- (1, 1): φ is trivial, contradicting `h`.
    exact absurd (q8_hom_ext ha.symm hb.symm) h
  · -- (1, inv): φ = q8OnC3Inv. Take α = id.
    exact close (MulEquiv.refl _)
  · -- (inv, 1): ker φ = ⟨xa 0⟩. Take α = q8_swap_a_xa.
    exact close q8_swap_a_xa
  · -- (inv, inv): ker φ = ⟨xa 1⟩. Take α = q8_a_to_xa1.
    exact close q8_a_to_xa1

/-- The basis-change automorphism (chosen non-constructively). -/
private noncomputable def q8_basis_change
    {φ : QuaternionGroup 2 →* MulAut (CyclicGroup 3)} (h : φ ≠ 1) :
    QuaternionGroup 2 ≃* QuaternionGroup 2 :=
  (q8_basis_change_exists h).choose

/-- The basis change transports `φ` to `q8OnC3Inv`. -/
private lemma q8_basis_change_eq
    {φ : QuaternionGroup 2 →* MulAut (CyclicGroup 3)} (h : φ ≠ 1) :
    q8OnC3Inv.comp (q8_basis_change h).toMonoidHom = φ :=
  (q8_basis_change_exists h).choose_spec

/-- Step 1 (basis change): any non-trivial action `φ` of `Q_8` on `C_3` produces a
semidirect product isomorphic to the same with the standard action `q8OnC3Inv`. -/
private noncomputable def c3_sdp_q8_iso_standard
    {φ : QuaternionGroup 2 →* MulAut (CyclicGroup 3)} (h_nontriv : φ ≠ 1) :
    CyclicGroup 3 ⋊[φ] QuaternionGroup 2 ≃*
      CyclicGroup 3 ⋊[q8OnC3Inv] QuaternionGroup 2 :=
  SemidirectProduct.congr (MulEquiv.refl _) (q8_basis_change h_nontriv) (by
    intro g
    have h := DFunLike.ext_iff.mp (q8_basis_change_eq h_nontriv) g
    ext n
    simp only [MulEquiv.trans_apply, MulEquiv.refl_apply]
    exact (congrArg (fun a : MulAut _ => a n) h).symm)

/-- Step 2 (identification): `C_3 ⋊[q8OnC3Inv] Q_8 ≃* Q_24`.

The iso sends `(c, a i) ↦ a (4c + 3i)` and `(c, xa i) ↦ xa (3i - 4c)`, where `c : ZMod 3`
and `i : ZMod 4` are cast to `ZMod 12`. -/
private def c3_sdp_q8_iso_q24 :
    CyclicGroup 3 ⋊[q8OnC3Inv] QuaternionGroup 2 ≃* QuaternionGroup 6 where
  toFun x :=
    let c : ZMod 12 := ((Multiplicative.toAdd x.left : ZMod 3).val : ZMod 12)
    match x.right with
    | .a i => .a (4 * c + 3 * ((i.val : ZMod 12)))
    | .xa i => .xa (3 * ((i.val : ZMod 12)) - 4 * c)
  invFun y :=
    match y with
    | .a j =>
        ⟨Multiplicative.ofAdd ((j.val : ZMod 3)),
         .a ((-j.val : ZMod 4))⟩
    | .xa j =>
        ⟨Multiplicative.ofAdd ((-j.val : ZMod 3)),
         .xa ((-j.val : ZMod 4))⟩
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

/-- Any non-trivial action of `Q_8` on `C_3` gives `C_3 ⋊[φ] Q_8 ≃* Q_24`, by combining
the basis-change `c3_sdp_q8_iso_standard` with the identification `c3_sdp_q8_iso_q24`. -/
private noncomputable def c3_sdp_q8_nontrivial
    {φ : QuaternionGroup 2 →* MulAut (CyclicGroup 3)} (h_nontriv : φ ≠ 1) :
    CyclicGroup 3 ⋊[φ] QuaternionGroup 2 ≃* QuaternionGroup 6 :=
  (c3_sdp_q8_iso_standard h_nontriv).trans c3_sdp_q8_iso_q24

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
    obtain ⟨eK⟩ := hQ8
    let : G ≃* QuaternionGroup 6 :=
      h_iso.symm.trans <|
      (SemidirectProduct.congr' eP eK).trans <|
      c3_sdp_q8_nontrivial (transported_action_ne_one eP eK h_phi_nontriv)
    tauto

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
