import Mathlib.GroupTheory.Sylow
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SemidirectProduct
import «M2rGroup7».Order8Classification
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
  -- Each leaf: lift `e : Q ≃* X` to `G ≃* CyclicGroup 3 × X` via `h_iso`, then dispatch.
  have mk : ∀ {X : Type} [Group X],
      Nonempty (Q ≃* X) → Nonempty (G ≃* CyclicGroup 3 × X) :=
    fun ⟨e⟩ => ⟨h_iso.trans ((MulEquiv.refl _).prodCongr e)⟩
  rcases order8_classification (G := Q) hQ_card with h | h | h | h | h <;>
    (have := mk h; tauto)

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

/-- Transport step (basis change): an automorphism `α` of `K` with `ψ ∘ α = φ` induces an
iso of semidirect products `N ⋊[φ] K ≃* N ⋊[ψ] K`. -/
private def sdp_congr_right_of_comp_eq
    {N K : Type*} [Group N] [Group K] {φ ψ : K →* MulAut N}
    (α : K ≃* K) (hα : ψ.comp α.toMonoidHom = φ) :
    N ⋊[φ] K ≃* N ⋊[ψ] K :=
  SemidirectProduct.congr (MulEquiv.refl _) α (by
    intro g
    have h := DFunLike.ext_iff.mp hα g
    ext n
    simp only [MulEquiv.trans_apply, MulEquiv.refl_apply]
    exact (congrArg (fun a : MulAut _ => a n) h).symm)

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
  sdp_congr_right_of_comp_eq (c3_sdp_c2cubed_basis_change h_nontriv)
    (c3_sdp_c2cubed_basis_change_eq h_nontriv)

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
  sdp_congr_right_of_comp_eq (q8_basis_change h_nontriv) (q8_basis_change_eq h_nontriv)

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

-- ── C_4 × C_2 leaf helpers ─────────────────────────────────────────────────
-- The 3 non-trivial homs `(C_4 × C_2) → MulAut(C_3) ≃ C_2` split into two
-- `Aut(C_4 × C_2)`-orbits, giving two output targets: `D_3 × C_4` and `C_2 × Q_12`.

/-- Standard action for the `D_3 × C_4` target: project to the `C_2` factor, then invert. -/
private def c4c2OnC3Inv_via_snd :
    (CyclicGroup 4 × CyclicGroup 2) →* MulAut (CyclicGroup 3) :=
  (c2OnCqInv 3).comp (MonoidHom.snd (CyclicGroup 4) (CyclicGroup 2))

/-- Standard action for the `C_2 × Q_12` target: project to the `C_4` factor, then apply
the order-2 action `c4OnCqInv 3` (which mods out by `C_2` and inverts). -/
private def c4c2OnC3Inv_via_fst_mod2 :
    (CyclicGroup 4 × CyclicGroup 2) →* MulAut (CyclicGroup 3) :=
  (c4OnCqInv 3).comp (MonoidHom.fst (CyclicGroup 4) (CyclicGroup 2))

/-- The Aut of `C_4 × C_2` fixing `(a², 1)` and `(1, b)`, swapping `(a, 1) ↔ (a, b)`.
Lifts the `(inv, inv)` action case to the `(1, inv)` standard form. The map is the
involution `(x, y) ↦ (x, b^((toAdd x).val mod 2) · y)`. -/
private def c4c2_diag_swap :
    (CyclicGroup 4 × CyclicGroup 2) ≃* (CyclicGroup 4 × CyclicGroup 2) :=
  let f : CyclicGroup 4 × CyclicGroup 2 → CyclicGroup 4 × CyclicGroup 2 :=
    fun p =>
      let q : CyclicGroup 2 := Multiplicative.ofAdd ((Multiplicative.toAdd p.1).val : ZMod 2)
      (p.1, q * p.2)
  { toFun := f, invFun := f
    left_inv := by decide
    right_inv := by decide
    map_mul' := by decide }

/-- The iso `C_3 ⋊[c4OnCqInv 3] C_4 ≃* Q_12`, identifying `c ↔ a⁴` and `x ↔ xa 0`.

The map sends `(c^k, x^i) ↦ a (4k + 3(i/2))` for even `i` and `↦ xa (2k + 3(i/2))` for
odd `i` (arithmetic in `ZMod 6`, `i/2` is Nat division). -/
private def c3_sdp_c4_iso_q12 :
    CyclicGroup 3 ⋊[c4OnCqInv 3] CyclicGroup 4 ≃* QuaternionGroup 3 where
  toFun x :=
    let k : ZMod 6 := ((Multiplicative.toAdd x.left).val : ZMod 6)
    let i := (Multiplicative.toAdd x.right).val
    if i % 2 = 0 then .a (4 * k + 3 * ((i / 2 : ℕ) : ZMod 6))
    else .xa (2 * k + 3 * ((i / 2 : ℕ) : ZMod 6))
  invFun y :=
    match y with
    | .a j =>
        ⟨Multiplicative.ofAdd ((j.val : ZMod 3)),
         Multiplicative.ofAdd (if j.val % 2 = 0 then 0 else 2 : ZMod 4)⟩
    | .xa j =>
        ⟨Multiplicative.ofAdd ((2 * j.val : ZMod 3)),
         Multiplicative.ofAdd (if j.val % 2 = 0 then 1 else 3 : ZMod 4)⟩
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

/-- Identification chain for the `via_snd → D_3 × C_4` target: swap `(C_4 × C_2)` to
`(C_2 × C_4)` so the acting factor is first, factor off the trailing `C_4`, then
identify `C_3 ⋊_inv C_2 ≃ D_3`. -/
private def c3_sdp_c4c2_via_snd_iso_d3c4 :
    CyclicGroup 3 ⋊[c4c2OnC3Inv_via_snd] (CyclicGroup 4 × CyclicGroup 2) ≃*
      DihedralGroup 3 × CyclicGroup 4 :=
  (SemidirectProduct.congr (MulEquiv.refl _)
      (MulEquiv.prodComm (M := CyclicGroup 4) (N := CyclicGroup 2))
      (by intro; rfl)).trans <|
  (sdp_prodEquivOfFstAction (c2OnCqInv 3)).trans <|
  dihedralThree_iso_sdp.prodCongr (MulEquiv.refl _)

/-- Identification chain for the `via_fst_mod2 → C_2 × Q_12` target: factor off the
trailing `C_2`, identify the `C_3 ⋊ C_4` factor as `Q_12`, then swap. -/
private def c3_sdp_c4c2_via_fst_mod2_iso_c2q12 :
    CyclicGroup 3 ⋊[c4c2OnC3Inv_via_fst_mod2] (CyclicGroup 4 × CyclicGroup 2) ≃*
      CyclicGroup 2 × QuaternionGroup 3 :=
  (sdp_prodEquivOfFstAction (c4OnCqInv 3)).trans <|
  (c3_sdp_c4_iso_q12.prodCongr (MulEquiv.refl _)).trans <|
  MulEquiv.prodComm (M := QuaternionGroup 3) (N := CyclicGroup 2)

/-- `CyclicGroup 4` has exactly four elements. -/
private lemma cyclicGroup_four_cases (k : CyclicGroup 4) :
    k = 1 ∨ k = Multiplicative.ofAdd (1 : ZMod 4) ∨ k = Multiplicative.ofAdd (2 : ZMod 4) ∨
      k = Multiplicative.ofAdd (3 : ZMod 4) := by
  revert k; decide

/-- Two homomorphisms out of `C_4 × C_2` agreeing on the generators `(a, 1)` and `(1, b)`
are equal. -/
private lemma c4c2_hom_ext {H : Type*} [Group H]
    {f g : (CyclicGroup 4 × CyclicGroup 2) →* H}
    (h1 : f (Multiplicative.ofAdd (1 : ZMod 4), 1) = g (Multiplicative.ofAdd (1 : ZMod 4), 1))
    (h2 : f (1, Multiplicative.ofAdd (1 : ZMod 2)) = g (1, Multiplicative.ofAdd (1 : ZMod 2))) :
    f = g := by
  have sq (φ : (CyclicGroup 4 × CyclicGroup 2) →* H) :
      φ (Multiplicative.ofAdd (2 : ZMod 4), 1) =
        φ (Multiplicative.ofAdd (1 : ZMod 4), 1) * φ (Multiplicative.ofAdd (1 : ZMod 4), 1) := by
    rw [← φ.map_mul]; exact congrArg φ (by decide)
  have cu (φ : (CyclicGroup 4 × CyclicGroup 2) →* H) :
      φ (Multiplicative.ofAdd (3 : ZMod 4), 1) =
        φ (Multiplicative.ofAdd (1 : ZMod 4), 1) * φ (Multiplicative.ofAdd (2 : ZMod 4), 1) := by
    rw [← φ.map_mul]; exact congrArg φ (by decide)
  have split (φ : (CyclicGroup 4 × CyclicGroup 2) →* H) (x : CyclicGroup 4) (y : CyclicGroup 2) :
      φ (x, y) = φ (x, 1) * φ (1, y) := by
    rw [← φ.map_mul]
    exact congrArg φ (by ext <;> simp only [Prod.mk_mul_mk, mul_one, one_mul])
  refine MonoidHom.ext fun ⟨x, y⟩ => ?_
  rw [split f, split g]
  rcases cyclicGroup_four_cases x with rfl | rfl | rfl | rfl <;>
    rcases cyclicGroup_two_cases y with rfl | rfl <;>
      simp only [sq, cu, h1, h2, show ((1, 1) : CyclicGroup 4 × CyclicGroup 2) = 1 from rfl,
        map_one, mul_one, one_mul]

/-- Case-bash on `(φ(a, 1), φ(1, b)) ∈ {1, inv}²` (excluding the trivial case). Three
sub-cases land in the `via_snd` form (using `c4c2_diag_swap` for the `(inv, inv)` case);
one lands in the `via_fst_mod2` form. -/
private lemma c4c2_basis_change_exists
    {φ : (CyclicGroup 4 × CyclicGroup 2) →* MulAut (CyclicGroup 3)} (h : φ ≠ 1) :
    (∃ α : (CyclicGroup 4 × CyclicGroup 2) ≃* (CyclicGroup 4 × CyclicGroup 2),
        c4c2OnC3Inv_via_snd.comp α.toMonoidHom = φ) ∨
    (∃ α : (CyclicGroup 4 × CyclicGroup 2) ≃* (CyclicGroup 4 × CyclicGroup 2),
        c4c2OnC3Inv_via_fst_mod2.comp α.toMonoidHom = φ) := by
  obtain ⟨a, ha⟩ : ∃ a, a = φ (Multiplicative.ofAdd (1 : ZMod 4), 1) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = φ (1, Multiplicative.ofAdd (1 : ZMod 2)) := ⟨_, rfl⟩
  have close_snd (α : (CyclicGroup 4 × CyclicGroup 2) ≃* (CyclicGroup 4 × CyclicGroup 2))
      (h1 : c4c2OnC3Inv_via_snd (α (Multiplicative.ofAdd (1 : ZMod 4), 1)) = a := by decide)
      (h2 : c4c2OnC3Inv_via_snd (α (1, Multiplicative.ofAdd (1 : ZMod 2))) = b := by decide) :
      ∃ α' : (CyclicGroup 4 × CyclicGroup 2) ≃* (CyclicGroup 4 × CyclicGroup 2),
        c4c2OnC3Inv_via_snd.comp α'.toMonoidHom = φ :=
    ⟨α, c4c2_hom_ext (f := c4c2OnC3Inv_via_snd.comp α.toMonoidHom)
      (h1.trans ha) (h2.trans hb)⟩
  have close_fst (α : (CyclicGroup 4 × CyclicGroup 2) ≃* (CyclicGroup 4 × CyclicGroup 2))
      (h1 : c4c2OnC3Inv_via_fst_mod2 (α (Multiplicative.ofAdd (1 : ZMod 4), 1)) = a := by decide)
      (h2 : c4c2OnC3Inv_via_fst_mod2 (α (1, Multiplicative.ofAdd (1 : ZMod 2))) = b := by decide) :
      ∃ α' : (CyclicGroup 4 × CyclicGroup 2) ≃* (CyclicGroup 4 × CyclicGroup 2),
        c4c2OnC3Inv_via_fst_mod2.comp α'.toMonoidHom = φ :=
    ⟨α, c4c2_hom_ext (f := c4c2OnC3Inv_via_fst_mod2.comp α.toMonoidHom)
      (h1.trans ha) (h2.trans hb)⟩
  rcases mulAut_cyclicGroup_three_cases a with rfl | rfl <;>
    rcases mulAut_cyclicGroup_three_cases b with rfl | rfl
  · -- (1, 1): φ is trivial, contradicting `h`.
    exact absurd (c4c2_hom_ext ha.symm hb.symm) h
  · -- (1, inv): ker φ = ⟨(a, 1)⟩. Take α = id.
    exact Or.inl (close_snd (MulEquiv.refl _))
  · -- (inv, 1): ker φ = ⟨(a², 1), (1, b)⟩ = V_4. Take α = id.
    exact Or.inr (close_fst (MulEquiv.refl _))
  · -- (inv, inv): ker φ = ⟨(a, b)⟩. Take α = c4c2_diag_swap.
    exact Or.inl (close_snd c4c2_diag_swap)

/-- Any non-trivial action `φ` of `C_4 × C_2` on `C_3` gives `C_3 ⋊[φ] (C_4 × C_2)`
isomorphic to either `D_3 × C_4` or `C_2 × Q_12`, depending on the iso class of `ker φ`. -/
private lemma c3_sdp_c4c2_nontrivial
    {φ : (CyclicGroup 4 × CyclicGroup 2) →* MulAut (CyclicGroup 3)} (h_nontriv : φ ≠ 1) :
    Nonempty (CyclicGroup 3 ⋊[φ] (CyclicGroup 4 × CyclicGroup 2) ≃*
              DihedralGroup 3 × CyclicGroup 4) ∨
    Nonempty (CyclicGroup 3 ⋊[φ] (CyclicGroup 4 × CyclicGroup 2) ≃*
              CyclicGroup 2 × QuaternionGroup 3) := by
  rcases c4c2_basis_change_exists h_nontriv with ⟨α, hα⟩ | ⟨α, hα⟩
  · let : CyclicGroup 3 ⋊[φ] (CyclicGroup 4 × CyclicGroup 2) ≃*
          DihedralGroup 3 × CyclicGroup 4 :=
      (sdp_congr_right_of_comp_eq α hα).trans c3_sdp_c4c2_via_snd_iso_d3c4
    tauto
  · let : CyclicGroup 3 ⋊[φ] (CyclicGroup 4 × CyclicGroup 2) ≃*
          CyclicGroup 2 × QuaternionGroup 3 :=
      (sdp_congr_right_of_comp_eq α hα).trans c3_sdp_c4c2_via_fst_mod2_iso_c2q12
    tauto

-- ── D_4 leaf helpers ────────────────────────────────────────────────────────
-- The 3 non-trivial homs `D_4 → MulAut(C_3) ≃ C_2` split into two `Aut(D_4)`-orbits:
-- kernel = rotation C_4 gives `D_12`; kernel = a reflection V_4 gives
-- `C_3 ⋊[d4OnCqInv 3] D_4` (which is the `retrieve 24 8` entry itself).

/-- Standard action for the `D_12` target: rotations act trivially, reflections invert.
Its kernel is the rotation subgroup `⟨r⟩ ≃ C_4`. -/
private def d4OnC3Inv_via_refl : DihedralGroup 4 →* MulAut (CyclicGroup 3) where
  toFun := fun
    | .r _ => 1
    | .sr _ => MulEquiv.inv (CyclicGroup 3)
  map_one' := rfl
  map_mul' p q := by
    rcases p with i | i <;> rcases q with j | j <;> ext c <;> revert c i j <;> decide

/-- The outer automorphism of `D_4` fixing rotations and shifting reflections by one.
Swaps the two reflection-V_4 subgroups, lifting the `(inv, inv)` action case to
`d4OnCqInv 3` standard form. -/
private def d4_shift : DihedralGroup 4 ≃* DihedralGroup 4 where
  toFun
    | .r i => .r i
    | .sr i => .sr (i + 1)
  invFun
    | .r i => .r i
    | .sr i => .sr (i - 1)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

/-- The iso `C_3 ⋊[d4OnC3Inv_via_refl] D_4 ≃* D_12`. The rotation part is the CRT iso
`C_3 × C_4 ≃ C_12`: `(c^k, r i) ↦ r (4k + 9i)`; reflections: `(c^k, sr i) ↦ sr (9i - 4k)`
(arithmetic in `ZMod 12`). -/
private def c3_sdp_d4_iso_d12 :
    CyclicGroup 3 ⋊[d4OnC3Inv_via_refl] DihedralGroup 4 ≃* DihedralGroup 12 where
  toFun x :=
    let k : ZMod 12 := ((Multiplicative.toAdd x.left).val : ZMod 12)
    match x.right with
    | .r i => .r (4 * k + 9 * (i.val : ZMod 12))
    | .sr i => .sr (9 * (i.val : ZMod 12) - 4 * k)
  invFun y :=
    match y with
    | .r j => ⟨Multiplicative.ofAdd ((j.val : ZMod 3)), .r ((j.val : ZMod 4))⟩
    | .sr j => ⟨Multiplicative.ofAdd (-(j.val : ZMod 3)), .sr ((j.val : ZMod 4))⟩
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

/-- Two homomorphisms out of `D_4` agreeing on the generators `r 1` and `sr 0` are equal. -/
private lemma d4_hom_ext {H : Type*} [Group H]
    {f g : DihedralGroup 4 →* H}
    (h1 : f (.r 1) = g (.r 1)) (h2 : f (.sr 0) = g (.sr 0)) :
    f = g := by
  have hr : ∀ i : ZMod 4, (.r i : DihedralGroup 4) = .r 1 ^ i.val := by decide
  have hsr : ∀ i : ZMod 4, (.sr i : DihedralGroup 4) = .sr 0 * .r 1 ^ i.val := by decide
  ext x
  rcases x with i | i
  · rw [hr, f.map_pow, g.map_pow, h1]
  · rw [hsr, f.map_mul, g.map_mul, f.map_pow, g.map_pow, h1, h2]

/-- Case-bash on `(φ(r 1), φ(sr 0)) ∈ {1, inv}²` (excluding the trivial case). The
`(1, inv)` case lands on `d4OnC3Inv_via_refl`; the other two land on `d4OnCqInv 3`
(using `d4_shift` for the `(inv, inv)` case). -/
private lemma d4_basis_change_exists
    {φ : DihedralGroup 4 →* MulAut (CyclicGroup 3)} (h : φ ≠ 1) :
    (∃ α : DihedralGroup 4 ≃* DihedralGroup 4,
        d4OnC3Inv_via_refl.comp α.toMonoidHom = φ) ∨
    (∃ α : DihedralGroup 4 ≃* DihedralGroup 4,
        (d4OnCqInv 3).comp α.toMonoidHom = φ) := by
  obtain ⟨a, ha⟩ : ∃ a, a = φ (.r 1) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = φ (.sr 0) := ⟨_, rfl⟩
  have close_refl (α : DihedralGroup 4 ≃* DihedralGroup 4)
      (h1 : d4OnC3Inv_via_refl (α (.r 1)) = a := by decide)
      (h2 : d4OnC3Inv_via_refl (α (.sr 0)) = b := by decide) :
      ∃ α' : DihedralGroup 4 ≃* DihedralGroup 4,
        d4OnC3Inv_via_refl.comp α'.toMonoidHom = φ :=
    ⟨α, d4_hom_ext (f := d4OnC3Inv_via_refl.comp α.toMonoidHom)
      (h1.trans ha) (h2.trans hb)⟩
  have close_parity (α : DihedralGroup 4 ≃* DihedralGroup 4)
      (h1 : d4OnCqInv 3 (α (.r 1)) = a := by decide)
      (h2 : d4OnCqInv 3 (α (.sr 0)) = b := by decide) :
      ∃ α' : DihedralGroup 4 ≃* DihedralGroup 4,
        (d4OnCqInv 3).comp α'.toMonoidHom = φ :=
    ⟨α, d4_hom_ext (f := (d4OnCqInv 3).comp α.toMonoidHom)
      (h1.trans ha) (h2.trans hb)⟩
  rcases mulAut_cyclicGroup_three_cases a with rfl | rfl <;>
    rcases mulAut_cyclicGroup_three_cases b with rfl | rfl
  · -- (1, 1): φ is trivial, contradicting `h`.
    exact absurd (d4_hom_ext ha.symm hb.symm) h
  · -- (1, inv): ker φ = ⟨r⟩. Take α = id.
    exact Or.inl (close_refl (MulEquiv.refl _))
  · -- (inv, 1): ker φ = {r 0, r 2, sr 0, sr 2}. Take α = id.
    exact Or.inr (close_parity (MulEquiv.refl _))
  · -- (inv, inv): ker φ = {r 0, r 2, sr 1, sr 3}. Take α = d4_shift.
    exact Or.inr (close_parity d4_shift)

/-- Any non-trivial action `φ` of `D_4` on `C_3` gives `C_3 ⋊[φ] D_4` isomorphic to either
`D_12` or `C_3 ⋊[d4OnCqInv 3] D_4`, depending on the iso class of `ker φ`. -/
private lemma c3_sdp_d4_nontrivial
    {φ : DihedralGroup 4 →* MulAut (CyclicGroup 3)} (h_nontriv : φ ≠ 1) :
    Nonempty (CyclicGroup 3 ⋊[φ] DihedralGroup 4 ≃* DihedralGroup 12) ∨
    Nonempty (CyclicGroup 3 ⋊[φ] DihedralGroup 4 ≃*
              CyclicGroup 3 ⋊[d4OnCqInv 3] DihedralGroup 4) := by
  rcases d4_basis_change_exists h_nontriv with ⟨α, hα⟩ | ⟨α, hα⟩
  · let : CyclicGroup 3 ⋊[φ] DihedralGroup 4 ≃* DihedralGroup 12 :=
      (sdp_congr_right_of_comp_eq α hα).trans c3_sdp_d4_iso_d12
    tauto
  · exact Or.inr ⟨sdp_congr_right_of_comp_eq α hα⟩

/-- Non-trivial-action branch of the normal-Sylow-3 classification. Given a
    semidirect-product iso `↥P ⋊[φ] ↥K ≃* G` with `|P| = 3` and `|K| = 8`,
    dispatch on `order8_classification` of `K`. The seven possible iso classes:
    - `K = C_8`                       →  `C_3 ⋊ C_8`
    - `K = C_4 × C_2`, `ker φ = C_4`  →  `D_3 × C_4`
    - `K = C_4 × C_2`, `ker φ = V_4`  →  `C_2 × Q_12`
    - `K = C_2^3`,    `ker φ = V_4`  →  `D_3 × V_4`
    - `K = D_4`,      `ker φ = C_4`  →  `D_12`
    - `K = Q_8`,      `ker φ = C_4`  →  `Q_24`
    - `K = D_4`,      `ker φ = V_4`  →  `C_3 ⋊[d4OnCqInv 3] D_4` -/
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
    Nonempty (G ≃* CyclicGroup 3 ⋊[d4OnCqInv 3] DihedralGroup 4) := by
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
    --   ker = C_4 or diagonal C_4  → D_3 × C_4
    --   ker = V_4                  → C_2 × Q_12
    obtain ⟨eK⟩ := hC4C2
    rcases c3_sdp_c4c2_nontrivial (transported_action_ne_one eP eK h_phi_nontriv) with he | he
    · obtain ⟨e⟩ := he
      let : G ≃* DihedralGroup 3 × CyclicGroup 4 :=
        h_iso.symm.trans <| (SemidirectProduct.congr' eP eK).trans e
      tauto
    · obtain ⟨e⟩ := he
      let : G ≃* CyclicGroup 2 × QuaternionGroup 3 :=
        h_iso.symm.trans <| (SemidirectProduct.congr' eP eK).trans e
      tauto
  · -- K ≃* C_2^3: target `D_3 × V_4`
    obtain ⟨eK⟩ := hC2sq3
    let : G ≃* DihedralGroup 3 × (CyclicGroup 2 × CyclicGroup 2) :=
      h_iso.symm.trans <|
      (SemidirectProduct.congr' eP eK).trans <|
      c3_sdp_c2cubed_nontrivial (transported_action_ne_one eP eK h_phi_nontriv)
    tauto
  · -- K ≃* D_4: two sub-cases by `ker φ`
    --   ker = rotation C_4   → D_12
    --   ker = reflection V_4 → C_3 ⋊[d4OnCqInv 3] D_4
    obtain ⟨eK⟩ := hD4
    rcases c3_sdp_d4_nontrivial (transported_action_ne_one eP eK h_phi_nontriv) with he | he
    · obtain ⟨e⟩ := he
      let : G ≃* DihedralGroup 12 :=
        h_iso.symm.trans <| (SemidirectProduct.congr' eP eK).trans e
      tauto
    · obtain ⟨e⟩ := he
      let : G ≃* CyclicGroup 3 ⋊[d4OnCqInv 3] DihedralGroup 4 :=
        h_iso.symm.trans <| (SemidirectProduct.congr' eP eK).trans e
      tauto
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

    The 5 trivial-action targets are proved in `order24_1_sylow3_trivial`; the
    7 non-trivial-action targets in `order24_1_sylow3_nontrivial`. -/
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
     Nonempty (G ≃* CyclicGroup 3 ⋊[d4OnCqInv 3] DihedralGroup 4)) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; decide)
  -- The unique Sylow 3-subgroup is normal in G
  haveI : Subsingleton (Sylow 3 G) := (Nat.card_eq_one_iff_unique.mp h_n3).1
  let P : Sylow 3 G := default
  haveI hPnormal : (↑P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
  -- |P| = 3 and [G : P] = 8
  have h_P_card : Nat.card ↥(P : Subgroup G) = 3 := by
    simpa using sylow_card_eq (p := 3) (q := 2) (by decide)
      (show Nat.card G = 3 ^ 1 * 2 ^ 3 by rw [h]; ring) P
  have h_P_idx : (↑P : Subgroup G).index = 8 := by
    simpa using sylow_index_eq (p := 3) (q := 2) (by decide)
      (show Nat.card G = 3 ^ 1 * 2 ^ 3 by rw [h]; ring) P
  -- Schur-Zassenhaus: a complement K of order 8 exists
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime
    (N := (↑P : Subgroup G)) (by rw [h_P_card, h_P_idx]; decide)
  -- Isomorphism `P ⋊[conjugation] K ≃* G`
  have h_iso := SemidirectProduct.mulEquivSubgroup hK
  -- |K| = 8
  have hK_card : Nat.card ↥K = 8 := by
    have := (Nat.card_congr h_iso.toEquiv).symm
    rw [SemidirectProduct.card, h_P_card, h] at this
    omega
  -- Conjugation action φ : K →* MulAut P
  let φ : ↥K →* MulAut ↥(↑P : Subgroup G) :=
    (↑P : Subgroup G).normalizerMonoidHom.comp
      (Subgroup.inclusion (by simp [Subgroup.normalizer_eq_top]))
  classical
  by_cases h_triv : φ = 1
  · -- Trivial action: extract `G ≃* C_3 × K`, dispatch via the trivial sub-lemma
    have h_iso_one : (↑P : Subgroup G) ⋊[(1 : ↥K →* MulAut ↥(↑P : Subgroup G))] ↥K ≃* G := by
      rw [← h_triv]; exact h_iso
    haveI : IsCyclic ↥(↑P : Subgroup G) := isCyclic_of_prime_card h_P_card
    have hP_iso : ↥(↑P : Subgroup G) ≃* CyclicGroup 3 :=
      mulEquivOfCyclicCardEq (h_P_card.trans (card_cyclicGroup 3).symm)
    have h_g_clean : G ≃* CyclicGroup 3 × ↥K :=
      h_iso_one.symm.trans <|
        SemidirectProduct.mulEquivProd.trans (hP_iso.prodCongr (MulEquiv.refl _))
    exact Or.inl (order24_1_sylow3_trivial h_g_clean hK_card)
  · -- Non-trivial action: pass setup state to the sub-lemma
    exact Or.inr (order24_1_sylow3_nontrivial h_P_card hK_card h_iso h_triv)

-- ── n₃ = 4 branch ───────────────────────────────────────────────────────────
-- Conjugation on the four Sylow 3-subgroups gives `ψ : G →* Perm (Sylow 3 G)`.
-- Its kernel `K = ⋂ N_G(P)` has order 1 or 2: each normalizer has order 6, and an
-- order-3 element of `K` would generate the unique Sylow-3 of all four distinct
-- normalizers at once. `|K| = 1` forces `G ≃* S_4` (count); `|K| = 2` puts a central
-- involution in `G`, which forces a normal Sylow-2 `T` (count), so `G ≃* T ⋊ C_3` with
-- `T ∈ {C_2³, Q_8}` (the only order-8 groups with an order-3 automorphism), giving
-- `C_2 × A_4` and `SL_2(𝔽_3)` respectively.

/-- With four Sylow 3-subgroups in a group of order 24, each normalizer has order 6. -/
private lemma sylow3_24_normalizer_card {G : Type*} [Group G] (h : Nat.card G = 24)
    (h_n3 : Nat.card (Sylow 3 G) = 4) (P : Sylow 3 G) :
    Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) = 6 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; decide)
  have h_idx := Sylow.card_eq_index_normalizer P
  rw [h_n3] at h_idx
  have h_mul := Subgroup.index_mul_card (Subgroup.normalizer ((P : Subgroup G) : Set G))
  rw [← h_idx, h] at h_mul
  omega

/-- The kernel of the conjugation action on Sylow 3-subgroups is contained in every
Sylow-3 normalizer. -/
private lemma sylow3_action_ker_le_normalizer {G : Type*} [Group G] (P : Sylow 3 G) :
    (MulAction.toPermHom G (Sylow 3 G)).ker ≤
      Subgroup.normalizer ((P : Subgroup G) : Set G) := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [← Sylow.smul_eq_iff_mem_normalizer]
  exact DFunLike.congr_fun hg P

/-- In a group of order 24, every Sylow 3-subgroup has order 3. -/
private lemma sylow3_24_card {G : Type*} [Group G] [Finite G] (h : Nat.card G = 24)
    (P : Sylow 3 G) : Nat.card (P : Subgroup G) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  simpa using sylow_card_eq (p := 3) (q := 2) (by decide)
    (show Nat.card G = 3 ^ 1 * 2 ^ 3 by rw [h]; ring) P

/-- An order-3 element of the normalizer of a Sylow 3-subgroup `P` lies in `P`: `P` has
index 2 in its order-6 normalizer, so squares of normalizer elements lie in `P`, and
`x = (x²)²` when `x³ = 1`. -/
private lemma sylow3_24_order3_mem_normalizer_mem_sylow {G : Type*} [Group G]
    (h : Nat.card G = 24) (h_n3 : Nat.card (Sylow 3 G) = 4) (P : Sylow 3 G)
    {x : G} (hx : orderOf x = 3)
    (hxN : x ∈ Subgroup.normalizer ((P : Subgroup G) : Set G)) :
    x ∈ (P : Subgroup G) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; decide)
  set N := Subgroup.normalizer ((P : Subgroup G) : Set G) with hN
  have h_card' : Nat.card ((P : Subgroup G).subgroupOf N) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv).trans
      (sylow3_24_card h P)
  have h_idx : ((P : Subgroup G).subgroupOf N).index = 2 := by
    have h_mul := Subgroup.index_mul_card ((P : Subgroup G).subgroupOf N)
    rw [h_card', sylow3_24_normalizer_card h h_n3 P] at h_mul
    omega
  have h3 : (⟨x, hxN⟩ : N) ^ 3 = 1 := by
    ext
    simpa using hx ▸ pow_orderOf_eq_one x
  have h_x4 : ((⟨x, hxN⟩ : N) ^ 2) ^ 2 = ⟨x, hxN⟩ := by
    rw [← pow_mul]
    calc (⟨x, hxN⟩ : N) ^ (2 * 2) = (⟨x, hxN⟩ : N) ^ 3 * ⟨x, hxN⟩ := by rw [pow_succ]
    _ = ⟨x, hxN⟩ := by rw [h3, one_mul]
  have h_mem := Subgroup.sq_mem_of_index_two h_idx ((⟨x, hxN⟩ : N) ^ 2)
  rw [h_x4] at h_mem
  exact Subgroup.mem_subgroupOf.mp h_mem

/-- The kernel of the Sylow-3 conjugation action has order coprime to 3: an order-3
element of the kernel would lie in all four (pairwise disjoint) Sylow 3-subgroups. -/
private lemma sylow3_action_ker_not_dvd_three {G : Type*} [Group G] (h : Nat.card G = 24)
    (h_n3 : Nat.card (Sylow 3 G) = 4) :
    ¬ 3 ∣ Nat.card (MulAction.toPermHom G (Sylow 3 G)).ker := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; decide)
  intro h_dvd
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h_dvd
  have hy' : orderOf (y : G) = 3 :=
    (orderOf_injective _ (Subgroup.subtype_injective _) y).trans hy
  have h_mem : ∀ P : Sylow 3 G, (y : G) ∈ (P : Subgroup G) := fun P =>
    sylow3_24_order3_mem_normalizer_mem_sylow h h_n3 P hy'
      (sylow3_action_ker_le_normalizer P y.2)
  haveI : Nontrivial (Sylow 3 G) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [h_n3]; norm_num)
  obtain ⟨P₁, P₂, hne⟩ := exists_pair_ne (Sylow 3 G)
  have h_y1 : (y : G) = 1 := Subgroup.mem_bot.mp
    (disjoint_iff.mp (sylow_prime_order_disjoint (sylow3_24_card h) hne) ▸
      Subgroup.mem_inf.mpr ⟨h_mem P₁, h_mem P₂⟩)
  rw [h_y1, orderOf_one] at hy'
  norm_num at hy'

/-- The kernel of the conjugation action on the four Sylow 3-subgroups has order 1 or 2. -/
private lemma sylow3_action_ker_card_dvd_two {G : Type*} [Group G] (h : Nat.card G = 24)
    (h_n3 : Nat.card (Sylow 3 G) = 4) :
    Nat.card (MulAction.toPermHom G (Sylow 3 G)).ker = 1 ∨
    Nat.card (MulAction.toPermHom G (Sylow 3 G)).ker = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; decide)
  obtain ⟨P⟩ : Nonempty (Sylow 3 G) := inferInstance
  have h_dvd6 : Nat.card (MulAction.toPermHom G (Sylow 3 G)).ker ∣ 6 :=
    sylow3_24_normalizer_card h h_n3 P ▸
      Subgroup.card_dvd_of_le (sylow3_action_ker_le_normalizer P)
  have h_not3 := sylow3_action_ker_not_dvd_three h h_n3
  have h_pos : 0 < Nat.card (MulAction.toPermHom G (Sylow 3 G)).ker := Nat.card_pos
  generalize hk : Nat.card (MulAction.toPermHom G (Sylow 3 G)).ker = k
      at h_dvd6 h_not3 h_pos ⊢
  have h_le : k ≤ 6 := Nat.le_of_dvd (by norm_num) h_dvd6
  interval_cases k <;> omega

/-- Trivial-kernel case: the action embeds `G` into `Perm (Sylow 3 G) ≃ S_4`, and both
have 24 elements. -/
private lemma order24_4_sylow3_ker_one {G : Type*} [Group G] (h : Nat.card G = 24)
    (h_n3 : Nat.card (Sylow 3 G) = 4)
    (h_ker : Nat.card (MulAction.toPermHom G (Sylow 3 G)).ker = 1) :
    Nonempty (G ≃* SymmetricGroup 4) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; decide)
  haveI : Fintype (Sylow 3 G) := Fintype.ofFinite _
  haveI : DecidableEq (Sylow 3 G) := Classical.decEq _
  have h_inj : Function.Injective (MulAction.toPermHom G (Sylow 3 G)) :=
    (MonoidHom.ker_eq_bot_iff _).mp (Subgroup.card_eq_one.mp h_ker)
  have h_card_perm : Nat.card (Equiv.Perm (Sylow 3 G)) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, h_n3]
    rfl
  have h_bij : Function.Bijective (MulAction.toPermHom G (Sylow 3 G)) :=
    (Nat.bijective_iff_injective_and_card _).mpr ⟨h_inj, by rw [h, h_card_perm]⟩
  have e_fin : Sylow 3 G ≃ Fin 4 :=
    Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card, h_n3])
  exact ⟨(MulEquiv.ofBijective _ h_bij).trans e_fin.permCongrHom⟩

/-- A group isomorphic to `T × H` with `|T| = 8` and `|H| = 3` has a unique Sylow
3-subgroup: there are at most 3 elements of order 3 (all in `1 × H`), but four Sylow
3-subgroups would give 8. -/
private lemma sylow3_card_one_of_iso_prod_order8 {G T H : Type*} [Group G] [Group T]
    [Group H] (hT : Nat.card T = 8) (hH : Nat.card H = 3) (e : G ≃* T × H) :
    Nat.card (Sylow 3 G) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [hT]; decide)
  haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; decide)
  haveI : Finite G := Finite.of_equiv _ e.toEquiv.symm
  have h24 : Nat.card G = 24 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, hT, hH]
  rcases sylow3_24 h24 with h1 | h4
  · exact h1
  exfalso
  have h_count : Nat.card {x : G | orderOf x = 3} = 8 := by
    rw [sylow_elements_order_p_card (sylow3_24_card h24), h4]
  -- every order-3 element maps into `1 × H` under `e`
  have h_fst : ∀ x : G, orderOf x = 3 → (e x).1 = 1 := by
    intro x hx
    have h_pow : (e x) ^ 3 = 1 := by
      rw [← map_pow, ← hx, pow_orderOf_eq_one x, map_one]
    have h_ord3 : orderOf (e x).1 ∣ 3 :=
      orderOf_dvd_iff_pow_eq_one.mpr (congrArg Prod.fst h_pow)
    have h_ord8 : orderOf (e x).1 ∣ 8 := hT ▸ orderOf_dvd_natCard _
    have h_one : orderOf (e x).1 ∣ 1 := by simpa using Nat.dvd_gcd h_ord3 h_ord8
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h_one)
  -- so the order-3 elements inject into H
  have h_le : Nat.card {x : G | orderOf x = 3} ≤ Nat.card H := by
    have hf : Function.Injective
        (fun x : {x : G | orderOf x = 3} => (e (x : G)).2) := by
      intro x y hxy
      have h_eq : e (x : G) = e (y : G) :=
        Prod.ext (by rw [h_fst _ x.2, h_fst _ y.2]) hxy
      exact Subtype.ext (e.injective h_eq)
    exact Nat.card_le_card_of_injective _ hf
  rw [h_count, hH] at h_le
  omega

/-- A hom out of `C_3` killing the generator is trivial. -/
private lemma c3_hom_eq_one_of_gen_eq_one {M : Type*} [Group M]
    {ψ : CyclicGroup 3 →* M} (h : ψ (Multiplicative.ofAdd 1) = 1) : ψ = 1 := by
  rw [cyclicHom_ext ψ (one_pow 3) h]
  ext x
  rw [cyclicHom_apply_eq_zpow]
  simp

/-- The cube of the generator image under a hom out of `C_3` is trivial. -/
private lemma c3_hom_gen_cube_eq_one {M : Type*} [Group M]
    (ψ : CyclicGroup 3 →* M) : ψ (Multiplicative.ofAdd 1) ^ 3 = 1 := by
  rw [← map_pow]
  exact (congrArg ψ (by decide)).trans (map_one ψ)

/-- Every element of `CyclicGroup 8` is killed by the 8th power. -/
private lemma c8_exp (b : CyclicGroup 8) : b ^ 8 = 1 := by revert b; decide

/-- `Aut(C_8)` has no non-trivial elements of order dividing 3. -/
private lemma mulAut_c8_eq_one_of_cube_eq_one
    (A : MulAut (CyclicGroup 8)) (h : A ^ 3 = 1) : A = 1 := by
  obtain ⟨a, ha⟩ : ∃ a, a = A (Multiplicative.ofAdd 1) := ⟨_, rfl⟩
  have h_det := cyclicHom_ext A.toMonoidHom (c8_exp a) ha.symm
  have hpt : ∀ x, A x = cyclicHom 8 a (c8_exp a) x := fun x => DFunLike.congr_fun h_det x
  have h1 : A (A (A (Multiplicative.ofAdd 1))) = Multiplicative.ofAdd 1 :=
    DFunLike.congr_fun h (Multiplicative.ofAdd 1)
  simp only [hpt] at h1
  have key : ∀ b : CyclicGroup 8,
      cyclicHom 8 b (c8_exp b) (cyclicHom 8 b (c8_exp b) (cyclicHom 8 b (c8_exp b)
        (Multiplicative.ofAdd 1))) = Multiplicative.ofAdd 1 →
      ∀ x, cyclicHom 8 b (c8_exp b) x = x := by decide
  ext x
  rw [hpt]
  exact key a h1 x

/-- Every element of `C_4 × C_2` is killed by the 4th power. -/
private lemma c4c2_exp4 (b : CyclicGroup 4 × CyclicGroup 2) : b ^ 4 = 1 := by
  revert b; decide

/-- The endomorphism of `C_4 × C_2` sending the generators `(a, 1) ↦ u` and `(1, b) ↦ v`
(the codomain is abelian, so the pointwise product of the two factor homs is a hom). -/
private def c4c2CompHom (u v : CyclicGroup 4 × CyclicGroup 2) (hv : v ^ 2 = 1) :
    (CyclicGroup 4 × CyclicGroup 2) →* (CyclicGroup 4 × CyclicGroup 2) :=
  ((cyclicHom 4 u (c4c2_exp4 u)).comp (MonoidHom.fst (CyclicGroup 4) (CyclicGroup 2))) *
    ((cyclicHom 2 v hv).comp (MonoidHom.snd (CyclicGroup 4) (CyclicGroup 2)))

private lemma c4c2CompHom_gen1 (u v : CyclicGroup 4 × CyclicGroup 2) (hv : v ^ 2 = 1) :
    c4c2CompHom u v hv (Multiplicative.ofAdd 1, 1) = u := by
  haveI : Fact (1 < 4) := ⟨by norm_num⟩
  simp [c4c2CompHom, cyclicHom_apply_eq_zpow, ZMod.val_one]

private lemma c4c2CompHom_gen2 (u v : CyclicGroup 4 × CyclicGroup 2) (hv : v ^ 2 = 1) :
    c4c2CompHom u v hv (1, Multiplicative.ofAdd 1) = v := by
  haveI : Fact (1 < 2) := ⟨by norm_num⟩
  simp [c4c2CompHom, cyclicHom_apply_eq_zpow, ZMod.val_one]

/-- `Aut(C_4 × C_2)` has no non-trivial elements of order dividing 3. -/
private lemma mulAut_c4c2_eq_one_of_cube_eq_one
    (A : MulAut (CyclicGroup 4 × CyclicGroup 2)) (h : A ^ 3 = 1) : A = 1 := by
  obtain ⟨u, hu⟩ : ∃ u, u = A (Multiplicative.ofAdd 1, 1) := ⟨_, rfl⟩
  obtain ⟨v, hv'⟩ : ∃ v, v = A (1, Multiplicative.ofAdd 1) := ⟨_, rfl⟩
  have hv : v ^ 2 = 1 := by
    rw [hv']
    exact (map_pow A _ 2).symm.trans ((congrArg A (by decide)).trans (map_one A))
  have h_det : A.toMonoidHom = c4c2CompHom u v hv :=
    c4c2_hom_ext (hu.symm.trans (c4c2CompHom_gen1 u v hv).symm)
      (hv'.symm.trans (c4c2CompHom_gen2 u v hv).symm)
  have hpt : ∀ x, A x = c4c2CompHom u v hv x := fun x => DFunLike.congr_fun h_det x
  have h1 : A (A (A (Multiplicative.ofAdd 1, 1))) = (Multiplicative.ofAdd 1, 1) :=
    DFunLike.congr_fun h _
  have h2 : A (A (A ((1 : CyclicGroup 4), Multiplicative.ofAdd 1))) =
      (1, Multiplicative.ofAdd 1) :=
    DFunLike.congr_fun h _
  simp only [hpt] at h1 h2
  have key : ∀ w : CyclicGroup 4 × CyclicGroup 2, ∀ hw : w ^ 2 = 1,
      ∀ z : CyclicGroup 4 × CyclicGroup 2,
      c4c2CompHom z w hw (c4c2CompHom z w hw (c4c2CompHom z w hw
        (Multiplicative.ofAdd 1, 1))) = (Multiplicative.ofAdd 1, 1) →
      c4c2CompHom z w hw (c4c2CompHom z w hw (c4c2CompHom z w hw
        (1, Multiplicative.ofAdd 1))) = (1, Multiplicative.ofAdd 1) →
      ∀ x, c4c2CompHom z w hw x = x := by decide
  refine MulEquiv.ext fun x => ?_
  rw [hpt]
  exact key v hv u h1 h2 x

/-- Candidate endomorphism of `D_4` from generator images `r 1 ↦ u`, `sr 0 ↦ w` (a raw
function; no hom structure is needed since every element is `r i` or `sr i`). -/
private def d4GenMap (u w : DihedralGroup 4) : DihedralGroup 4 → DihedralGroup 4
  | .r i => u ^ i.val
  | .sr i => w * u ^ i.val

/-- `Aut(D_4)` has no non-trivial elements of order dividing 3. -/
private lemma mulAut_d4_eq_one_of_cube_eq_one
    (A : MulAut (DihedralGroup 4)) (h : A ^ 3 = 1) : A = 1 := by
  obtain ⟨u, hu⟩ : ∃ u, u = A (.r 1) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = A (.sr 0) := ⟨_, rfl⟩
  have hr : ∀ j : ZMod 4, (.r j : DihedralGroup 4) = .r 1 ^ j.val := by decide
  have hsr : ∀ j : ZMod 4, (.sr j : DihedralGroup 4) = .sr 0 * .r 1 ^ j.val := by decide
  have hpt : ∀ d, A d = d4GenMap u w d := by
    intro d
    rcases d with i | i
    · change A (.r i) = u ^ i.val
      rw [hr i, map_pow, ← hu]
    · change A (.sr i) = w * u ^ i.val
      rw [hsr i, map_mul, map_pow, ← hu, ← hw]
  have hinj : Function.Injective (d4GenMap u w) := by
    rw [← funext hpt]
    exact A.injective
  have h1 : A (A (A (.r 1))) = .r 1 := DFunLike.congr_fun h _
  have h2 : A (A (A (.sr 0))) = .sr 0 := DFunLike.congr_fun h _
  simp only [hpt] at h1 h2
  have key : ∀ z y : DihedralGroup 4, Function.Injective (d4GenMap z y) →
      d4GenMap z y (d4GenMap z y (d4GenMap z y (.r 1))) = .r 1 →
      d4GenMap z y (d4GenMap z y (d4GenMap z y (.sr 0))) = .sr 0 →
      ∀ d, d4GenMap z y d = d := by decide
  refine MulEquiv.ext fun x => ?_
  rw [hpt]
  exact key u w hinj h1 h2 x

/-- `Aut(C_8)` has order 4, so it admits no non-trivial hom from `C_3`. -/
private lemma c3_hom_mulAut_c8_trivial
    (ψ : CyclicGroup 3 →* MulAut (CyclicGroup 8)) : ψ = 1 :=
  c3_hom_eq_one_of_gen_eq_one
    (mulAut_c8_eq_one_of_cube_eq_one _ (c3_hom_gen_cube_eq_one ψ))

/-- `Aut(C_4 × C_2)` has order 8, so it admits no non-trivial hom from `C_3`. -/
private lemma c3_hom_mulAut_c4c2_trivial
    (ψ : CyclicGroup 3 →* MulAut (CyclicGroup 4 × CyclicGroup 2)) : ψ = 1 :=
  c3_hom_eq_one_of_gen_eq_one
    (mulAut_c4c2_eq_one_of_cube_eq_one _ (c3_hom_gen_cube_eq_one ψ))

/-- `Aut(D_4)` has order 8, so it admits no non-trivial hom from `C_3`. -/
private lemma c3_hom_mulAut_d4_trivial
    (ψ : CyclicGroup 3 →* MulAut (DihedralGroup 4)) : ψ = 1 :=
  c3_hom_eq_one_of_gen_eq_one
    (mulAut_d4_eq_one_of_cube_eq_one _ (c3_hom_gen_cube_eq_one ψ))

/-- The order-3 automorphism of `Q_8` cycling `i ↦ j ↦ k ↦ i` (and `-i ↦ -j ↦ -k`),
in the encoding `i = a 1`, `j = xa 0`, `k = xa 3`, `-1 = a 2`. -/
private def q8_cycle_ijk : QuaternionGroup 2 ≃* QuaternionGroup 2 where
  toFun
    | .a 0 => .a 0   | .a 1 => .xa 0 | .a 2 => .a 2   | .a 3 => .xa 2
    | .xa 0 => .xa 3 | .xa 1 => .a 3 | .xa 2 => .xa 1 | .xa 3 => .a 1
  invFun
    | .a 0 => .a 0   | .a 1 => .xa 3 | .a 2 => .a 2   | .a 3 => .xa 1
    | .xa 0 => .a 1  | .xa 1 => .xa 2 | .xa 2 => .a 3 | .xa 3 => .xa 0
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

/-- The standard non-trivial action of `C_3` on `Q_8`, sending the generator to
`q8_cycle_ijk`. -/
private def c3OnQ8 : CyclicGroup 3 →* MulAut (QuaternionGroup 2) :=
  cyclicHom 3 q8_cycle_ijk (by
    ext x
    change q8_cycle_ijk (q8_cycle_ijk (q8_cycle_ijk x)) = x
    revert x; decide)

/-- Candidate endomorphism of `Q_8` from generator images `a 1 ↦ u`, `xa 0 ↦ w` (a raw
function; every element of `Q_8` is a word `a i = (a 1)^i` or `xa i = xa 0 * a i`). -/
private def q8GenMap (u w : QuaternionGroup 2) : QuaternionGroup 2 → QuaternionGroup 2
  | .a i => u ^ i.val
  | .xa i => w * u ^ i.val

/-- Every multiplicative injective `q8GenMap` of order dividing 3 (and not the identity)
is conjugate to `q8_cycle_ijk` by some multiplicative injective `q8GenMap`: all order-3
automorphisms of `Q_8` are conjugate in `Aut(Q_8) ≃ S_4`. -/
private lemma q8GenMap_conjugator_exists : ∀ z y : QuaternionGroup 2,
    (∀ s t, q8GenMap z y (s * t) = q8GenMap z y s * q8GenMap z y t) →
    (∀ s t, q8GenMap z y s = q8GenMap z y t → s = t) →
    q8GenMap z y (q8GenMap z y (q8GenMap z y (.a 1))) = .a 1 →
    q8GenMap z y (q8GenMap z y (q8GenMap z y (.xa 0))) = .xa 0 →
    (¬ ∀ q, q8GenMap z y q = q) →
    ∃ p r : QuaternionGroup 2,
      (∀ s t, q8GenMap p r (s * t) = q8GenMap p r s * q8GenMap p r t) ∧
      (∀ s t, q8GenMap p r s = q8GenMap p r t → s = t) ∧
      ∀ q, q8GenMap p r (q8GenMap z y q) = q8_cycle_ijk (q8GenMap p r q) := by
  decide

/-- Basis change: any non-trivial action of `C_3` on `Q_8` is conjugate to the standard
one, since all order-3 automorphisms of `Q_8` are conjugate in `Aut(Q_8) ≃ S_4`. -/
private lemma q8_sdp_c3_iso_standard
    {ψ : CyclicGroup 3 →* MulAut (QuaternionGroup 2)} (h_nontriv : ψ ≠ 1) :
    Nonempty (QuaternionGroup 2 ⋊[ψ] CyclicGroup 3 ≃*
      QuaternionGroup 2 ⋊[c3OnQ8] CyclicGroup 3) := by
  -- Pin the generator image `B := ψ(gen)` to a raw generator-image map
  obtain ⟨B, hB⟩ : ∃ B, B = ψ (Multiplicative.ofAdd 1) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = B (.a 1) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = B (.xa 0) := ⟨_, rfl⟩
  have hra : ∀ j : ZMod 4, (.a j : QuaternionGroup 2) = .a 1 ^ j.val := by decide
  have hxa : ∀ j : ZMod 4, (.xa j : QuaternionGroup 2) = .xa 0 * .a 1 ^ j.val := by decide
  have hpt : ∀ q, B q = q8GenMap u w q := by
    intro q
    rcases q with i | i
    · change B (.a i) = u ^ i.val
      rw [hra i, map_pow, ← hu]
    · change B (.xa i) = w * u ^ i.val
      rw [hxa i, map_mul, map_pow, ← hu, ← hw]
  have hmul : ∀ s t, q8GenMap u w (s * t) = q8GenMap u w s * q8GenMap u w t := by
    intro s t
    rw [← hpt, ← hpt, ← hpt, map_mul]
  have hinj : ∀ s t, q8GenMap u w s = q8GenMap u w t → s = t := by
    intro s t hst
    rw [← hpt, ← hpt] at hst
    exact B.injective hst
  have hB3 : B ^ 3 = 1 := by rw [hB]; exact c3_hom_gen_cube_eq_one ψ
  have h1 : B (B (B (.a 1))) = .a 1 := DFunLike.congr_fun hB3 _
  have h2 : B (B (B (.xa 0))) = .xa 0 := DFunLike.congr_fun hB3 _
  simp only [hpt] at h1 h2
  have hne : ¬ ∀ q, q8GenMap u w q = q := fun hall =>
    h_nontriv (c3_hom_eq_one_of_gen_eq_one
      (hB.symm.trans (MulEquiv.ext fun q => (hpt q).trans (hall q))))
  -- Extract the conjugator and assemble it into an automorphism β
  obtain ⟨p, r, hmul', hinj', hconj⟩ :=
    q8GenMap_conjugator_exists u w hmul hinj h1 h2 hne
  have hbij : Function.Bijective (q8GenMap p r) :=
    Finite.injective_iff_bijective.mp fun s t => hinj' s t
  let β : QuaternionGroup 2 ≃* QuaternionGroup 2 :=
    MulEquiv.ofBijective (MonoidHom.mk' (q8GenMap p r) hmul') hbij
  -- β conjugates B to the standard generator automorphism
  have h_gen_conj : MulAut.congr β B = q8_cycle_ijk := by
    refine MulEquiv.ext fun x => ?_
    change β (B (β.symm x)) = q8_cycle_ijk x
    rw [hpt (β.symm x)]
    change q8GenMap p r (q8GenMap u w (β.symm x)) = q8_cycle_ijk x
    rw [hconj (β.symm x)]
    change q8_cycle_ijk (β (β.symm x)) = q8_cycle_ijk x
    rw [MulEquiv.apply_symm_apply]
  -- hence it intertwines the actions as homs out of C_3
  have hρ3 : q8_cycle_ijk ^ 3 = 1 := by
    ext x
    change q8_cycle_ijk (q8_cycle_ijk (q8_cycle_ijk x)) = x
    revert x; decide
  have h_gen : ((MulAut.congr β).toMonoidHom.comp ψ) (Multiplicative.ofAdd 1) =
      q8_cycle_ijk := by
    change MulAut.congr β (ψ (Multiplicative.ofAdd 1)) = q8_cycle_ijk
    rw [← hB]
    exact h_gen_conj
  have h_hom : (MulAut.congr β).toMonoidHom.comp ψ = c3OnQ8 :=
    cyclicHom_ext _ hρ3 h_gen
  -- transport the semidirect product along β
  refine ⟨SemidirectProduct.congr β (MulEquiv.refl _) fun g => ?_⟩
  have hg := DFunLike.congr_fun h_hom g
  ext n
  change β (ψ g n) = c3OnQ8 g (β n)
  rw [← hg]
  change β (ψ g n) = β (ψ g (β.symm (β n)))
  rw [MulEquiv.symm_apply_apply]

/-- The embedding `Q_8 →* SL_2(𝔽_3)` sending `i, j, k` to `!![0,-1;1,0]`, `!![1,1;1,-1]`,
`!![-1,1;1,1]`. Its image is the (unique) Sylow 2-subgroup of `SL_2(𝔽_3)`. -/
private def q8HomSL23 : QuaternionGroup 2 →* SL2 3 where
  toFun
    | .a 0 => ⟨!![1, 0; 0, 1], by decide⟩
    | .a 1 => ⟨!![0, -1; 1, 0], by decide⟩
    | .a 2 => ⟨!![-1, 0; 0, -1], by decide⟩
    | .a 3 => ⟨!![0, 1; -1, 0], by decide⟩
    | .xa 0 => ⟨!![1, 1; 1, -1], by decide⟩
    | .xa 1 => ⟨!![1, -1; -1, -1], by decide⟩
    | .xa 2 => ⟨!![-1, -1; -1, 1], by decide⟩
    | .xa 3 => ⟨!![-1, 1; 1, 1], by decide⟩
  map_one' := by decide
  map_mul' p q := by revert p q; decide

/-- The hom `C_3 →* SL_2(𝔽_3)` sending the generator to the order-3 unipotent
`!![1,1;0,1]`, whose conjugation action cycles the images of `i, j, k`. -/
private def c3HomSL23 : CyclicGroup 3 →* SL2 3 :=
  cyclicHom 3 ⟨!![1, 1; 0, 1], by decide⟩ (by decide)

/-- Conjugating `q8HomSL23` by `c3HomSL23 g` realises the action `c3OnQ8 g`. -/
private lemma q8HomSL23_compat (g : CyclicGroup 3) (n : QuaternionGroup 2) :
    q8HomSL23 (c3OnQ8 g n) = c3HomSL23 g * q8HomSL23 n * (c3HomSL23 g)⁻¹ := by
  revert g n; decide

/-- Identification: `Q_8 ⋊[c3OnQ8] C_3 ≃* SL_2(𝔽_3)`. The hom is assembled by
`SemidirectProduct.lift` from `q8HomSL23` and `c3HomSL23` (the compatibility and
injectivity checks are decidable), and bijectivity follows since both sides have 24
elements. -/
private noncomputable def q8_sdp_c3OnQ8_iso_sl23 :
    QuaternionGroup 2 ⋊[c3OnQ8] CyclicGroup 3 ≃* SL2 3 := by
  refine MulEquiv.ofBijective
    (SemidirectProduct.lift q8HomSL23 c3HomSL23
      (fun g => MonoidHom.ext fun n => q8HomSL23_compat g n))
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩)
  · rw [injective_iff_map_eq_one]
    decide
  · have h1 : Nat.card (QuaternionGroup 2) = 8 := by
      rw [Nat.card_eq_fintype_card]; decide
    have h2 : Nat.card (SL2 3) = 24 := by
      rw [Nat.card_eq_fintype_card]; decide
    rw [SemidirectProduct.card, h1, card_cyclicGroup, h2]

/-- Any non-trivial action `ψ` of `C_3` on `Q_8` gives `Q_8 ⋊[ψ] C_3 ≃* SL_2(𝔽_3)`. -/
private lemma q8_sdp_c3_nontrivial
    {ψ : CyclicGroup 3 →* MulAut (QuaternionGroup 2)} (h_nontriv : ψ ≠ 1) :
    Nonempty (QuaternionGroup 2 ⋊[ψ] CyclicGroup 3 ≃* SL2 3) := by
  obtain ⟨e⟩ := q8_sdp_c3_iso_standard h_nontriv
  exact ⟨e.trans q8_sdp_c3OnQ8_iso_sl23⟩

/-- Any non-trivial action `ψ` of `C_3` on `(C_2)³` gives
`(C_2)³ ⋊[ψ] C_3 ≃* C_2 × A_4`: the fixed line of `ψ` splits off as a central `C_2`, and
`C_3` acts simply on the complementary `V_4`. -/
private lemma c2cubed_sdp_c3_nontrivial
    {ψ : CyclicGroup 3 →* MulAut (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2)}
    (h_nontriv : ψ ≠ 1) :
    Nonempty ((CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) ⋊[ψ] CyclicGroup 3 ≃*
      CyclicGroup 2 × AlternatingGroup 4) := by
  sorry

/-- Dispatch on the iso class of the order-8 normal subgroup in `T ⋊[φ] C` with `φ ≠ 1`:
only `C_2³` and `Q_8` admit an order-3 automorphism, giving `C_2 × A_4` and `SL_2(𝔽_3)`
respectively. -/
private lemma order24_4_sdp_dispatch {G : Type*} [Group G]
    {T C : Subgroup G} (h_T_card : Nat.card ↥T = 8) (h_C_card : Nat.card ↥C = 3)
    {φ : ↥C →* MulAut ↥T} (h_iso : ↥T ⋊[φ] ↥C ≃* G) (h_phi_nontriv : φ ≠ 1) :
    Nonempty (G ≃* CyclicGroup 2 × AlternatingGroup 4) ∨
    Nonempty (G ≃* SL2 3) := by
  haveI : IsCyclic ↥C := isCyclic_of_prime_card h_C_card
  have eC : ↥C ≃* CyclicGroup 3 :=
    mulEquivOfCyclicCardEq (h_C_card.trans (card_cyclicGroup 3).symm)
  rcases order8_classification (G := ↥T) h_T_card with hC8 | hC4C2 | hC2sq3 | hD4 | hQ8
  · -- T ≃* C_8: impossible, Aut(C_8) has no order-3 elements
    obtain ⟨eT⟩ := hC8
    exact absurd (c3_hom_mulAut_c8_trivial _)
      (transported_action_ne_one eT eC h_phi_nontriv)
  · -- T ≃* C_4 × C_2: impossible
    obtain ⟨eT⟩ := hC4C2
    exact absurd (c3_hom_mulAut_c4c2_trivial _)
      (transported_action_ne_one eT eC h_phi_nontriv)
  · -- T ≃* C_2³: target C_2 × A_4
    obtain ⟨eT⟩ := hC2sq3
    obtain ⟨e⟩ := c2cubed_sdp_c3_nontrivial (transported_action_ne_one eT eC h_phi_nontriv)
    let : G ≃* CyclicGroup 2 × AlternatingGroup 4 :=
      h_iso.symm.trans <| (SemidirectProduct.congr' eT eC).trans e
    tauto
  · -- T ≃* D_4: impossible
    obtain ⟨eT⟩ := hD4
    exact absurd (c3_hom_mulAut_d4_trivial _)
      (transported_action_ne_one eT eC h_phi_nontriv)
  · -- T ≃* Q_8: target SL_2(𝔽_3)
    obtain ⟨eT⟩ := hQ8
    obtain ⟨e⟩ := q8_sdp_c3_nontrivial (transported_action_ne_one eT eC h_phi_nontriv)
    let : G ≃* SL2 3 :=
      h_iso.symm.trans <| (SemidirectProduct.congr' eT eC).trans e
    tauto

/-- A group of order 24 with four Sylow 3-subgroups and a normal Sylow 2-subgroup `T` is
`T ⋊ C_3` with a non-trivial action, so `T ≃ C_2³` (giving `C_2 × A_4`) or `T ≃ Q_8`
(giving `SL_2(𝔽_3)`) — the other order-8 groups have no order-3 automorphism. -/
private lemma order24_4_sylow3_normal_sylow2 {G : Type*} [Group G] (h : Nat.card G = 24)
    (h_n3 : Nat.card (Sylow 3 G) = 4) (h_n2 : Nat.card (Sylow 2 G) = 1) :
    Nonempty (G ≃* CyclicGroup 2 × AlternatingGroup 4) ∨
    Nonempty (G ≃* SL2 3) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; decide)
  -- The unique Sylow 2-subgroup is normal in G
  haveI : Subsingleton (Sylow 2 G) := (Nat.card_eq_one_iff_unique.mp h_n2).1
  let T : Sylow 2 G := default
  haveI hTnormal : (↑T : Subgroup G).Normal := Sylow.normal_of_subsingleton T
  -- |T| = 8 and [G : T] = 3
  have h_T_card : Nat.card ↥(T : Subgroup G) = 8 := by
    simpa using sylow_card_eq (p := 2) (q := 3) (by decide)
      (show Nat.card G = 2 ^ 3 * 3 ^ 1 by rw [h]; ring) T
  have h_T_idx : (↑T : Subgroup G).index = 3 := by
    simpa using sylow_index_eq (p := 2) (q := 3) (by decide)
      (show Nat.card G = 2 ^ 3 * 3 ^ 1 by rw [h]; ring) T
  -- Schur-Zassenhaus: a complement C of order 3 exists
  obtain ⟨C, hC⟩ := Subgroup.exists_right_complement'_of_coprime
    (N := (↑T : Subgroup G)) (by rw [h_T_card, h_T_idx]; decide)
  have h_iso := SemidirectProduct.mulEquivSubgroup hC
  have h_C_card : Nat.card ↥C = 3 := by
    have := (Nat.card_congr h_iso.toEquiv).symm
    rw [SemidirectProduct.card, h_T_card, h] at this
    omega
  -- Conjugation action φ : C →* MulAut T
  let φ : ↥C →* MulAut ↥(↑T : Subgroup G) :=
    (↑T : Subgroup G).normalizerMonoidHom.comp
      (Subgroup.inclusion (by simp [Subgroup.normalizer_eq_top]))
  classical
  by_cases h_triv : φ = 1
  · -- Trivial action would make the Sylow-3 normal, contradicting n₃ = 4
    exfalso
    have h_iso_one : ↥(↑T : Subgroup G) ⋊[(1 : ↥C →* MulAut ↥(↑T : Subgroup G))] ↥C ≃* G := by
      rw [← h_triv]; exact h_iso
    have e : G ≃* ↥(↑T : Subgroup G) × ↥C :=
      h_iso_one.symm.trans SemidirectProduct.mulEquivProd
    have := sylow3_card_one_of_iso_prod_order8 h_T_card h_C_card e
    omega
  · exact order24_4_sdp_dispatch h_T_card h_C_card h_iso h_triv

/-- A normal subgroup of order 2 is generated by a central involution: conjugation
preserves the subgroup and cannot move its unique non-identity element. -/
private lemma exists_central_involution_of_normal_card_two {G : Type*} [Group G]
    {K : Subgroup G} [hKn : K.Normal] (hK : Nat.card K = 2) :
    ∃ z : G, orderOf z = 2 ∧ z ∈ Subgroup.center G := by
  haveI : Finite ↥K := Nat.finite_of_card_ne_zero (by rw [hK]; decide)
  obtain ⟨y, hy, hy_uniq⟩ := (Nat.card_eq_two_iff' (1 : ↥K)).mp hK
  have hy_coe : (↑y : G) ≠ 1 := fun h1 => hy (Subtype.ext h1)
  refine ⟨↑y, ?_, ?_⟩
  · have hy2 : (↑y : G) ^ 2 = 1 := by
      have := pow_card_eq_one' (G := ↥K) (x := y)
      rw [hK] at this
      exact_mod_cast congrArg Subtype.val this
    exact orderOf_eq_prime hy2 hy_coe
  · rw [Subgroup.mem_center_iff]
    intro g
    have h_mem : g * ↑y * g⁻¹ ∈ K := hKn.conj_mem _ y.2 g
    have h_ne : (⟨g * ↑y * g⁻¹, h_mem⟩ : ↥K) ≠ 1 := by
      intro h1
      apply hy_coe
      have h_one : g * ↑y * g⁻¹ = 1 := congrArg Subtype.val h1
      calc (↑y : G) = g⁻¹ * (g * ↑y * g⁻¹) * g := by group
      _ = 1 := by rw [h_one]; group
    have h_eq : g * ↑y * g⁻¹ = ↑y := congrArg Subtype.val (hy_uniq _ h_ne)
    calc g * ↑y = g * ↑y * g⁻¹ * g := by group
    _ = ↑y * g := by rw [h_eq]

/-- Multiplying by a central involution sends order-3 elements to order-6 elements. -/
private lemma orderOf_central_invol_mul {G : Type*} [Group G] {z x : G}
    (hz : orderOf z = 2) (hz_mem : z ∈ Subgroup.center G) (hx : orderOf x = 3) :
    orderOf (z * x) = 6 := by
  have hcomm : Commute z x := (Subgroup.mem_center_iff.mp hz_mem x).symm
  rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hz, hx]; decide), hz, hx]

/-- Counting: with `n₃ = 4` and a central involution, the four Sylow 3-subgroups give 8
elements of order 3 and their translates give 8 of order 6, so each order-8 Sylow
2-subgroup must absorb all 8 elements of 2-power order. -/
private lemma two_power_order_mem_sylow2_of_central_invol {G : Type*} [Group G]
    (h : Nat.card G = 24) (h_n3 : Nat.card (Sylow 3 G) = 4) {z : G}
    (hz : orderOf z = 2) (hz_mem : z ∈ Subgroup.center G)
    (T : Sylow 2 G) (x : G) (hx : orderOf x ∣ 8) :
    x ∈ (T : Subgroup G) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; decide)
  haveI : Fintype G := Fintype.ofFinite G
  haveI : DecidableEq G := Classical.decEq G
  haveI : DecidablePred (· ∈ (T : Subgroup G)) := Classical.decPred _
  set S3 : Finset G := ({y | orderOf y = 3} : Set G).toFinset with hS3def
  set S6 : Finset G := ({y | orderOf y = 6} : Set G).toFinset with hS6def
  set TF : Finset G := ((T : Subgroup G) : Set G).toFinset with hTFdef
  have mem_S3 : ∀ y : G, y ∈ S3 ↔ orderOf y = 3 := fun y => by
    rw [hS3def]; simp
  have mem_S6 : ∀ y : G, y ∈ S6 ↔ orderOf y = 6 := fun y => by
    rw [hS6def]; simp
  have mem_TF : ∀ y : G, y ∈ TF ↔ y ∈ (T : Subgroup G) := fun y => by
    rw [hTFdef]; simp
  have h8 : Nat.card (T : Subgroup G) = 8 := by
    simpa using sylow_card_eq (p := 2) (q := 3) (by decide)
      (show Nat.card G = 2 ^ 3 * 3 ^ 1 by rw [h]; ring) T
  -- the three cardinalities
  have hS3_card : S3.card = 8 := by
    have heq : S3.card = Nat.card {y : G | orderOf y = 3} := by
      rw [hS3def, Set.toFinset_card, Nat.card_eq_fintype_card]
    rw [heq, sylow_elements_order_p_card (sylow3_24_card h), h_n3]
  have hTF_card : TF.card = 8 := by
    have heq : TF.card = Nat.card (T : Subgroup G) := by
      rw [hTFdef]; simp [Set.toFinset_card]
    rw [heq, h8]
  have hS6_ge : 8 ≤ S6.card := by
    have hmaps : ∀ y ∈ S3, z * y ∈ S6 := fun y hy =>
      (mem_S6 _).mpr (orderOf_central_invol_mul hz hz_mem ((mem_S3 _).mp hy))
    have hinj : Set.InjOn (fun y => z * y) ↑S3 := (mul_right_injective z).injOn
    calc 8 = S3.card := hS3_card.symm
    _ ≤ S6.card := Finset.card_le_card_of_injOn _ hmaps hinj
  -- pairwise disjoint
  have hd36 : Disjoint S3 S6 := by
    rw [Finset.disjoint_left]
    intro y hy3 hy6
    rw [mem_S3] at hy3
    rw [mem_S6] at hy6
    omega
  have h_not36 : ∀ y : G, orderOf y ∣ 8 → y ∉ S3 ∪ S6 := by
    intro y h_dvd h36
    rcases Finset.mem_union.mp h36 with hy | hy
    · rw [mem_S3] at hy; rw [hy] at h_dvd; omega
    · rw [mem_S6] at hy; rw [hy] at h_dvd; omega
  have hdT : Disjoint (S3 ∪ S6) TF := by
    rw [Finset.disjoint_left]
    intro y hy36 hyT
    refine h_not36 y ?_ hy36
    have := Subgroup.orderOf_dvd_natCard (T : Subgroup G) ((mem_TF _).mp hyT)
    rwa [h8] at this
  -- 8 + 8 + 8 = 24 pins the union to be everything
  have hU_card : (S3 ∪ S6 ∪ TF).card = S3.card + S6.card + TF.card := by
    rw [Finset.card_union_of_disjoint hdT, Finset.card_union_of_disjoint hd36]
  have h_le_univ : (S3 ∪ S6 ∪ TF).card ≤ 24 := by
    have := Finset.card_le_univ (S3 ∪ S6 ∪ TF)
    rwa [← Nat.card_eq_fintype_card, h] at this
  have hS6_card : S6.card = 8 := by
    rw [hU_card, hS3_card, hTF_card] at h_le_univ
    omega
  have hU_univ : S3 ∪ S6 ∪ TF = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hU_card, hS3_card, hS6_card, hTF_card, ← Nat.card_eq_fintype_card, h]
  -- x has 2-power order, so it can only sit in the TF part
  have hx_mem : x ∈ S3 ∪ S6 ∪ TF := hU_univ ▸ Finset.mem_univ x
  rcases Finset.mem_union.mp hx_mem with hx36 | hxT
  · exact absurd hx36 (h_not36 x hx)
  · exact (mem_TF _).mp hxT

/-- Counting core: a central involution `z` forces a unique Sylow 2-subgroup when
`n₃ = 4`: any two Sylow 2-subgroups consist of 2-power-order elements, hence contain
each other. -/
private lemma sylow2_card_one_of_central_invol {G : Type*} [Group G]
    (h : Nat.card G = 24) (h_n3 : Nat.card (Sylow 3 G) = 4) {z : G}
    (hz : orderOf z = 2) (hz_mem : z ∈ Subgroup.center G) :
    Nat.card (Sylow 2 G) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; decide)
  have h_le : ∀ T₁ T₂ : Sylow 2 G, (T₁ : Subgroup G) ≤ T₂ := by
    intro T₁ T₂ x hx
    refine two_power_order_mem_sylow2_of_central_invol h h_n3 hz hz_mem T₂ x ?_
    have h_dvd := Subgroup.orderOf_dvd_natCard (T₁ : Subgroup G) hx
    rwa [sylow_card_eq (p := 2) (q := 3) (by decide)
      (show Nat.card G = 2 ^ 3 * 3 ^ 1 by rw [h]; ring) T₁] at h_dvd
  haveI : Subsingleton (Sylow 2 G) :=
    ⟨fun T₁ T₂ => Sylow.ext (le_antisymm (h_le T₁ T₂) (h_le T₂ T₁))⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨default⟩⟩

/-- An order-2 action kernel forces a normal Sylow 2-subgroup, since the kernel is
generated by a central involution. -/
private lemma sylow2_card_one_of_ker_two {G : Type*} [Group G] (h : Nat.card G = 24)
    (h_n3 : Nat.card (Sylow 3 G) = 4)
    (h_ker : Nat.card (MulAction.toPermHom G (Sylow 3 G)).ker = 2) :
    Nat.card (Sylow 2 G) = 1 := by
  obtain ⟨z, hz2, hz_c⟩ := exists_central_involution_of_normal_card_two h_ker
  exact sylow2_card_one_of_central_invol h h_n3 hz2 hz_c

/-- Order-2-kernel case: the kernel is a central involution, forcing a normal Sylow-2 `T`
with `G ≃* T ⋊ C_3` non-trivially; `T ≃ C_2³` gives `C_2 × A_4`, `T ≃ Q_8` gives
`SL_2(𝔽_3)`. -/
private lemma order24_4_sylow3_ker_two {G : Type*} [Group G] (h : Nat.card G = 24)
    (h_n3 : Nat.card (Sylow 3 G) = 4)
    (h_ker : Nat.card (MulAction.toPermHom G (Sylow 3 G)).ker = 2) :
    Nonempty (G ≃* CyclicGroup 2 × AlternatingGroup 4) ∨
    Nonempty (G ≃* SL2 3) :=
  order24_4_sylow3_normal_sylow2 h h_n3 (sylow2_card_one_of_ker_two h h_n3 h_ker)

/-- A group of order `24` with four Sylow 3-subgroups is isomorphic to one of the three
    non-normal-Sylow-3 groups: `S_4`, `C_2 × A_4`, or `SL(2, 𝔽_3)`. The precondition is
    equivalent to not having a normal Sylow 3-subgroup. -/
lemma order24_4_sylow3 {G : Type*} [Group G] (h : Nat.card G = 24)
    (h_n3 : Nat.card (Sylow 3 G) = 4) :
    Nonempty (G ≃* SymmetricGroup 4) ∨
    Nonempty (G ≃* CyclicGroup 2 × AlternatingGroup 4) ∨
    Nonempty (G ≃* SL2 3) := by
  rcases sylow3_action_ker_card_dvd_two h h_n3 with h_ker | h_ker
  · exact Or.inl (order24_4_sylow3_ker_one h h_n3 h_ker)
  · rcases order24_4_sylow3_ker_two h h_n3 h_ker with h' | h' <;> tauto

/-- A group of order `24` is isomorphic to one of the 15 groups of order 24:
    five from a trivial Sylow-3 conjugation action, seven from a non-trivial action, and
    three from the non-normal-Sylow-3 case. -/
theorem order24_classification {G : Type*} [Group G] (h : Nat.card G = 24) :
    Nonempty (G ≃* CyclicGroup 3 × CyclicGroup 8) ∨
    Nonempty (G ≃* CyclicGroup 3 × (CyclicGroup 4 × CyclicGroup 2)) ∨
    Nonempty (G ≃* CyclicGroup 3 × (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2)) ∨
    Nonempty (G ≃* CyclicGroup 3 × DihedralGroup 4) ∨
    Nonempty (G ≃* CyclicGroup 3 × QuaternionGroup 2) ∨
    Nonempty (G ≃* CyclicGroup 3 ⋊[c8OnCqInv 3] CyclicGroup 8) ∨
    Nonempty (G ≃* DihedralGroup 3 × CyclicGroup 4) ∨
    Nonempty (G ≃* CyclicGroup 2 × QuaternionGroup 3) ∨
    Nonempty (G ≃* DihedralGroup 3 × (CyclicGroup 2 × CyclicGroup 2)) ∨
    Nonempty (G ≃* DihedralGroup 12) ∨
    Nonempty (G ≃* QuaternionGroup 6) ∨
    Nonempty (G ≃* CyclicGroup 3 ⋊[d4OnCqInv 3] DihedralGroup 4) ∨
    Nonempty (G ≃* SymmetricGroup 4) ∨
    Nonempty (G ≃* CyclicGroup 2 × AlternatingGroup 4) ∨
    Nonempty (G ≃* SL2 3) := by
  rcases sylow3_24 h with h_n3_1 | h_n3_4
  · rcases order24_1_sylow3 h h_n3_1 with
      (_ | _ | _ | _ | _) | (_ | _ | _ | _ | _ | _ | _) <;> tauto
  · rcases order24_4_sylow3 h h_n3_4 with _ | _ | _ <;> tauto
