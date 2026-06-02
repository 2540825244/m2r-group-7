import «M2rGroup7».SixteenClassification.Preliminary
import «M2rGroup7».SixteenClassification.Blueprints
import «M2rGroup7».SixteenClassification.Extensions

/-!
# Wild's Lemma 3 for groups of order 16

This file develops the case analysis required to prove
`OrderSixteen.realise_ext_type_if_not_iso_to_C2_4`, the formalisation of
Lemma 3 of Marcel Wild's paper *The Groups of Order Sixteen Made Easy*
(Amer. Math. Monthly **112** (2005), 20-31).

The strategy follows Wild's proof:

1. Transfer a `RealiseExtType` along a group isomorphism
   (`RealiseExtType.transfer`, `realise_of_mulEquiv`).
2. From a normal subgroup of index 2 and a coset representative, manufacture
   the associated extension type and its realisation
   (`exists_inducing_element`, `realise_from_normal_index_two`).
3. Split into the two big cases coming from the preceding lemma
   `exists_normal_C8_or_C4_C2`:
   - `realise_with_normal_C8`: normal `C_8`, yielding one of `ext_16_{1,5,6,7,8,9}`.
   - `realise_with_normal_K8`: normal `C_4 × C_2`, yielding one of
     `ext_16_{2,3,4,10,11,12,13}`.

Each per-case sublemma is stated with `sorry`; only the structural transfer
construction is fully proved here.
-/

namespace OrderSixteen

/-! ## Transfer along a group isomorphism -/

/-- Transfer a realisation of an extension type along a group isomorphism.
If `e : G ≃* G'` and `R` realises `E` in `G'`, then we obtain a realisation
of `E` in `G` by composing with `e⁻¹`. -/
noncomputable def RealiseExtType.transfer
    {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') {E : ExtensionType} (R : RealiseExtType G' E) :
    RealiseExtType G E where
  a := e.symm R.a
  ι := (e.symm : G' →* G).comp R.ι
  act_a := by
    intro x
    show e.symm R.a * e.symm (R.ι x) * (e.symm R.a)⁻¹ = e.symm (R.ι (E.act x))
    have h := R.act_a x
    rw [← map_inv e.symm, ← map_mul e.symm, ← map_mul e.symm, h]
  pow_a_n := by
    show (e.symm R.a) ^ E.n = e.symm (R.ι E.glue)
    rw [← map_pow e.symm, R.pow_a_n]
  equiv := R.equiv.trans e.symm.toEquiv
  equiv_apply := by
    intro x i
    show e.symm (R.equiv (x, i)) = e.symm (R.ι x) * (e.symm R.a) ^ (i : ℕ)
    rw [R.equiv_apply, map_mul, map_pow]

/-- If `G ≃* G'` and `G'` realises an extension type `E`, then so does `G`. -/
theorem realise_of_mulEquiv
    {G G' : Type*} [Group G] [Group G']
    {E : ExtensionType}
    (e : G ≃* G') (h : Nonempty (RealiseExtType G' E)) :
    Nonempty (RealiseExtType G E) :=
  h.map (RealiseExtType.transfer e)

/-! ## Inducing elements for an index-2 normal subgroup -/

/-- For any normal subgroup `H` of index 2 in `G`, there exists an "inducing"
element `a ∈ G` with `a ∉ H` and `a^2 ∈ H`. -/
lemma exists_inducing_element
    {G : Type*} [Group G] (H : Subgroup G) [H.Normal] (h_index : H.index = 2) :
    ∃ a : G, a ∉ H ∧ a ^ 2 ∈ H := by
  obtain ⟨a, ha_not, hall⟩ := Subgroup.index_eq_two_iff_exists_notMem_and'.mp h_index
  refine ⟨a, ha_not, ?_⟩
  rcases hall a with h | h
  · simpa [sq] using h
  · exact (ha_not h).elim

/-- Construct a realisation of an extension type from a normal subgroup of
index 2 together with an inducing element.

Given `H ◁ G` of index 2 and `a ∈ G \ H`, set `v := a^2 ∈ H` and let
`τ ∈ Aut(H)` be conjugation by `a`. Then `G` realises the extension type
`(H, 2, τ, v)`. -/
noncomputable def realise_from_normal_index_two
    {G : Type*} [Group G]
    (H : Subgroup G) [H.Normal] (h_index : H.index = 2)
    (a : G) (h_a_notMem : a ∉ H) (h_a_sq : a ^ 2 ∈ H) :
    Σ (E : ExtensionType), RealiseExtType G E := by
  classical
  have hcoset : ∀ g : G, g ∉ H → g * a⁻¹ ∈ H := by
    obtain ⟨a₀, _, hall⟩ :=
      Subgroup.index_eq_two_iff_exists_notMem_and'.mp h_index
    intro g hg
    have ha_inv_notMem : a⁻¹ ∉ H := fun ha => h_a_notMem (by simpa using inv_mem ha)
    rcases hall (g * a⁻¹) with h1 | h1
    · rcases hall a⁻¹ with h2 | h2
      · have hmul : (a₀ * a⁻¹)⁻¹ * (a₀ * (g * a⁻¹)) ∈ H :=
          mul_mem (inv_mem h2) h1
        have eq1 : (a₀ * a⁻¹)⁻¹ * (a₀ * (g * a⁻¹)) = a * g * a⁻¹ := by group
        rw [eq1] at hmul
        have hconj := ‹H.Normal›.conj_mem' _ hmul a
        have eq2 : a⁻¹ * (a * g * a⁻¹) * a = g := by group
        rw [eq2] at hconj
        exact (hg hconj).elim
      · exact (ha_inv_notMem h2).elim
    · exact h1
  let τ : MulAut H :=
    { toFun := fun h => ⟨a * h.1 * a⁻¹, ‹H.Normal›.conj_mem h.1 h.2 a⟩
      invFun := fun h => ⟨a⁻¹ * h.1 * a, by
        have := ‹H.Normal›.conj_mem' h.1 h.2 a
        simpa using this⟩
      left_inv := by intro h; ext; simp; group
      right_inv := by intro h; ext; simp; group
      map_mul' := by intro x y; ext; simp; group }
  let v : H := ⟨a ^ 2, h_a_sq⟩
  have hmap_glue : τ v = v := by
    ext
    show a * a ^ 2 * a⁻¹ = a ^ 2
    group
  have hpow_n : τ ^ 2 = MulAut.conj v := by
    ext h
    show (τ (τ h)).1 = v.1 * h.1 * v.1⁻¹
    show a * (a * h.1 * a⁻¹) * a⁻¹ = a^2 * h.1 * (a^2)⁻¹
    rw [pow_two, mul_inv_rev]
    group
  let E : ExtensionType :=
    { N := H, n := 2, act := τ, glue := v,
      map_glue := hmap_glue, pow_n := hpow_n }
  refine ⟨E, ?_⟩
  let toFun : H × Fin 2 → G := fun p => p.1.1 * a ^ (p.2 : ℕ)
  let invFun : G → H × Fin 2 := fun g =>
    if hg : g ∈ H then (⟨g, hg⟩, 0)
    else (⟨g * a⁻¹, hcoset g hg⟩, 1)
  have left_inv : Function.LeftInverse invFun toFun := by
    rintro ⟨h, i⟩
    fin_cases i
    · show invFun (h.1 * a ^ (0 : ℕ)) = (h, (0 : Fin 2))
      have hh : h.1 ∈ H := h.2
      have hsimp : h.1 * a ^ (0 : ℕ) = h.1 := by simp
      rw [hsimp]
      show (if hg : h.1 ∈ H then ((⟨h.1, hg⟩ : H), (0 : Fin 2))
            else (⟨h.1 * a⁻¹, hcoset h.1 hg⟩, 1)) = (h, 0)
      rw [dif_pos hh]
    · show invFun (h.1 * a ^ ((1 : Fin 2) : ℕ)) = (h, (1 : Fin 2))
      have hh_a_notMem : h.1 * a ∉ H := by
        intro hcontra
        have hh : h.1⁻¹ ∈ H := inv_mem h.2
        have h2 : h.1⁻¹ * (h.1 * a) ∈ H := mul_mem hh hcontra
        have : h.1⁻¹ * (h.1 * a) = a := by group
        rw [this] at h2
        exact h_a_notMem h2
      have hsimp : h.1 * a ^ ((1 : Fin 2) : ℕ) = h.1 * a := by
        show h.1 * a ^ (1 : ℕ) = h.1 * a
        rw [pow_one]
      rw [hsimp]
      show (if hg : h.1 * a ∈ H then ((⟨h.1 * a, hg⟩ : H), (0 : Fin 2))
            else (⟨(h.1 * a) * a⁻¹, hcoset (h.1 * a) hg⟩, 1)) = (h, 1)
      rw [dif_neg hh_a_notMem]
      ext
      · show h.1 * a * a⁻¹ = h.1
        group
      · rfl
  have right_inv : Function.RightInverse invFun toFun := by
    intro g
    by_cases hg : g ∈ H
    · show toFun (invFun g) = g
      have : invFun g = (⟨g, hg⟩, (0 : Fin 2)) := dif_pos hg
      rw [this]
      show g * a ^ ((0 : Fin 2) : ℕ) = g
      simp
    · show toFun (invFun g) = g
      have : invFun g = (⟨g * a⁻¹, hcoset g hg⟩, (1 : Fin 2)) := dif_neg hg
      rw [this]
      show g * a⁻¹ * a ^ ((1 : Fin 2) : ℕ) = g
      show g * a⁻¹ * a ^ (1 : ℕ) = g
      rw [pow_one]
      group
  let myEquiv : H × Fin 2 ≃ G :=
    { toFun := toFun
      invFun := invFun
      left_inv := left_inv
      right_inv := right_inv }
  exact
    { a := a
      ι := H.subtype
      act_a := by
        intro x
        show a * x.1 * a⁻¹ = (τ x).1
        rfl
      pow_a_n := by
        show a ^ 2 = v.1
        rfl
      equiv := myEquiv
      equiv_apply := by
        intro x i
        show x.1 * a ^ (i : ℕ) = x.1 * a ^ (i : ℕ)
        rfl }

/-! ## Case analysis: normal `C_8` -/

/-- If `G` is a group of order 16 containing a normal subgroup isomorphic to
`CyclicGroup 8`, then `G` realises one of the six `C_8`-based extension types
`ext_16_1`, `ext_16_5`, `ext_16_6`, `ext_16_7`, `ext_16_8`, `ext_16_9`. -/
lemma realise_with_normal_C8
    {G : Type*} [Group G]
    (hn : Nat.card G = 16)
    (H : Subgroup G) [H.Normal] (h_iso : Nonempty (H ≃* CyclicGroup 8)) :
    Nonempty (RealiseExtType G ext_16_1) ∨
    Nonempty (RealiseExtType G ext_16_5) ∨
    Nonempty (RealiseExtType G ext_16_6) ∨
    Nonempty (RealiseExtType G ext_16_7) ∨
    Nonempty (RealiseExtType G ext_16_8) ∨
    Nonempty (RealiseExtType G ext_16_9) := by
  sorry

/-! ## Case analysis: normal `K_8 = C_4 × C_2` -/

/-- If `G` is a group of order 16 containing a normal subgroup isomorphic to
`CyclicGroup 4 × CyclicGroup 2`, then `G` realises one of the seven
`K_8`-based extension types `ext_16_2`, `ext_16_3`, `ext_16_4`,
`ext_16_10`, `ext_16_11`, `ext_16_12`, `ext_16_13`. -/
lemma realise_with_normal_K8
    {G : Type*} [Group G]
    (hn : Nat.card G = 16)
    (H : Subgroup G) [H.Normal]
    (h_iso : Nonempty (H ≃* CyclicGroup 4 × CyclicGroup 2)) :
    Nonempty (RealiseExtType G ext_16_2) ∨
    Nonempty (RealiseExtType G ext_16_3) ∨
    Nonempty (RealiseExtType G ext_16_4) ∨
    Nonempty (RealiseExtType G ext_16_10) ∨
    Nonempty (RealiseExtType G ext_16_11) ∨
    Nonempty (RealiseExtType G ext_16_12) ∨
    Nonempty (RealiseExtType G ext_16_13) := by
  sorry

end OrderSixteen
