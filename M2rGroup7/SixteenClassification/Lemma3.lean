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
`(H, 2, τ, v)`. The return type exposes `τ`, the validity proofs, and
the realisation as a flat `Σ'`, with `N := ↥H` pinned syntactically so
downstream callers can chain with `RealiseExtType.transferN` without
losing the connection between `E.N` and `↥H`. -/
noncomputable def realise_from_normal_index_two
    {G : Type*} [Group G]
    (H : Subgroup G) [H.Normal] (h_index : H.index = 2)
    (a : G) (h_a_notMem : a ∉ H) (h_a_sq : a ^ 2 ∈ H) :
    Σ' (τ : MulAut H) (hmap : τ (⟨a ^ 2, h_a_sq⟩ : H) = ⟨a ^ 2, h_a_sq⟩)
       (hpow : τ ^ 2 = MulAut.conj (⟨a ^ 2, h_a_sq⟩ : H)),
      RealiseExtType G { N := H, n := 2, act := τ, glue := ⟨a ^ 2, h_a_sq⟩,
                         map_glue := hmap, pow_n := hpow } := by
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
  refine ⟨τ, hmap_glue, hpow_n, ?_⟩
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

/-- A version of `realise_from_normal_index_two` that also exposes the conjugation property
of `τ_H`, the action by `a` on `H`. -/
noncomputable def realise_from_normal_index_two_with_conj
    {G : Type*} [Group G]
    (H : Subgroup G) [H.Normal] (h_index : H.index = 2)
    (a : G) (h_a_notMem : a ∉ H) (h_a_sq : a ^ 2 ∈ H) :
    Σ' (τ : MulAut H) (hmap : τ (⟨a ^ 2, h_a_sq⟩ : H) = ⟨a ^ 2, h_a_sq⟩)
       (hpow : τ ^ 2 = MulAut.conj (⟨a ^ 2, h_a_sq⟩ : H))
       (_ : ∀ x : H, ((τ x : H) : G) = a * (x : G) * a⁻¹),
      RealiseExtType G { N := H, n := 2, act := τ, glue := ⟨a ^ 2, h_a_sq⟩,
                         map_glue := hmap, pow_n := hpow } := by
  let res := realise_from_normal_index_two H h_index a h_a_notMem h_a_sq
  refine ⟨res.1, res.2.1, res.2.2.1, ?_, res.2.2.2⟩
  intro x
  rfl

/-! ## Glue: ExtEquiv-based matching helper -/

/-- Transfer a realisation along an `ExtEquiv`: given `R_src : RealiseExtType G E_src`,
a witness `R_tgt' : RealiseExtType G' E_tgt`, and `eq : ExtEquiv E_src E_tgt`, build
`RealiseExtType G E_tgt`.

Chains `ExtEquiv.realisingEquiv` (which gives `G ≃* G'`) with `RealiseExtType.transfer`. -/
noncomputable def RealiseExtType.transfer_along_extEquiv
    {G G' : Type*} [Group G] [Group G']
    {E_src E_tgt : ExtensionType}
    (R_src : RealiseExtType G E_src)
    (R_tgt' : RealiseExtType G' E_tgt)
    (eq : ExtEquiv E_src E_tgt) :
    RealiseExtType G E_tgt :=
  RealiseExtType.transfer (ExtEquiv.realisingEquiv eq R_src R_tgt') R_tgt'

/-- Conjugate an `ExtensionType` along an isomorphism of its underlying normal group. -/
def ExtensionType.conjN
    (E : ExtensionType)
    {N' : Type*} [Group N']
    (e : E.N ≃* N') : ExtensionType where
  N := N'
  n := E.n
  act := (e.symm.trans E.act).trans e
  glue := e E.glue
  map_glue := by
    show e (E.act (e.symm (e E.glue))) = e E.glue
    rw [MulEquiv.symm_apply_apply, E.map_glue]
  pow_n := by
    -- Pointwise: ((e.symm.trans E.act).trans e)^n x = e (E.act^n (e.symm x))
    have T_pow : ∀ k : ℕ, ∀ x : N',
        (((e.symm.trans E.act).trans e) ^ k) x = e ((E.act ^ k) (e.symm x)) := by
      intro k
      induction k with
      | zero =>
        intro x
        show x = e (e.symm x)
        rw [MulEquiv.apply_symm_apply]
      | succ k ih =>
        intro x
        rw [pow_succ', MulAut.mul_apply, ih]
        show e (E.act (e.symm (e ((E.act ^ k) (e.symm x))))) =
             e ((E.act ^ (k + 1)) (e.symm x))
        rw [MulEquiv.symm_apply_apply, pow_succ', MulAut.mul_apply]
    ext x
    rw [T_pow E.n]
    have hpow := E.pow_n
    have hx := DFunLike.congr_fun hpow (e.symm x)
    show e ((E.act ^ E.n) (e.symm x)) = (e E.glue) * x * (e E.glue)⁻¹
    rw [hx]
    show e (E.glue * (e.symm x) * E.glue⁻¹) = e E.glue * x * (e E.glue)⁻¹
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

/-- Transport a realisation across an isomorphism of the underlying normal group.

If `R : RealiseExtType G E` and `e : E.N ≃* N'`, then `G` realises `E.conjN e`,
i.e. the extension with `N` replaced by `N'`, `act` conjugated by `e`, and `glue`
mapped through `e`. The same inducing element `a ∈ G` works; only the embedding
`ι` is precomposed with `e.symm`. -/
noncomputable def RealiseExtType.transferN
    {G : Type*} [Group G]
    {E : ExtensionType}
    {N' : Type*} [Group N']
    (e : E.N ≃* N')
    (R : RealiseExtType G E) :
    RealiseExtType G (E.conjN e) where
  a := R.a
  ι := R.ι.comp e.symm.toMonoidHom
  act_a := by
    intro x
    show R.a * R.ι (e.symm x) * R.a⁻¹ = R.ι (e.symm (e (E.act (e.symm x))))
    rw [MulEquiv.symm_apply_apply, R.act_a]
  pow_a_n := by
    show R.a ^ E.n = R.ι (e.symm (e E.glue))
    rw [MulEquiv.symm_apply_apply, R.pow_a_n]
  equiv := (Equiv.prodCongr e.symm.toEquiv (Equiv.refl _)).trans R.equiv
  equiv_apply := by
    intro x i
    show R.equiv (e.symm x, i) = R.ι (e.symm x) * R.a ^ (i : ℕ)
    rw [R.equiv_apply]

/-- For a finite group `G` with a normal subgroup `H` of index 2, there exists an
inducing element `a ∉ H` with `a^2 ∈ H` whose order is minimal among elements of `G \ H`.
-/
lemma exists_min_order_inducing_element
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal] (h_index : H.index = 2) :
    ∃ a : G, a ∉ H ∧ a ^ 2 ∈ H ∧
      ∀ b : G, b ∉ H → b ^ 2 ∈ H → orderOf a ≤ orderOf b := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  -- The set of (order, element) pairs for inducing elements is nonempty and finite.
  have h_all_sq : ∀ b : G, b ^ 2 ∈ H := by
    intro b
    have := Subgroup.pow_index_mem H b
    rw [h_index] at this
    exact this
  obtain ⟨a0, ha0_not, _⟩ := exists_inducing_element H h_index
  let S : Finset G := (Finset.univ : Finset G).filter (· ∉ H)
  have hS_nonempty : S.Nonempty := ⟨a0, by simp [S, ha0_not]⟩
  let f : G → ℕ := fun g => orderOf g
  obtain ⟨a, ha_mem, ha_min⟩ := S.exists_min_image f hS_nonempty
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at ha_mem
  refine ⟨a, ha_mem, h_all_sq a, ?_⟩
  intro b hb _
  have : b ∈ S := by simp [S, hb]
  exact ha_min b this

/-! ## Case analysis: normal `C_8`

The plan for `realise_with_normal_C8`:

1. Obtain a minimum-order inducing element `a ∉ H` with `a^2 ∈ H`
   via `exists_min_order_inducing_element`.
2. Build `R_H : RealiseExtType G E_H` with `E_H.N = ↥H`
   via `realise_from_normal_index_two`.
3. Transfer along `e : ↥H ≃* CyclicGroup 8` (from `h_iso`)
   using `RealiseExtType.transferN` to land on
   `R_C8 : RealiseExtType G (E_H.conjN e)`.
4. Dispatch on the resulting automorphism via `MulAut.forall_eq_C8`
   into the four cases `{1, c2OnC8Pow3, c2OnC8Pow5, c2OnC8Pow7}`.
5. For each `τ'`, sub-dispatch on the glue element `v' ∈ CyclicGroup 8`
   (8 possibilities, restricted by the validity condition `τ' v' = v'`).
6. For each `(τ', v')` pair, construct an `ExtEquiv` to the matching
   `ext_16_i` (using `extension_families_same_isoClasses` or
   `conjugateActEquiv` to bridge glue/action differences) and apply
   `RealiseExtType.transfer_along_extEquiv`.

The four foundational helpers needed for this plan are now in place
(`transferN`, `conjN`, `transfer_along_extEquiv`,
`exists_min_order_inducing_element`). What remains is the explicit
case-by-case construction of the per-case `ExtEquiv` witnesses.
-/

/-- If `G` is a group of order 16 containing a normal subgroup isomorphic to
`CyclicGroup 8`, then `G` realises one of the six `C_8`-based extension types
`ext_16_1`, `ext_16_5`, `ext_16_6`, `ext_16_7`, `ext_16_8`, `ext_16_9`.

The proof picks a coset representative `a ∉ H` of minimum order, then case-splits
on `orderOf a ∈ {2, 4, 8, 16}`. The `o(a) = 2` branch dispatches on
`MulAut.forall_eq_C8` to yield `ext_16_{5,6,7,8}`. The `o(a) = 4` branch yields
`ext_16_9` (with τ forced to be inversion via min-order). The `o(a) = 8` case
is ruled out by min-order. The `o(a) = 16` branch yields `ext_16_1` directly
since `G` is cyclic. -/
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
  classical
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hn]; decide)
  -- Deduce H.index = 2 from |G|=16 and |H|=|C_8|=8
  have h_card_H : Nat.card H = 8 := by
    rw [Nat.card_congr h_iso.some.toEquiv, card_cyclicGroup]
  have h_index : H.index = 2 := by
    have h := Subgroup.index_mul_card H
    rw [h_card_H, hn] at h
    omega
  obtain ⟨e⟩ := h_iso
  obtain ⟨a, ha_notMem, ha_sq, ha_min⟩ :=
    exists_min_order_inducing_element H h_index
  obtain ⟨τ_H, hmap_H, hpow_H, hconj_H, R_H⟩ :=
    realise_from_normal_index_two_with_conj H h_index a ha_notMem ha_sq
  by_cases h_o2 : orderOf a = 2
  · -- o(a) = 2 case: a² = 1, so e ⟨a², _⟩ = 1 in CyclicGroup 8.
    have h_a_sq_eq : a ^ 2 = 1 := by
      have := pow_orderOf_eq_one a
      rw [h_o2] at this
      exact this
    have h_glue : e (⟨a ^ 2, ha_sq⟩ : H) = (1 : CyclicGroup 8) := by
      have hv : (⟨a ^ 2, ha_sq⟩ : H) = 1 := Subtype.ext h_a_sq_eq
      rw [hv]
      exact map_one e
    -- Conjugate τ_H over to MulAut (CyclicGroup 8) via e.
    rcases MulAut.forall_eq_C8 ((e.symm.trans τ_H).trans e) with hτ | hτ | hτ | hτ
    · -- τ_C8 = 1 → ext_16_5
      right; left
      refine ⟨RealiseExtType.transfer_along_extEquiv R_H realise_16_5
        { hn := rfl
          φ := e
          act_conj := hτ.symm
          act_glue := h_glue.symm }⟩
    · -- τ_C8 = pow3 → ext_16_8
      right; right; right; right; left
      refine ⟨RealiseExtType.transfer_along_extEquiv R_H realise_16_8
        { hn := rfl
          φ := e
          act_conj := hτ.symm
          act_glue := h_glue.symm }⟩
    · -- τ_C8 = pow5 → ext_16_6
      right; right; left
      refine ⟨RealiseExtType.transfer_along_extEquiv R_H realise_16_6
        { hn := rfl
          φ := e
          act_conj := hτ.symm
          act_glue := h_glue.symm }⟩
    · -- τ_C8 = pow7 → ext_16_7
      right; right; right; left
      refine ⟨RealiseExtType.transfer_along_extEquiv R_H realise_16_7
        { hn := rfl
          φ := e
          act_conj := hτ.symm
          act_glue := h_glue.symm }⟩
  · by_cases h_o16 : orderOf a = 16
    · -- o(a) = 16 case: ⟨a⟩ = G, so G is cyclic of order 16, realising ext_16_1.
      left
      have hcyc : IsCyclic G := isCyclic_of_orderOf_eq_card a (by rw [h_o16, hn])
      have iso : G ≃* CyclicGroup 16 := by
        have h : G ≃* Multiplicative (ZMod (Nat.card G)) := (zmodCyclicMulEquiv hcyc).symm
        rw [hn] at h
        exact h
      exact ⟨RealiseExtType.transfer iso realise_16_1⟩
    · -- o(a) ∈ {4, 8} cases. We rule out 8 by min-order, then handle 4 → ext_16_9.
      have h_ord_pos : 0 < orderOf a := orderOf_pos a
      have h_ord_dvd : orderOf a ∣ 16 := hn ▸ orderOf_dvd_natCard a
      have h_a_ne_one : a ≠ 1 := fun h => ha_notMem (h ▸ H.one_mem)
      have h_ord_ne_one : orderOf a ≠ 1 := fun h => h_a_ne_one (orderOf_eq_one_iff.mp h)
      -- The crucial computation: for any x : H, (a * x.1)^2 ∈ H with explicit form.
      have h_b_sq_eq : ∀ x : H,
          (a * (x : G)) ^ 2 = ((τ_H x : H) : G) * a ^ 2 * (x : G) := by
        intro x
        calc (a * (x : G)) ^ 2
            = a * (x : G) * (a * (x : G)) := by rw [sq]
          _ = (a * (x : G) * a⁻¹) * (a * a) * (x : G) := by group
          _ = ((τ_H x : H) : G) * a ^ 2 * (x : G) := by rw [hconj_H x, sq]
      have h_b_notMem : ∀ x : H, a * (x : G) ∉ H := by
        intro x hx
        have : a = (a * (x : G)) * (x : G)⁻¹ := by group
        exact ha_notMem (this ▸ H.mul_mem hx (H.inv_mem x.2))
      have h_b_sq_mem : ∀ x : H, (a * (x : G)) ^ 2 ∈ H := by
        intro x
        rw [h_b_sq_eq x]
        exact H.mul_mem (H.mul_mem (τ_H x).2 ha_sq) x.2
      -- Define τ_C8 and the key contradiction helper.
      set τ_C8 : MulAut (CyclicGroup 8) := (e.symm.trans τ_H).trans e with hτ_C8_def
      have h_b_sq_subtype : ∀ x : H,
          (a * (x : G)) ^ 2 = ((τ_H x * ⟨a ^ 2, ha_sq⟩ * x : H) : G) := by
        intro x
        rw [h_b_sq_eq x]
        rfl
      have hτH_eq : ∀ x : H, τ_H x = e.symm (τ_C8 (e x)) := by
        intro x
        change τ_H x = e.symm (e (τ_H (e.symm (e x))))
        rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
      have h_contra_helper : ∀ x : H,
          (e ((τ_H x) * ⟨a ^ 2, ha_sq⟩ * x) : CyclicGroup 8) = 1 → orderOf a ≤ 2 := by
        intro x hex
        have hH : ((τ_H x) * ⟨a ^ 2, ha_sq⟩ * x : H) = 1 := by
          have := e.injective (hex.trans (map_one e).symm)
          exact this
        have hb2_eq : (a * (x : G)) ^ 2 = 1 := by
          rw [h_b_sq_subtype x, hH]
          rfl
        have hb_order_dvd : orderOf (a * (x : G)) ∣ 2 :=
          orderOf_dvd_iff_pow_eq_one.mpr hb2_eq
        have hb_order_le : orderOf (a * (x : G)) ≤ 2 := Nat.le_of_dvd two_pos hb_order_dvd
        have := ha_min (a * (x : G)) (h_b_notMem x) (h_b_sq_mem x)
        omega
      have h_v_fixed : τ_C8 (e ⟨a ^ 2, ha_sq⟩) = e ⟨a ^ 2, ha_sq⟩ := by
        change e (τ_H (e.symm (e ⟨a ^ 2, ha_sq⟩))) = e ⟨a ^ 2, ha_sq⟩
        rw [MulEquiv.symm_apply_apply, hmap_H]
      -- Rule out orderOf a = 8.
      have h_o8 : orderOf a ≠ 8 := by
        intro h_o8_eq
        have ha2_ord : orderOf (a ^ 2) = 4 := by
          rw [orderOf_pow, h_o8_eq]; decide
        have ha2_H_ord : orderOf (⟨a ^ 2, ha_sq⟩ : H) = 4 := by
          have h := orderOf_injective H.subtype Subtype.val_injective (⟨a ^ 2, ha_sq⟩ : H)
          change orderOf (⟨a ^ 2, ha_sq⟩ : H) = 4
          rw [← h]; exact ha2_ord
        have he_ord : orderOf (e ⟨a ^ 2, ha_sq⟩) = 4 := by
          rw [e.orderOf_eq]; exact ha2_H_ord
        rcases MulAut.forall_eq_C8 τ_C8 with hτ | hτ | hτ | hτ
        · have he_cases :
              e ⟨a ^ 2, ha_sq⟩ = Multiplicative.ofAdd (2 : ZMod 8) ∨
              e ⟨a ^ 2, ha_sq⟩ = Multiplicative.ofAdd (6 : ZMod 8) := by
            have hv4 : (e ⟨a ^ 2, ha_sq⟩) ^ 4 = 1 := by
              rw [← he_ord]; exact pow_orderOf_eq_one _
            have hv2 : (e ⟨a ^ 2, ha_sq⟩) ^ 2 ≠ 1 := by
              intro h
              have : orderOf (e ⟨a ^ 2, ha_sq⟩) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
              rw [he_ord] at this
              omega
            have key : ∀ y : CyclicGroup 8, y ^ 4 = 1 → y ^ 2 ≠ 1 →
                y = Multiplicative.ofAdd (2 : ZMod 8) ∨
                y = Multiplicative.ofAdd (6 : ZMod 8) := by decide
            exact key _ hv4 hv2
          rcases he_cases with hv | hv
          · set x : H := e.symm (Multiplicative.ofAdd (3 : ZMod 8))
            have hex : e x = Multiplicative.ofAdd (3 : ZMod 8) := e.apply_symm_apply _
            have h_eq_one : (e ((τ_H x) * ⟨a ^ 2, ha_sq⟩ * x) : CyclicGroup 8) = 1 := by
              rw [map_mul, map_mul, hv, hex, hτH_eq x, hex, hτ,
                  MulAut.one_apply, e.apply_symm_apply]
              decide
            have := h_contra_helper x h_eq_one
            omega
          · set x : H := e.symm (Multiplicative.ofAdd (1 : ZMod 8))
            have hex : e x = Multiplicative.ofAdd (1 : ZMod 8) := e.apply_symm_apply _
            have h_eq_one : (e ((τ_H x) * ⟨a ^ 2, ha_sq⟩ * x) : CyclicGroup 8) = 1 := by
              rw [map_mul, map_mul, hv, hex, hτH_eq x, hex, hτ,
                  MulAut.one_apply, e.apply_symm_apply]
              decide
            have := h_contra_helper x h_eq_one
            omega
        · exfalso
          rw [hτ] at h_v_fixed
          have hv3 : (e ⟨a ^ 2, ha_sq⟩) ^ 3 = e ⟨a ^ 2, ha_sq⟩ := by
            have heq : c2OnC8Pow3 (Multiplicative.ofAdd 1) (e ⟨a ^ 2, ha_sq⟩) =
                (e ⟨a ^ 2, ha_sq⟩) ^ 3 := rfl
            rw [← heq]; exact h_v_fixed
          have hv_sq : (e ⟨a ^ 2, ha_sq⟩) ^ 2 = 1 := by
            have key : (e ⟨a ^ 2, ha_sq⟩) ^ 2 * (e ⟨a ^ 2, ha_sq⟩) =
                1 * (e ⟨a ^ 2, ha_sq⟩) := by
              rw [one_mul, ← pow_succ]; exact hv3
            exact mul_right_cancel key
          have hdvd : orderOf (e ⟨a ^ 2, ha_sq⟩) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hv_sq
          rw [he_ord] at hdvd
          omega
        · have he_cases :
              e ⟨a ^ 2, ha_sq⟩ = Multiplicative.ofAdd (2 : ZMod 8) ∨
              e ⟨a ^ 2, ha_sq⟩ = Multiplicative.ofAdd (6 : ZMod 8) := by
            have hv4 : (e ⟨a ^ 2, ha_sq⟩) ^ 4 = 1 := by
              rw [← he_ord]; exact pow_orderOf_eq_one _
            have hv2 : (e ⟨a ^ 2, ha_sq⟩) ^ 2 ≠ 1 := by
              intro h
              have : orderOf (e ⟨a ^ 2, ha_sq⟩) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
              rw [he_ord] at this
              omega
            have key : ∀ y : CyclicGroup 8, y ^ 4 = 1 → y ^ 2 ≠ 1 →
                y = Multiplicative.ofAdd (2 : ZMod 8) ∨
                y = Multiplicative.ofAdd (6 : ZMod 8) := by decide
            exact key _ hv4 hv2
          rcases he_cases with hv | hv
          · set x : H := e.symm (Multiplicative.ofAdd (1 : ZMod 8))
            have hex : e x = Multiplicative.ofAdd (1 : ZMod 8) := e.apply_symm_apply _
            have h_eq_one : (e ((τ_H x) * ⟨a ^ 2, ha_sq⟩ * x) : CyclicGroup 8) = 1 := by
              rw [map_mul, map_mul, hv, hex, hτH_eq x, hex, hτ, e.apply_symm_apply]
              decide
            have := h_contra_helper x h_eq_one
            omega
          · set x : H := e.symm (Multiplicative.ofAdd (3 : ZMod 8))
            have hex : e x = Multiplicative.ofAdd (3 : ZMod 8) := e.apply_symm_apply _
            have h_eq_one : (e ((τ_H x) * ⟨a ^ 2, ha_sq⟩ * x) : CyclicGroup 8) = 1 := by
              rw [map_mul, map_mul, hv, hex, hτH_eq x, hex, hτ, e.apply_symm_apply]
              decide
            have := h_contra_helper x h_eq_one
            omega
        · exfalso
          rw [hτ] at h_v_fixed
          have hv7 : (e ⟨a ^ 2, ha_sq⟩) ^ 7 = e ⟨a ^ 2, ha_sq⟩ := by
            have heq : c2OnC8Pow7 (Multiplicative.ofAdd 1) (e ⟨a ^ 2, ha_sq⟩) =
                (e ⟨a ^ 2, ha_sq⟩) ^ 7 := rfl
            rw [← heq]; exact h_v_fixed
          have hv6 : (e ⟨a ^ 2, ha_sq⟩) ^ 6 = 1 := by
            have key : (e ⟨a ^ 2, ha_sq⟩) ^ 6 * (e ⟨a ^ 2, ha_sq⟩) =
                1 * (e ⟨a ^ 2, ha_sq⟩) := by
              rw [one_mul, ← pow_succ]; exact hv7
            exact mul_right_cancel key
          have hd : orderOf (e ⟨a ^ 2, ha_sq⟩) ∣ 6 := orderOf_dvd_iff_pow_eq_one.mpr hv6
          rw [he_ord] at hd
          exact absurd hd (by decide)
      -- Conclude orderOf a = 4.
      have h_o4 : orderOf a = 4 := by
        have h16 : (16 : ℕ) = 2 ^ 4 := by decide
        rw [h16] at h_ord_dvd
        rcases (Nat.dvd_prime_pow Nat.prime_two (m := 4) (i := orderOf a)).mp h_ord_dvd
          with ⟨k, hk_le, hk_eq⟩
        interval_cases k
        · exact absurd hk_eq h_ord_ne_one
        · exact absurd hk_eq h_o2
        · exact hk_eq
        · exact absurd hk_eq h_o8
        · exact absurd hk_eq h_o16
      -- Now: o(a) = 4 case. Derive that e ⟨a²,_⟩ = ofAdd 4.
      right; right; right; right; right
      have ha4 : a ^ 4 = 1 := by rw [← h_o4]; exact pow_orderOf_eq_one a
      have ha2_ne_one : a ^ 2 ≠ 1 := by
        intro h
        have : orderOf a ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
        rw [h_o4] at this
        omega
      have ha2_H_ne_one : (⟨a ^ 2, ha_sq⟩ : H) ≠ 1 :=
        fun h => ha2_ne_one (congrArg Subtype.val h)
      have ha2_H_sq : (⟨a ^ 2, ha_sq⟩ : H) ^ 2 = 1 := by
        ext
        change (a ^ 2) ^ 2 = 1
        rw [← pow_mul]; exact ha4
      have h_glue_val : e (⟨a ^ 2, ha_sq⟩ : H) = Multiplicative.ofAdd (4 : ZMod 8) := by
        have he_sq : (e (⟨a ^ 2, ha_sq⟩ : H)) ^ 2 = 1 := by
          rw [← map_pow, ha2_H_sq, map_one]
        have he_ne_one : e (⟨a ^ 2, ha_sq⟩ : H) ≠ 1 := by
          intro h
          exact ha2_H_ne_one (e.injective (h.trans (map_one e).symm))
        have key : ∀ y : CyclicGroup 8, y ^ 2 = 1 → y ≠ 1 →
            y = Multiplicative.ofAdd (4 : ZMod 8) := by decide
        exact key _ he_sq he_ne_one
      -- Determine τ_C8: must be pow7 (else use h_contra_helper for contradiction).
      rcases MulAut.forall_eq_C8 τ_C8 with hτ | hτ | hτ | hτ
      · exfalso
        set x : H := e.symm (Multiplicative.ofAdd (2 : ZMod 8))
        have hex : e x = Multiplicative.ofAdd (2 : ZMod 8) := e.apply_symm_apply _
        have h_eq_one : (e ((τ_H x) * ⟨a ^ 2, ha_sq⟩ * x) : CyclicGroup 8) = 1 := by
          rw [map_mul, map_mul, h_glue_val, hex, hτH_eq x, hex, hτ,
              MulAut.one_apply, e.apply_symm_apply]
          decide
        have := h_contra_helper x h_eq_one
        omega
      · exfalso
        set x : H := e.symm (Multiplicative.ofAdd (1 : ZMod 8))
        have hex : e x = Multiplicative.ofAdd (1 : ZMod 8) := e.apply_symm_apply _
        have h_eq_one : (e ((τ_H x) * ⟨a ^ 2, ha_sq⟩ * x) : CyclicGroup 8) = 1 := by
          rw [map_mul, map_mul, h_glue_val, hex, hτH_eq x, hex, hτ, e.apply_symm_apply]
          decide
        have := h_contra_helper x h_eq_one
        omega
      · exfalso
        set x : H := e.symm (Multiplicative.ofAdd (2 : ZMod 8))
        have hex : e x = Multiplicative.ofAdd (2 : ZMod 8) := e.apply_symm_apply _
        have h_eq_one : (e ((τ_H x) * ⟨a ^ 2, ha_sq⟩ * x) : CyclicGroup 8) = 1 := by
          rw [map_mul, map_mul, h_glue_val, hex, hτH_eq x, hex, hτ, e.apply_symm_apply]
          decide
        have := h_contra_helper x h_eq_one
        omega
      · -- τ_C8 = pow7: produce realisation of ext_16_9.
        refine ⟨RealiseExtType.transfer_along_extEquiv R_H realise_16_9
          { hn := rfl
            φ := e
            act_conj := hτ.symm
            act_glue := h_glue_val.symm }⟩

/-! ## Case analysis: normal `K_8 = C_4 × C_2` -/

/-- If `G` is a group of order 16 containing a normal subgroup isomorphic to
`CyclicGroup 4 × CyclicGroup 2`, then `G` realises one of the seven
`K_8`-based extension types `ext_16_2`, `ext_16_3`, `ext_16_4`,
`ext_16_10`, `ext_16_11`, `ext_16_12`, `ext_16_13`.

The proof picks a coset representative `a ∉ H` of minimum order, then case-splits
on `orderOf a ∈ {2, 4, 8, 16}`. The `o(a) = 2` branch dispatches on
`MulAut.involution_K8_conj_to_rep` to obtain a conjugating automorphism `σ`
sliding the conjugated action `τ_K` into one of `{1, ψ₃, ψ₅, ψ₆}`, then emits
`ext_16_10`, `ext_16_11`, `ext_16_3`, `ext_16_13` respectively (each with glue
`(1, 1)` since `a² = 1`). The `o(a) = 16` branch is ruled out via cyclicity:
G cyclic of order 16 would force its subgroup `H ≃ K_8` to be cyclic too,
contradicted by K_8 having 4 elements with `x² = 1`. The `o(a) ∈ {4, 8}`
branches remain `sorry` because the lemma signature, as written, is too weak:
the group `G = CyclicGroup 8 × CyclicGroup 2` has `H ≃ K_8` as a normal
subgroup yet every element of `G \ H` has order 8, and none of the seven
K_8-family targets admits an order-4 glue. Resolving these branches requires
an additional hypothesis such as `(h_no_o8 : ∀ x : G, orderOf x ≠ 8)`. -/
lemma realise_with_normal_K8
    {G : Type*} [Group G]
    (hn : Nat.card G = 16)
    (h_no_o8 : ∀ x : G, orderOf x ≠ 8)
    (H : Subgroup G) [H.Normal]
    (h_iso : Nonempty (H ≃* CyclicGroup 4 × CyclicGroup 2)) :
    Nonempty (RealiseExtType G ext_16_2) ∨
    Nonempty (RealiseExtType G ext_16_3) ∨
    Nonempty (RealiseExtType G ext_16_4) ∨
    Nonempty (RealiseExtType G ext_16_10) ∨
    Nonempty (RealiseExtType G ext_16_11) ∨
    Nonempty (RealiseExtType G ext_16_12) ∨
    Nonempty (RealiseExtType G ext_16_13) := by
  classical
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hn]; decide)
  have h_card_H : Nat.card H = 8 := by
    rw [Nat.card_congr h_iso.some.toEquiv, Nat.card_prod,
        card_cyclicGroup, card_cyclicGroup]
  have h_index : H.index = 2 := by
    have h := Subgroup.index_mul_card H
    rw [h_card_H, hn] at h
    omega
  obtain ⟨e⟩ := h_iso
  obtain ⟨a, ha_notMem, ha_sq, ha_min⟩ :=
    exists_min_order_inducing_element H h_index
  obtain ⟨τ_H, hmap_H, hpow_H, hconj_H, R_H⟩ :=
    realise_from_normal_index_two_with_conj H h_index a ha_notMem ha_sq
  by_cases h_o2 : orderOf a = 2
  · -- o(a) = 2 branch: a^2 = 1, so glue = 1 in K_8. Dispatch on the four
    -- conjugacy representatives of τ_K via `MulAut.involution_K8_conj_to_rep`.
    have h_a_sq_eq : a ^ 2 = 1 := by
      have := pow_orderOf_eq_one a
      rw [h_o2] at this
      exact this
    have h_a_sq_H_eq : (⟨a ^ 2, ha_sq⟩ : H) = 1 := Subtype.ext h_a_sq_eq
    have h_glue : e (⟨a ^ 2, ha_sq⟩ : H) = (1 : CyclicGroup 4 × CyclicGroup 2) := by
      rw [h_a_sq_H_eq]
      exact map_one e
    set τ_K : MulAut (CyclicGroup 4 × CyclicGroup 2) :=
      (e.symm.trans τ_H).trans e with hτ_K_def
    have T_pow : ∀ k : ℕ, ∀ y : CyclicGroup 4 × CyclicGroup 2,
        (τ_K ^ k) y = e ((τ_H ^ k) (e.symm y)) := by
      intro k
      induction k with
      | zero =>
        intro y
        change y = e (e.symm y)
        rw [MulEquiv.apply_symm_apply]
      | succ k ih =>
        intro y
        rw [pow_succ', MulAut.mul_apply, ih]
        change e (τ_H (e.symm (e ((τ_H ^ k) (e.symm y))))) =
             e ((τ_H ^ (k + 1)) (e.symm y))
        rw [MulEquiv.symm_apply_apply, pow_succ', MulAut.mul_apply]
    have hτ_K_sq : τ_K ^ 2 = 1 := by
      apply MulEquiv.ext
      intro y
      rw [T_pow 2 y]
      have hx := DFunLike.congr_fun hpow_H (e.symm y)
      change e ((τ_H ^ 2) (e.symm y)) = y
      rw [hx]
      change e (MulAut.conj (⟨a ^ 2, ha_sq⟩ : H) (e.symm y)) = y
      rw [h_a_sq_H_eq, map_one MulAut.conj]
      change e (e.symm y) = y
      rw [MulEquiv.apply_symm_apply]
    obtain ⟨σ, hσ⟩ := MulAut.involution_K8_conj_to_rep τ_K hτ_K_sq
    set e' : H ≃* CyclicGroup 4 × CyclicGroup 2 := e.trans σ with he'_def
    have h_glue' : e' (⟨a ^ 2, ha_sq⟩ : H) = (1 : CyclicGroup 4 × CyclicGroup 2) := by
      change σ (e (⟨a ^ 2, ha_sq⟩ : H)) = 1
      rw [h_glue]
      exact map_one σ
    have h_conj_eq : (e'.symm.trans τ_H).trans e' = σ * τ_K * σ⁻¹ := by
      apply MulEquiv.ext
      intro x
      change σ (e (τ_H (e.symm (σ.symm x)))) = σ (τ_K (σ⁻¹ x))
      rfl
    rcases hσ with hσ | hσ | hσ | hσ
    · -- ψ = 1 → ext_16_10
      right; right; right; left
      have act_conj : (e'.symm.trans τ_H).trans e' = ext_16_10.act := by
        rw [h_conj_eq, hσ]
      refine ⟨RealiseExtType.transfer_along_extEquiv R_H realise_16_10
        { hn := rfl
          φ := e'
          act_conj := act_conj.symm
          act_glue := h_glue'.symm }⟩
    · -- ψ = ψ₃ → ext_16_11
      right; right; right; right; left
      have act_conj : (e'.symm.trans τ_H).trans e' = ext_16_11.act := by
        rw [h_conj_eq, hσ]
      refine ⟨RealiseExtType.transfer_along_extEquiv R_H realise_16_11
        { hn := rfl
          φ := e'
          act_conj := act_conj.symm
          act_glue := h_glue'.symm }⟩
    · -- ψ = ψ₅ → ext_16_3
      right; left
      have act_conj : (e'.symm.trans τ_H).trans e' = ext_16_3.act := by
        rw [h_conj_eq, hσ]
      refine ⟨RealiseExtType.transfer_along_extEquiv R_H realise_16_3
        { hn := rfl
          φ := e'
          act_conj := act_conj.symm
          act_glue := h_glue'.symm }⟩
    · -- ψ = ψ₆ → ext_16_13
      right; right; right; right; right; right
      have act_conj : (e'.symm.trans τ_H).trans e' = ext_16_13.act := by
        rw [h_conj_eq, hσ]
        rfl
      refine ⟨RealiseExtType.transfer_along_extEquiv R_H realise_16_13
        { hn := rfl
          φ := e'
          act_conj := act_conj.symm
          act_glue := h_glue'.symm }⟩
  · -- o(a) ∈ {4, 8, 16} branches.
    have h_ord_pos : 0 < orderOf a := orderOf_pos a
    have h_ord_dvd : orderOf a ∣ 16 := hn ▸ orderOf_dvd_natCard a
    have h_a_ne_one : a ≠ 1 := fun h => ha_notMem (h ▸ H.one_mem)
    have h_ord_ne_one : orderOf a ≠ 1 := fun h => h_a_ne_one (orderOf_eq_one_iff.mp h)
    -- Rule out orderOf a = 16: G cyclic ⇒ H cyclic ⇒ K_8 cyclic, contradiction.
    have h_o16 : orderOf a ≠ 16 := by
      intro h_o16_eq
      haveI hcyc : IsCyclic G := isCyclic_of_orderOf_eq_card a (by rw [h_o16_eq, hn])
      haveI : IsCyclic H := Subgroup.isCyclic H
      haveI : IsCyclic (CyclicGroup 4 × CyclicGroup 2) := e.isCyclic.mp ‹_›
      -- K_8 has 4 elements x with x² = 1; a cyclic group has at most 2.
      have hle :
          ((Finset.univ : Finset (CyclicGroup 4 × CyclicGroup 2)).filter
            (fun x => x ^ 2 = 1)).card ≤ 2 :=
        IsCyclic.card_pow_eq_one_le two_pos
      have hge :
          (4 : ℕ) ≤
            ((Finset.univ : Finset (CyclicGroup 4 × CyclicGroup 2)).filter
              (fun x => x ^ 2 = 1)).card := by
        decide
      omega
    -- Rule out orderOf a = 8 via the threaded hypothesis.
    have h_o8 : orderOf a ≠ 8 := h_no_o8 a
    -- Conclude orderOf a = 4.
    have h_o4 : orderOf a = 4 := by
      have h16 : (16 : ℕ) = 2 ^ 4 := by decide
      rw [h16] at h_ord_dvd
      rcases (Nat.dvd_prime_pow Nat.prime_two (m := 4) (i := orderOf a)).mp h_ord_dvd
        with ⟨k, hk_le, hk_eq⟩
      interval_cases k
      · exact absurd hk_eq h_ord_ne_one
      · exact absurd hk_eq h_o2
      · exact hk_eq
      · exact absurd hk_eq h_o8
      · exact absurd hk_eq h_o16
    -- The o(a) = 4 case body remains to be done. Plan: `a^2` has order 2 in H,
    -- so `e ⟨a², ha_sq⟩` is one of the three order-2 elements of K_8. Use
    -- `MulAut.involution_K8_conj_to_rep` (τ_K^2 = 1 because K_8 abelian makes
    -- `MulAut.conj v = 1`) to slide τ_K into a representative ψ. For each (ψ, v)
    -- pair, compose with an Aut(K_8)-element to align glue with the canonical
    -- glue of ext_16_{2, 4, 12}. The ψ_6 case yields a min-order contradiction
    -- via h_contra_helper. See milestones.md for the per-case mapping.
    sorry

end OrderSixteen
