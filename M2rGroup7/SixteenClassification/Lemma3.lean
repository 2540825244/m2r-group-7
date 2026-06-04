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
    change e.symm R.a * e.symm (R.ι x) * (e.symm R.a)⁻¹ = e.symm (R.ι (E.act x))
    have h := R.act_a x
    rw [← map_inv e.symm, ← map_mul e.symm, ← map_mul e.symm, h]
  pow_a_n := by
    change (e.symm R.a) ^ E.n = e.symm (R.ι E.glue)
    rw [← map_pow e.symm, R.pow_a_n]
  equiv := R.equiv.trans e.symm.toEquiv
  equiv_apply := by
    intro x i
    change e.symm (R.equiv (x, i)) = e.symm (R.ι x) * (e.symm R.a) ^ (i : ℕ)
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
      map_mul' := by intro x y; ext; simp }
  let v : H := ⟨a ^ 2, h_a_sq⟩
  have hmap_glue : τ v = v := by
    ext
    change a * a ^ 2 * a⁻¹ = a ^ 2
    group
  have hpow_n : τ ^ 2 = MulAut.conj v := by
    ext h
    change (τ (τ h)).1 = v.1 * h.1 * v.1⁻¹
    change a * (a * h.1 * a⁻¹) * a⁻¹ = a^2 * h.1 * (a^2)⁻¹
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
    · change invFun (h.1 * a ^ (0 : ℕ)) = (h, (0 : Fin 2))
      have hh : h.1 ∈ H := h.2
      have hsimp : h.1 * a ^ (0 : ℕ) = h.1 := by simp
      rw [hsimp]
      change (if hg : h.1 ∈ H then ((⟨h.1, hg⟩ : H), (0 : Fin 2))
            else (⟨h.1 * a⁻¹, hcoset h.1 hg⟩, 1)) = (h, 0)
      rw [dif_pos hh]
    · change invFun (h.1 * a ^ ((1 : Fin 2) : ℕ)) = (h, (1 : Fin 2))
      have hh_a_notMem : h.1 * a ∉ H := by
        intro hcontra
        have hh : h.1⁻¹ ∈ H := inv_mem h.2
        have h2 : h.1⁻¹ * (h.1 * a) ∈ H := mul_mem hh hcontra
        have : h.1⁻¹ * (h.1 * a) = a := by group
        rw [this] at h2
        exact h_a_notMem h2
      have hsimp : h.1 * a ^ ((1 : Fin 2) : ℕ) = h.1 * a := by
        change h.1 * a ^ (1 : ℕ) = h.1 * a
        rw [pow_one]
      rw [hsimp]
      change (if hg : h.1 * a ∈ H then ((⟨h.1 * a, hg⟩ : H), (0 : Fin 2))
            else (⟨(h.1 * a) * a⁻¹, hcoset (h.1 * a) hg⟩, 1)) = (h, 1)
      rw [dif_neg hh_a_notMem]
      ext
      · change h.1 * a * a⁻¹ = h.1
        group
      · rfl
  have right_inv : Function.RightInverse invFun toFun := by
    intro g
    by_cases hg : g ∈ H
    · change toFun (invFun g) = g
      have : invFun g = (⟨g, hg⟩, (0 : Fin 2)) := dif_pos hg
      rw [this]
      change g * a ^ ((0 : Fin 2) : ℕ) = g
      simp
    · change toFun (invFun g) = g
      have : invFun g = (⟨g * a⁻¹, hcoset g hg⟩, (1 : Fin 2)) := dif_neg hg
      rw [this]
      change g * a⁻¹ * a ^ ((1 : Fin 2) : ℕ) = g
      change g * a⁻¹ * a ^ (1 : ℕ) = g
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
        change a * x.1 * a⁻¹ = (τ x).1
        rfl
      pow_a_n := by
        change a ^ 2 = v.1
        rfl
      equiv := myEquiv
      equiv_apply := by
        intro x i
        change x.1 * a ^ (i : ℕ) = x.1 * a ^ (i : ℕ)
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
    change e (E.act (e.symm (e E.glue))) = e E.glue
    rw [MulEquiv.symm_apply_apply, E.map_glue]
  pow_n := by
    -- Pointwise: ((e.symm.trans E.act).trans e)^n x = e (E.act^n (e.symm x))
    have T_pow : ∀ k : ℕ, ∀ x : N',
        (((e.symm.trans E.act).trans e) ^ k) x = e ((E.act ^ k) (e.symm x)) := by
      intro k
      induction k with
      | zero =>
        intro x
        change x = e (e.symm x)
        rw [MulEquiv.apply_symm_apply]
      | succ k ih =>
        intro x
        rw [pow_succ', MulAut.mul_apply, ih]
        change e (E.act (e.symm (e ((E.act ^ k) (e.symm x))))) =
             e ((E.act ^ (k + 1)) (e.symm x))
        rw [MulEquiv.symm_apply_apply, pow_succ', MulAut.mul_apply]
    ext x
    rw [T_pow E.n]
    have hpow := E.pow_n
    have hx := DFunLike.congr_fun hpow (e.symm x)
    change e ((E.act ^ E.n) (e.symm x)) = (e E.glue) * x * (e E.glue)⁻¹
    rw [hx]
    change e (E.glue * (e.symm x) * E.glue⁻¹) = e E.glue * x * (e E.glue)⁻¹
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
    change R.a * R.ι (e.symm x) * R.a⁻¹ = R.ι (e.symm (e (E.act (e.symm x))))
    rw [MulEquiv.symm_apply_apply, R.act_a]
  pow_a_n := by
    change R.a ^ E.n = R.ι (e.symm (e E.glue))
    rw [MulEquiv.symm_apply_apply, R.pow_a_n]
  equiv := (Equiv.prodCongr e.symm.toEquiv (Equiv.refl _)).trans R.equiv
  equiv_apply := by
    intro x i
    change R.equiv (e.symm x, i) = R.ι (e.symm x) * R.a ^ (i : ℕ)
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
    -- o(a) = 4 branch: glue v = e ⟨a², _⟩ is an order-2 element of K_8.
    -- Use MulAut.involution_K8_conj_to_rep to slide τ_K to one of {1, ψ₃, ψ₅, ψ₆},
    -- then dispatch per (ψ, v) pair.
    have h_a4 : a ^ 4 = 1 := by rw [← h_o4]; exact pow_orderOf_eq_one a
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
      rw [← pow_mul]; exact h_a4
    -- K_8 is abelian, so conjugation by any element is trivial.
    have hconj_one : MulAut.conj (⟨a ^ 2, ha_sq⟩ : H) = 1 := by
      apply MulEquiv.ext
      intro x
      change (⟨a ^ 2, ha_sq⟩ : H) * x * (⟨a ^ 2, ha_sq⟩ : H)⁻¹ = x
      apply e.injective
      rw [map_mul, map_mul, map_inv]
      have hcomm : ∀ y z : CyclicGroup 4 × CyclicGroup 2, y * z = z * y :=
        fun y z => mul_comm y z
      rw [hcomm (e _) (e x), mul_assoc, mul_inv_cancel, mul_one]
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
    have h_b_sq_subtype : ∀ x : H,
        (a * (x : G)) ^ 2 = ((τ_H x * ⟨a ^ 2, ha_sq⟩ * x : H) : G) := by
      intro x
      rw [h_b_sq_eq x]
      rfl
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
      rw [hx, hconj_one]
      change e (e.symm y) = y
      rw [MulEquiv.apply_symm_apply]
    obtain ⟨σ, hσ⟩ := MulAut.involution_K8_conj_to_rep τ_K hτ_K_sq
    set e' : H ≃* CyclicGroup 4 × CyclicGroup 2 := e.trans σ with he'_def
    -- The glue under e' is σ (e ⟨a², _⟩); call it v_K'.
    set v_K' : CyclicGroup 4 × CyclicGroup 2 := e' (⟨a ^ 2, ha_sq⟩ : H) with hv_K'_def
    have hv_K'_sq : v_K' ^ 2 = 1 := by
      rw [hv_K'_def, ← map_pow, ha2_H_sq, map_one]
    have hv_K'_ne_one : v_K' ≠ 1 := by
      intro h
      apply ha2_H_ne_one
      exact e'.injective (h.trans (map_one e').symm)
    have h_conj_eq : (e'.symm.trans τ_H).trans e' = σ * τ_K * σ⁻¹ := by
      apply MulEquiv.ext
      intro x
      change σ (e (τ_H (e.symm (σ.symm x)))) = σ (τ_K (σ⁻¹ x))
      rfl
    have hτH_eq' : ∀ x : H,
        e' (τ_H x) = ((e'.symm.trans τ_H).trans e') (e' x) := by
      intro x
      change σ (e (τ_H x)) = σ (e (τ_H (e.symm (σ.symm (σ (e x))))))
      rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    -- Helper for min-order contradiction (mirror of C_8 branch).
    have h_contra_helper : ∀ x : H,
        (e' ((τ_H x) * ⟨a ^ 2, ha_sq⟩ * x) : CyclicGroup 4 × CyclicGroup 2) = 1 →
        orderOf a ≤ 2 := by
      intro x hex
      have hH : ((τ_H x) * ⟨a ^ 2, ha_sq⟩ * x : H) = 1 := by
        have := e'.injective (hex.trans (map_one e').symm)
        exact this
      have hb2_eq : (a * (x : G)) ^ 2 = 1 := by
        rw [h_b_sq_subtype x, hH]
        rfl
      have hb_order_dvd : orderOf (a * (x : G)) ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr hb2_eq
      have hb_order_le : orderOf (a * (x : G)) ≤ 2 := Nat.le_of_dvd two_pos hb_order_dvd
      have := ha_min (a * (x : G)) (h_b_notMem x) (h_b_sq_mem x)
      omega
    -- Classify order-2 elements of K_8.
    have order2_K8 : ∀ y : CyclicGroup 4 × CyclicGroup 2,
        y ^ 2 = 1 → y ≠ 1 →
        y = (Multiplicative.ofAdd 2, 1) ∨
        y = (1, Multiplicative.ofAdd 1) ∨
        y = (Multiplicative.ofAdd 2, Multiplicative.ofAdd 1) := by decide
    rcases order2_K8 v_K' hv_K'_sq hv_K'_ne_one with hv | hv | hv
    all_goals rcases hσ with hσ | hσ | hσ | hσ
    -- v = (ofAdd 2, 1) cases
    · -- v = (ofAdd 2, 1), ψ = 1: rule out via h_contra_helper.
      exfalso
      set x : H := e'.symm ((Multiplicative.ofAdd 1, 1) :
        CyclicGroup 4 × CyclicGroup 2) with hx_def
      have hex : e' x = (Multiplicative.ofAdd 1, 1) := e'.apply_symm_apply _
      have h_eq_one :
          (e' ((τ_H x) * ⟨a ^ 2, ha_sq⟩ * x) : CyclicGroup 4 × CyclicGroup 2) = 1 := by
        rw [map_mul, map_mul, ← hv_K'_def, hv, hτH_eq' x, hex, h_conj_eq, hσ]
        decide
      have := h_contra_helper x h_eq_one
      omega
    · -- v = (ofAdd 2, 1), ψ = ψ₃: emit ext_16_12.
      right; right; right; right; right; left
      have act_conj : (e'.symm.trans τ_H).trans e' = ext_16_12.act := by
        rw [h_conj_eq, hσ]
      refine ⟨RealiseExtType.transfer_along_extEquiv R_H realise_16_12
        { hn := rfl
          φ := e'
          act_conj := act_conj.symm
          act_glue := hv.symm }⟩
    · -- v = (ofAdd 2, 1), ψ = ψ₅: emit ext_16_4.
      right; right; left
      have act_conj : (e'.symm.trans τ_H).trans e' = ext_16_4.act := by
        rw [h_conj_eq, hσ]
      refine ⟨RealiseExtType.transfer_along_extEquiv R_H realise_16_4
        { hn := rfl
          φ := e'
          act_conj := act_conj.symm
          act_glue := hv.symm }⟩
    · -- v = (ofAdd 2, 1), ψ = ψ₆: rule out via h_contra_helper.
      exfalso
      set x : H := e'.symm ((1, Multiplicative.ofAdd 1) :
        CyclicGroup 4 × CyclicGroup 2) with hx_def
      have hex : e' x = (1, Multiplicative.ofAdd 1) := e'.apply_symm_apply _
      have h_eq_one :
          (e' ((τ_H x) * ⟨a ^ 2, ha_sq⟩ * x) : CyclicGroup 4 × CyclicGroup 2) = 1 := by
        rw [map_mul, map_mul, ← hv_K'_def, hv, hτH_eq' x, hex, h_conj_eq, hσ]
        decide
      have := h_contra_helper x h_eq_one
      omega
    -- v = (1, ofAdd 1) cases
    · -- v = (1, ofAdd 1), ψ = 1: emit ext_16_2.
      left
      have act_conj : (e'.symm.trans τ_H).trans e' = ext_16_2.act := by
        rw [h_conj_eq, hσ]
      refine ⟨RealiseExtType.transfer_along_extEquiv R_H realise_16_2
        { hn := rfl
          φ := e'
          act_conj := act_conj.symm
          act_glue := hv.symm }⟩
    · -- v = (1, ofAdd 1), ψ = ψ₃: K_8-subgroup switch.
      right; right; left
      -- H is abelian (via e').
      have h_H_comm : ∀ y z : H, (y : G) * (z : G) = (z : G) * (y : G) := by
        intro y z
        have hyz : (y * z : H) = (z * y : H) := by
          apply e'.injective
          rw [map_mul, map_mul, mul_comm]
        exact congrArg Subtype.val hyz
      -- Generators c_H and V_H of H.
      set c_H : H := e'.symm ((Multiplicative.ofAdd 1, 1) :
        CyclicGroup 4 × CyclicGroup 2) with hc_H_def
      have hec_H : e' c_H = (Multiplicative.ofAdd 1, 1) := e'.apply_symm_apply _
      set V_H : H := e'.symm ((Multiplicative.ofAdd 2, 1) :
        CyclicGroup 4 × CyclicGroup 2) with hV_H_def
      have heV_H : e' V_H = (Multiplicative.ofAdd 2, 1) := e'.apply_symm_apply _
      -- c_H ^ 2 = V_H, c_H ^ 4 = 1, V_H ^ 2 = 1 in H.
      have hc_sq_VH : c_H ^ 2 = V_H := by
        apply e'.injective; rw [map_pow, hec_H, heV_H]; decide
      have hcH4 : c_H ^ 4 = 1 := by
        have h : e' (c_H ^ 4) = 1 := by
          rw [map_pow, hec_H]; decide
        exact e'.injective (h.trans (map_one e').symm)
      have hVH_sq : V_H ^ 2 = 1 := by
        have h : e' (V_H ^ 2) = 1 := by
          rw [map_pow, heV_H]; decide
        exact e'.injective (h.trans (map_one e').symm)
      -- Same in G:
      have hcG4 : ((c_H : G)) ^ 4 = 1 := by
        have h := congrArg (fun x : H => (x : G)) hcH4
        simpa using h
      have hVG_sq : ((V_H : G)) ^ 2 = 1 := by
        have h := congrArg (fun x : H => (x : G)) hVH_sq
        simpa using h
      have hcG_sq : ((c_H : G)) ^ 2 = (V_H : G) := by
        have h := congrArg (fun x : H => (x : G)) hc_sq_VH
        simpa using h
      -- a * c_H * a⁻¹ = c_H⁻¹ (psi3 sends (ofAdd 1, 1) ↦ (ofAdd 3, 1)).
      have hτcH : τ_H c_H = c_H⁻¹ := by
        apply e'.injective
        rw [hτH_eq' c_H, h_conj_eq, hσ, hec_H, map_inv, hec_H]
        decide
      have hconj_c : a * (c_H : G) * a⁻¹ = ((c_H : G))⁻¹ := by
        have h := hconj_H c_H
        have h2 : ((τ_H c_H : H) : G) = (((c_H⁻¹ : H) : G)) := congrArg _ hτcH
        rw [← h, h2]
        push_cast
        simp
      -- a * V_H * a⁻¹ = V_H (psi3 fixes (ofAdd 2, 1)).
      have hτVH : τ_H V_H = V_H := by
        apply e'.injective
        rw [hτH_eq' V_H, h_conj_eq, hσ, heV_H]
        decide
      have hconj_V : a * (V_H : G) * a⁻¹ = (V_H : G) := by
        have h := hconj_H V_H
        have h2 : ((τ_H V_H : H) : G) = ((V_H : H) : G) := congrArg _ hτVH
        rw [← h, h2]
      -- a * V_H = V_H * a.
      have ha_V_comm : a * (V_H : G) = (V_H : G) * a := by
        have : a * (V_H : G) * a⁻¹ * a = (V_H : G) * a := by rw [hconj_V]
        rwa [mul_assoc, inv_mul_cancel, mul_one] at this
      -- a * c_H = c_H⁻¹ * a (rearrange hconj_c).
      have hac : a * (c_H : G) = ((c_H : G))⁻¹ * a := by
        have : a * (c_H : G) * a⁻¹ * a = ((c_H : G))⁻¹ * a := by rw [hconj_c]
        rwa [mul_assoc, inv_mul_cancel, mul_one] at this
      -- a^2 commutes with c_H in G (a^2 ∈ H, c_H ∈ H, H abelian).
      have ha2_cH_comm : a ^ 2 * (c_H : G) = (c_H : G) * a ^ 2 := by
        have hh := h_H_comm (⟨a^2, ha_sq⟩ : H) c_H
        exact hh
      -- c_H and V_H commute in G.
      have hcV_comm : (c_H : G) * (V_H : G) = (V_H : G) * (c_H : G) := h_H_comm c_H V_H
      -- c_H⁻¹ = c_H^3.
      have hc_inv_pow3 : ((c_H : G))⁻¹ = ((c_H : G)) ^ 3 := by
        have h : (c_H : G) ^ 4 = 1 := hcG4
        have h2 : (c_H : G) * (c_H : G) ^ 3 = 1 := by
          calc (c_H : G) * (c_H : G) ^ 3
              = (c_H : G) ^ 1 * (c_H : G) ^ 3 := by rw [pow_one]
            _ = (c_H : G) ^ (1 + 3) := by rw [← pow_add]
            _ = (c_H : G) ^ 4 := by norm_num
            _ = 1 := h
        exact (eq_inv_of_mul_eq_one_left (by
          calc (c_H : G) ^ 3 * (c_H : G)
              = (c_H : G) ^ 3 * (c_H : G) ^ 1 := by rw [pow_one]
            _ = (c_H : G) ^ (3 + 1) := by rw [← pow_add]
            _ = (c_H : G) ^ 4 := by norm_num
            _ = 1 := h)).symm
      have hc_pow3_eq : ((c_H : G)) ^ 3 = (V_H : G) * (c_H : G) := by
        have : (c_H : G) ^ 3 = (c_H : G) ^ 2 * (c_H : G) := by
          rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one]
        rw [this, hcG_sq]
      -- Define U = a * c_H (using let so we don't auto-substitute).
      let U : G := a * (c_H : G)
      have hU_def : U = a * (c_H : G) := rfl
      -- U^2 = a^2: U*U = ac·ac = (c⁻¹a)(ac) = c⁻¹·a²·c, then a² commutes with c.
      have hU_sq_a_sq : U ^ 2 = a ^ 2 := by
        have step1 : U * U = ((c_H : G))⁻¹ * a * (a * (c_H : G)) := by
          change (a * (c_H : G)) * (a * (c_H : G)) = ((c_H : G))⁻¹ * a * (a * (c_H : G))
          rw [hac]
        have step2 : ((c_H : G))⁻¹ * a * (a * (c_H : G)) = ((c_H : G))⁻¹ * (a * a * (c_H : G)) := by
          rw [mul_assoc, mul_assoc, ← mul_assoc a a]
        have step3 : a * a = a ^ 2 := by rw [sq]
        have step4 : ((c_H : G))⁻¹ * (a ^ 2 * (c_H : G)) = ((c_H : G))⁻¹ * ((c_H : G) * a ^ 2) := by
          rw [ha2_cH_comm]
        have step5 : ((c_H : G))⁻¹ * ((c_H : G) * a ^ 2) = a ^ 2 := by
          rw [← mul_assoc, inv_mul_cancel, one_mul]
        calc U ^ 2 = U * U := by rw [sq]
          _ = ((c_H : G))⁻¹ * a * (a * (c_H : G)) := step1
          _ = ((c_H : G))⁻¹ * (a * a * (c_H : G)) := step2
          _ = ((c_H : G))⁻¹ * (a ^ 2 * (c_H : G)) := by rw [step3]
          _ = ((c_H : G))⁻¹ * ((c_H : G) * a ^ 2) := step4
          _ = a ^ 2 := step5
      -- U^4 = 1.
      have hU4 : U ^ 4 = 1 := by
        have h1 : U ^ 4 = (U ^ 2) ^ 2 := by
          rw [← pow_mul]
        rw [h1, hU_sq_a_sq]
        have h2 : (a ^ 2) ^ 2 = a ^ 4 := by
          rw [← pow_mul]
        rw [h2, h_a4]
      -- U * V_H = V_H * U.
      have hUV_comm : U * (V_H : G) = (V_H : G) * U := by
        change a * (c_H : G) * (V_H : G) = (V_H : G) * (a * (c_H : G))
        have h1 : a * (c_H : G) * (V_H : G) = a * ((c_H : G) * (V_H : G)) := mul_assoc _ _ _
        have h2 : a * ((c_H : G) * (V_H : G)) = a * ((V_H : G) * (c_H : G)) := by rw [hcV_comm]
        have h3 : a * ((V_H : G) * (c_H : G)) = (a * (V_H : G)) * (c_H : G) :=
          (mul_assoc _ _ _).symm
        have h4 : (a * (V_H : G)) * (c_H : G) = ((V_H : G) * a) * (c_H : G) := by rw [ha_V_comm]
        have h5 : ((V_H : G) * a) * (c_H : G) = (V_H : G) * (a * (c_H : G)) := mul_assoc _ _ _
        rw [h1, h2, h3, h4, h5]
      -- a * U * a⁻¹ = U * V_H.
      have hconj_U : a * U * a⁻¹ = U * (V_H : G) := by
        change a * (a * (c_H : G)) * a⁻¹ = (a * (c_H : G)) * (V_H : G)
        have step1 : a * (a * (c_H : G)) * a⁻¹ = a * ((c_H : G))⁻¹ := by
          have rearr : a * (a * (c_H : G)) * a⁻¹ = a * (a * (c_H : G) * a⁻¹) := by
            rw [mul_assoc, mul_assoc]
          rw [rearr, hconj_c]
        have step2 : a * ((c_H : G))⁻¹ = a * (c_H : G) * (V_H : G) := by
          rw [hc_inv_pow3, hc_pow3_eq]
          rw [← hcV_comm, ← mul_assoc]
        rw [step1, step2]
      -- Use cyclicHom for each factor and combine via noncommCoprod.
      let ιU : CyclicGroup 4 →* G := cyclicHom 4 U hU4
      let ιV : CyclicGroup 2 →* G := cyclicHom 2 (V_H : G) hVG_sq
      have hUV : Commute U (V_H : G) := hUV_comm
      have hιU_mem : ∀ x : CyclicGroup 4, ∃ k : ℤ, ιU x = U ^ k := by
        intro x
        refine ⟨(Multiplicative.toAdd x).cast, ?_⟩
        change cyclicHom 4 U hU4 x = U ^ ((Multiplicative.toAdd x).cast : ℤ)
        unfold cyclicHom
        rfl
      have hιV_mem : ∀ y : CyclicGroup 2, ∃ l : ℤ, ιV y = (V_H : G) ^ l := by
        intro y
        refine ⟨(Multiplicative.toAdd y).cast, ?_⟩
        change cyclicHom 2 (V_H : G) hVG_sq y = (V_H : G) ^ ((Multiplicative.toAdd y).cast : ℤ)
        unfold cyclicHom
        rfl
      have hιUV_comm : ∀ (x : CyclicGroup 4) (y : CyclicGroup 2), Commute (ιU x) (ιV y) := by
        intro x y
        obtain ⟨k, hk⟩ := hιU_mem x
        obtain ⟨l, hl⟩ := hιV_mem y
        rw [hk, hl]
        exact hUV.zpow_zpow k l
      -- Now combine ιU and ιV to get ι.
      let ι : CyclicGroup 4 × CyclicGroup 2 →* G :=
        MonoidHom.noncommCoprod ιU ιV (fun x y => (hιUV_comm x y).eq)
      have hι_apply : ∀ m n, ι (m, n) = ιU m * ιV n := by
        intro m n; rfl
      have hιU_pow : ∀ k : ZMod 4, ιU (Multiplicative.ofAdd k) = U ^ (k.cast : ℤ) := by
        intro k; rfl
      have hιV_pow : ∀ k : ZMod 2, ιV (Multiplicative.ofAdd k) = (V_H : G) ^ (k.cast : ℤ) := by
        intro k; rfl
      have hιU_gen : ιU (Multiplicative.ofAdd (1 : ZMod 4)) = U := by
        rw [hιU_pow]
        have h : ((1 : ZMod 4).cast : ℤ) = 1 := by decide
        rw [h]
        exact zpow_one U
      have hιU_ofAdd2 : ιU (Multiplicative.ofAdd (2 : ZMod 4)) = a ^ 2 := by
        rw [hιU_pow]
        have h : ((2 : ZMod 4).cast : ℤ) = 2 := by decide
        rw [h]
        change U ^ (2 : ℤ) = a ^ 2
        rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hU_sq_a_sq]
      have hιV_gen : ιV (Multiplicative.ofAdd (1 : ZMod 2)) = (V_H : G) := by
        rw [hιV_pow]
        have h : ((1 : ZMod 2).cast : ℤ) = 1 := by decide
        rw [h]
        exact zpow_one _
      let conjA : G →* G :=
        { toFun := fun g => a * g * a⁻¹
          map_one' := by simp
          map_mul' := by intro x y; group }
      have hconjA_apply : ∀ g : G, conjA g = a * g * a⁻¹ := fun _ => rfl
      have hconjA_U : conjA U = U * (V_H : G) := hconj_U
      have hconjA_V : conjA (V_H : G) = (V_H : G) := hconj_V
      have hconjA_zpow : ∀ (g : G) (k : ℤ), conjA (g ^ k) = (conjA g) ^ k := fun g k =>
        map_zpow conjA g k
      have hUV_mul_zpow : ∀ k : ℤ, (U * (V_H : G)) ^ k = U ^ k * (V_H : G) ^ k :=
        fun k => Commute.mul_zpow hUV k
      have h_act : ∀ x : CyclicGroup 4 × CyclicGroup 2, a * ι x * a⁻¹ = ι (psi5 x) := by
        rintro ⟨m, n⟩
        obtain ⟨m', rfl⟩ : ∃ m', Multiplicative.ofAdd m' = m :=
          ⟨Multiplicative.toAdd m, rfl⟩
        obtain ⟨n', rfl⟩ : ∃ n', Multiplicative.ofAdd n' = n :=
          ⟨Multiplicative.toAdd n, rfl⟩
        change conjA (ι (Multiplicative.ofAdd m', Multiplicative.ofAdd n')) =
             ι (psi5 (Multiplicative.ofAdd m', Multiplicative.ofAdd n'))
        have lhs_eq : conjA (ι (Multiplicative.ofAdd m', Multiplicative.ofAdd n')) =
            U ^ (m'.cast : ℤ) * (V_H : G) ^ ((m'.cast : ℤ) + (n'.cast : ℤ)) := by
          rw [hι_apply, hιU_pow, hιV_pow]
          rw [map_mul conjA, map_zpow conjA, map_zpow conjA]
          rw [hconjA_U, hconjA_V]
          rw [hUV_mul_zpow, mul_assoc, ← zpow_add]
        have rhs_eq : ι (psi5 (Multiplicative.ofAdd m', Multiplicative.ofAdd n')) =
            U ^ (m'.cast : ℤ) * (V_H : G) ^ ((n' + (m'.val : ZMod 2)).cast : ℤ) := by
          change ι (Multiplicative.ofAdd m',
                 Multiplicative.ofAdd (n' + (m'.val : ZMod 2))) = _
          rw [hι_apply, hιU_pow, hιV_pow]
        rw [lhs_eq, rhs_eq]
        congr 1
        have hV2 : (V_H : G) ^ (2 : ℤ) = 1 := by
          rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hVG_sq]
        have hV3 : (V_H : G) ^ (3 : ℤ) = (V_H : G) := by
          rw [show (3 : ℤ) = 2 + 1 from rfl, zpow_add, hV2, one_mul, zpow_one]
        have hV4 : (V_H : G) ^ (4 : ℤ) = 1 := by
          rw [show (4 : ℤ) = 2 + 2 from rfl, zpow_add, hV2, mul_one]
        fin_cases m' <;> fin_cases n' <;>
          first
            | rfl
            | (change (V_H : G) ^ (2 : ℤ) = (V_H : G) ^ (0 : ℤ); rw [hV2, zpow_zero])
            | (change (V_H : G) ^ (3 : ℤ) = (V_H : G) ^ (1 : ℤ); rw [hV3, zpow_one])
            | (change (V_H : G) ^ (4 : ℤ) = (V_H : G) ^ (0 : ℤ); rw [hV4, zpow_zero])
      have hU_ne_one : U ≠ 1 := by
        intro hU1
        have ha_eq : a = ((c_H : G))⁻¹ := by
          have : a * (c_H : G) = 1 := hU1
          exact eq_inv_of_mul_eq_one_left this
        exact ha_notMem (ha_eq ▸ H.inv_mem c_H.2)
      have hU2_ne_one : U ^ 2 ≠ 1 := by rw [hU_sq_a_sq]; exact ha2_ne_one
      have hV_ne_one : (V_H : G) ≠ 1 := by
        intro h
        have hV_eq_one : V_H = 1 := Subtype.ext h
        have hev : e' V_H = (Multiplicative.ofAdd (2 : ZMod 4), 1) := heV_H
        rw [hV_eq_one, map_one] at hev
        have h1 : (1 : CyclicGroup 4) = Multiplicative.ofAdd (2 : ZMod 4) := (Prod.mk.inj hev).1
        revert h1; decide
      have hV_ne_a2 : (V_H : G) ≠ a ^ 2 := by
        intro h
        have hV_eq_a2 : V_H = ⟨a ^ 2, ha_sq⟩ := Subtype.ext h
        have hev : e' V_H = (Multiplicative.ofAdd (2 : ZMod 4), 1) := heV_H
        rw [hV_eq_a2, ← hv_K'_def, hv] at hev
        have h1 : Multiplicative.ofAdd (2 : ZMod 4) = (1 : CyclicGroup 4) :=
          (Prod.mk.inj hev.symm).1
        revert h1; decide
      have hιU_inj : Function.Injective ιU := by
        rw [injective_iff_map_eq_one]
        intro x hx
        obtain ⟨k, rfl⟩ : ∃ k, Multiplicative.ofAdd k = x := ⟨Multiplicative.toAdd x, rfl⟩
        rw [hιU_pow] at hx
        fin_cases k
        · rfl
        · exfalso
          change U ^ ((1 : ZMod 4).cast : ℤ) = 1 at hx
          rw [show ((1 : ZMod 4).cast : ℤ) = 1 from rfl, zpow_one] at hx
          exact hU_ne_one hx
        · exfalso
          change U ^ ((2 : ZMod 4).cast : ℤ) = 1 at hx
          rw [show ((2 : ZMod 4).cast : ℤ) = 2 from rfl,
              show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast] at hx
          exact hU2_ne_one hx
        · exfalso
          change U ^ ((3 : ZMod 4).cast : ℤ) = 1 at hx
          rw [show ((3 : ZMod 4).cast : ℤ) = 3 from rfl,
              show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast] at hx
          have hU1 : U = 1 := by
            calc U = U ^ 4 * (U ^ 3)⁻¹ := by group
              _ = 1 * 1⁻¹ := by rw [hU4, hx]
              _ = 1 := by group
          exact hU_ne_one hU1
      have hιV_inj : Function.Injective ιV := by
        rw [injective_iff_map_eq_one]
        intro x hx
        obtain ⟨k, rfl⟩ : ∃ k, Multiplicative.ofAdd k = x := ⟨Multiplicative.toAdd x, rfl⟩
        rw [hιV_pow] at hx
        fin_cases k
        · rfl
        · exfalso
          change (V_H : G) ^ ((1 : ZMod 2).cast : ℤ) = 1 at hx
          rw [show ((1 : ZMod 2).cast : ℤ) = 1 from rfl, zpow_one] at hx
          exact hV_ne_one hx
      have h_disjoint : Disjoint ιU.range ιV.range := by
        rw [Subgroup.disjoint_def]
        intro g hgU hgV
        obtain ⟨x, hxg⟩ := hgV
        obtain ⟨l, rfl⟩ : ∃ l, Multiplicative.ofAdd l = x := ⟨Multiplicative.toAdd x, rfl⟩
        rw [hιV_pow] at hxg
        fin_cases l
        · change (V_H : G) ^ ((0 : ZMod 2).cast : ℤ) = g at hxg
          rw [show ((0 : ZMod 2).cast : ℤ) = 0 from rfl, zpow_zero] at hxg
          exact hxg.symm
        · exfalso
          change (V_H : G) ^ ((1 : ZMod 2).cast : ℤ) = g at hxg
          rw [show ((1 : ZMod 2).cast : ℤ) = 1 from rfl, zpow_one] at hxg
          rw [← hxg] at hgU
          obtain ⟨y, hyV⟩ := hgU
          obtain ⟨k, rfl⟩ : ∃ k, Multiplicative.ofAdd k = y := ⟨Multiplicative.toAdd y, rfl⟩
          rw [hιU_pow] at hyV
          fin_cases k
          · change U ^ ((0 : ZMod 4).cast : ℤ) = (V_H : G) at hyV
            rw [show ((0 : ZMod 4).cast : ℤ) = 0 from rfl, zpow_zero] at hyV
            exact hV_ne_one hyV.symm
          · change U ^ ((1 : ZMod 4).cast : ℤ) = (V_H : G) at hyV
            rw [show ((1 : ZMod 4).cast : ℤ) = 1 from rfl, zpow_one] at hyV
            exact ha_notMem (by
              have : a = U * ((c_H : G))⁻¹ := by rw [hU_def]; group
              rw [this, hyV]
              exact H.mul_mem V_H.2 (H.inv_mem c_H.2))
          · change U ^ ((2 : ZMod 4).cast : ℤ) = (V_H : G) at hyV
            rw [show ((2 : ZMod 4).cast : ℤ) = 2 from rfl,
                show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hU_sq_a_sq] at hyV
            exact hV_ne_a2 hyV.symm
          · change U ^ ((3 : ZMod 4).cast : ℤ) = (V_H : G) at hyV
            rw [show ((3 : ZMod 4).cast : ℤ) = 3 from rfl,
                show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast] at hyV
            have hU3_in_H : U ^ 3 ∈ H := hyV ▸ V_H.2
            have hU3_eq : U ^ 3 = a ^ 2 * U := by
              rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one, hU_sq_a_sq]
            rw [hU3_eq] at hU3_in_H
            have hU_in_H : U ∈ H := by
              have : U = (a ^ 2)⁻¹ * (a ^ 2 * U) := by group
              rw [this]
              exact H.mul_mem (H.inv_mem ha_sq) hU3_in_H
            apply ha_notMem
            have : a = U * ((c_H : G))⁻¹ := by rw [hU_def]; group
            rw [this]
            exact H.mul_mem hU_in_H (H.inv_mem c_H.2)
      have hι_inj : Function.Injective ι := by
        rw [MonoidHom.noncommCoprod_injective]
        exact ⟨hιU_inj, hιV_inj, h_disjoint⟩
      have ha_notMem_ιrange : ∀ x : CyclicGroup 4 × CyclicGroup 2, ι x ≠ a := by
        intro x hxa
        obtain ⟨m, n⟩ := x
        obtain ⟨m', rfl⟩ : ∃ m', Multiplicative.ofAdd m' = m :=
          ⟨Multiplicative.toAdd m, rfl⟩
        obtain ⟨n', rfl⟩ : ∃ n', Multiplicative.ofAdd n' = n :=
          ⟨Multiplicative.toAdd n, rfl⟩
        rw [hι_apply, hιU_pow, hιV_pow] at hxa
        fin_cases m' <;> fin_cases n' <;>
        ( first
          | (change U ^ ((0 : ZMod 4).cast : ℤ) * (V_H : G) ^ ((0 : ZMod 2).cast : ℤ) = a at hxa
             rw [show ((0 : ZMod 4).cast : ℤ) = 0 from rfl,
                 show ((0 : ZMod 2).cast : ℤ) = 0 from rfl, zpow_zero, zpow_zero, mul_one] at hxa
             exact h_a_ne_one hxa.symm)
          | (change U ^ ((0 : ZMod 4).cast : ℤ) * (V_H : G) ^ ((1 : ZMod 2).cast : ℤ) = a at hxa
             rw [show ((0 : ZMod 4).cast : ℤ) = 0 from rfl,
                 show ((1 : ZMod 2).cast : ℤ) = 1 from rfl, zpow_zero, zpow_one, one_mul] at hxa
             exact ha_notMem (hxa ▸ V_H.2))
          | (change U ^ ((1 : ZMod 4).cast : ℤ) * (V_H : G) ^ ((0 : ZMod 2).cast : ℤ) = a at hxa
             rw [show ((1 : ZMod 4).cast : ℤ) = 1 from rfl,
                 show ((0 : ZMod 2).cast : ℤ) = 0 from rfl, zpow_one, zpow_zero, mul_one] at hxa
             have hc1 : (c_H : G) = 1 := by
               have h1 : a * (c_H : G) = a := hxa
               exact mul_left_cancel (by rw [mul_one]; exact h1)
             have hc_H_one : c_H = 1 := Subtype.ext hc1
             have he_c : e' c_H = (Multiplicative.ofAdd 1, 1) := hec_H
             rw [hc_H_one, map_one] at he_c
             have h1 : (1 : CyclicGroup 4) = Multiplicative.ofAdd (1 : ZMod 4) :=
               (Prod.mk.inj he_c).1
             revert h1; decide)
          | (change U ^ ((1 : ZMod 4).cast : ℤ) * (V_H : G) ^ ((1 : ZMod 2).cast : ℤ) = a at hxa
             rw [show ((1 : ZMod 4).cast : ℤ) = 1 from rfl,
                 show ((1 : ZMod 2).cast : ℤ) = 1 from rfl, zpow_one, zpow_one] at hxa
             have hUV : U * (V_H : G) = a := hxa
             have hV_inv : (V_H : G)⁻¹ = (V_H : G) := by
               rw [inv_eq_iff_mul_eq_one]; rw [← sq]; exact hVG_sq
             have hU_eq : U = a * (V_H : G) := by
               calc U = U * (V_H : G) * (V_H : G)⁻¹ := by rw [mul_inv_cancel_right]
                 _ = a * (V_H : G)⁻¹ := by rw [hUV]
                 _ = a * (V_H : G) := by rw [hV_inv]
             have hc_eq : (c_H : G) = (V_H : G) := by
               rw [hU_def] at hU_eq
               exact mul_left_cancel hU_eq
             have hc_H_eq_VH : c_H = V_H := Subtype.ext hc_eq
             have he_c : e' c_H = (Multiplicative.ofAdd 1, 1) := hec_H
             rw [hc_H_eq_VH, heV_H] at he_c
             have h1 : Multiplicative.ofAdd (2 : ZMod 4) = Multiplicative.ofAdd (1 : ZMod 4) :=
               (Prod.mk.inj he_c).1
             revert h1; decide)
          | (change U ^ ((2 : ZMod 4).cast : ℤ) * (V_H : G) ^ ((0 : ZMod 2).cast : ℤ) = a at hxa
             rw [show ((2 : ZMod 4).cast : ℤ) = 2 from rfl,
                 show ((0 : ZMod 2).cast : ℤ) = 0 from rfl, zpow_zero, mul_one,
                 show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hU_sq_a_sq] at hxa
             have : a = 1 := by
               have h1 : a * a = a := by rw [← sq]; exact hxa
               exact mul_left_cancel (a := a) (by rw [mul_one]; exact h1)
             exact h_a_ne_one this)
          | (change U ^ ((2 : ZMod 4).cast : ℤ) * (V_H : G) ^ ((1 : ZMod 2).cast : ℤ) = a at hxa
             rw [show ((2 : ZMod 4).cast : ℤ) = 2 from rfl,
                 show ((1 : ZMod 2).cast : ℤ) = 1 from rfl,
                 show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, zpow_one, hU_sq_a_sq] at hxa
             have hV_eq : (V_H : G) = a⁻¹ := by
               have ha2V_eq : a ^ 2 * (V_H : G) = a := hxa
               have : (V_H : G) = (a ^ 2)⁻¹ * a := by
                 have h2 : a ^ 2 * (V_H : G) = a ^ 2 * ((a ^ 2)⁻¹ * a) := by
                   rw [← mul_assoc, mul_inv_cancel, one_mul]; exact ha2V_eq
                 exact mul_left_cancel h2
               rw [this]; group
             apply ha_notMem
             have : a = (V_H : G)⁻¹ := by rw [hV_eq]; group
             rw [this]
             exact H.inv_mem V_H.2)
          | (change U ^ ((3 : ZMod 4).cast : ℤ) * (V_H : G) ^ ((0 : ZMod 2).cast : ℤ) = a at hxa
             rw [show ((3 : ZMod 4).cast : ℤ) = 3 from rfl,
                 show ((0 : ZMod 2).cast : ℤ) = 0 from rfl, zpow_zero, mul_one,
                 show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast] at hxa
             have hU3_eq : U ^ 3 = a ^ 3 * (c_H : G) := by
               have : U ^ 3 = U * U ^ 2 := by rw [show (3 : ℕ) = 1 + 2 from rfl, pow_add, pow_one]
               rw [this, hU_sq_a_sq, hU_def]
               calc a * (c_H : G) * a ^ 2 = a * ((c_H : G) * a ^ 2) := by rw [mul_assoc]
                 _ = a * (a ^ 2 * (c_H : G)) := by rw [← ha2_cH_comm]
                 _ = a * a ^ 2 * (c_H : G) := by rw [mul_assoc]
                 _ = a ^ 3 * (c_H : G) := by rw [show (3 : ℕ) = 1 + 2 from rfl, pow_add, pow_one]
             rw [hU3_eq] at hxa
             have hcH_eq_a2 : (c_H : G) = a ^ 2 := by
               have h1 : a ^ 3 * (c_H : G) = a := hxa
               have h2 : (c_H : G) = (a ^ 3)⁻¹ * a := by
                 have : a ^ 3 * (c_H : G) = a ^ 3 * ((a ^ 3)⁻¹ * a) := by
                   rw [← mul_assoc, mul_inv_cancel, one_mul]; exact h1
                 exact mul_left_cancel this
               rw [h2]
               have : (a ^ 3)⁻¹ * a = a ^ 2 := by
                 have ha3a : a ^ 3 * a = a ^ 4 := by
                   rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, pow_one]
                 have : a ^ 3 * (a ^ 3 * a) = a ^ 3 * a ^ 4 := by rw [ha3a]
                 calc (a ^ 3)⁻¹ * a = (a ^ 3)⁻¹ * (a * 1) := by rw [mul_one]
                   _ = (a ^ 3)⁻¹ * (a * a ^ 4) := by rw [h_a4]
                   _ = (a ^ 3)⁻¹ * (a * a ^ 4) := rfl
                   _ = (a ^ 3)⁻¹ * (a ^ 5) := by
                       rw [show (5 : ℕ) = 1 + 4 from rfl, pow_add, pow_one]
                   _ = (a ^ 3)⁻¹ * (a ^ 3 * a ^ 2) := by
                       rw [show (5 : ℕ) = 3 + 2 from rfl, pow_add]
                   _ = (a ^ 3)⁻¹ * a ^ 3 * a ^ 2 := by rw [mul_assoc]
                   _ = a ^ 2 := by rw [inv_mul_cancel, one_mul]
               exact this
             have hc_H_eq : c_H = ⟨a ^ 2, ha_sq⟩ := Subtype.ext hcH_eq_a2
             have he_c : e' c_H = (Multiplicative.ofAdd 1, 1) := hec_H
             rw [hc_H_eq, ← hv_K'_def, hv] at he_c
             have h1' : (1 : CyclicGroup 4) = Multiplicative.ofAdd (1 : ZMod 4) :=
               (Prod.mk.inj he_c).1
             revert h1'; decide)
          | (change U ^ ((3 : ZMod 4).cast : ℤ) * (V_H : G) ^ ((1 : ZMod 2).cast : ℤ) = a at hxa
             rw [show ((3 : ZMod 4).cast : ℤ) = 3 from rfl,
                 show ((1 : ZMod 2).cast : ℤ) = 1 from rfl,
                 show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, zpow_one] at hxa
             have hU3_eq : U ^ 3 = a ^ 3 * (c_H : G) := by
               have : U ^ 3 = U * U ^ 2 := by rw [show (3 : ℕ) = 1 + 2 from rfl, pow_add, pow_one]
               rw [this, hU_sq_a_sq, hU_def]
               calc a * (c_H : G) * a ^ 2 = a * ((c_H : G) * a ^ 2) := by rw [mul_assoc]
                 _ = a * (a ^ 2 * (c_H : G)) := by rw [← ha2_cH_comm]
                 _ = a * a ^ 2 * (c_H : G) := by rw [mul_assoc]
                 _ = a ^ 3 * (c_H : G) := by rw [show (3 : ℕ) = 1 + 2 from rfl, pow_add, pow_one]
             rw [hU3_eq] at hxa
             have hcV_eq : (c_H : G) * (V_H : G) = a ^ 2 := by
               have h1 : (a ^ 3)⁻¹ * (a ^ 3 * (c_H : G) * (V_H : G)) = (a ^ 3)⁻¹ * a := by
                 rw [hxa]
               rw [← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul] at h1
               rw [h1]
               calc (a ^ 3)⁻¹ * a = (a ^ 3)⁻¹ * (a * 1) := by rw [mul_one]
                 _ = (a ^ 3)⁻¹ * (a * a ^ 4) := by rw [h_a4]
                 _ = (a ^ 3)⁻¹ * (a ^ 5) := by
                     rw [show (5 : ℕ) = 1 + 4 from rfl, pow_add, pow_one]
                 _ = (a ^ 3)⁻¹ * (a ^ 3 * a ^ 2) := by
                     rw [show (5 : ℕ) = 3 + 2 from rfl, pow_add]
                 _ = (a ^ 3)⁻¹ * a ^ 3 * a ^ 2 := by rw [mul_assoc]
                 _ = a ^ 2 := by rw [inv_mul_cancel, one_mul]
             have hcVH_eq : c_H * V_H = ⟨a ^ 2, ha_sq⟩ := by
               apply Subtype.ext
               change (c_H : G) * (V_H : G) = a ^ 2
               exact hcV_eq
             have he_cV : e' (c_H * V_H) = e' (⟨a ^ 2, ha_sq⟩ : H) := by rw [hcVH_eq]
             rw [map_mul, hec_H, heV_H, ← hv_K'_def, hv] at he_cV
             have h1' :
                 (Multiplicative.ofAdd (1 : ZMod 4) * Multiplicative.ofAdd (2 : ZMod 4) :
                   CyclicGroup 4) = (1 : CyclicGroup 4) := (Prod.mk.inj he_cV).1
             revert h1'; decide))
      let f : (CyclicGroup 4 × CyclicGroup 2) × Fin 2 → G :=
        fun p => ι p.1 * a ^ (p.2 : ℕ)
      have hf_inj : Function.Injective f := by
        intro ⟨k₁, j₁⟩ ⟨k₂, j₂⟩ hfeq
        simp only [f] at hfeq
        by_cases hj : j₁ = j₂
        · subst hj
          have : ι k₁ = ι k₂ := mul_right_cancel hfeq
          have : k₁ = k₂ := hι_inj this
          rw [this]
        · exfalso
          have h01 : (j₁ = 0 ∧ j₂ = 1) ∨ (j₁ = 1 ∧ j₂ = 0) := by
            fin_cases j₁ <;> fin_cases j₂
            · exact absurd rfl hj
            · left; exact ⟨rfl, rfl⟩
            · right; exact ⟨rfl, rfl⟩
            · exact absurd rfl hj
          rcases h01 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · subst h1; subst h2
            simp only [Fin.val_zero, Fin.val_one, pow_zero, mul_one, pow_one] at hfeq
            have ha_eq : a = ι (k₂⁻¹ * k₁) := by
              rw [map_mul, map_inv]
              have : (ι k₂)⁻¹ * ι k₁ = (ι k₂)⁻¹ * (ι k₂ * a) := by rw [← hfeq]
              rw [this, ← mul_assoc, inv_mul_cancel, one_mul]
            exact ha_notMem_ιrange _ ha_eq.symm
          · subst h1; subst h2
            simp only [Fin.val_zero, Fin.val_one, pow_zero, mul_one, pow_one] at hfeq
            have ha_eq : a = ι (k₁⁻¹ * k₂) := by
              rw [map_mul, map_inv]
              have : (ι k₁)⁻¹ * (ι k₁ * a) = (ι k₁)⁻¹ * ι k₂ := by rw [hfeq]
              rw [← mul_assoc, inv_mul_cancel, one_mul] at this
              exact this
            exact ha_notMem_ιrange _ ha_eq.symm
      haveI hfinG : Fintype G := Fintype.ofFinite G
      have hcard_eq : Nat.card G = Nat.card ((CyclicGroup 4 × CyclicGroup 2) × Fin 2) := by
        rw [hn, Nat.card_prod, Nat.card_prod, card_cyclicGroup, card_cyclicGroup,
            Nat.card_eq_fintype_card, Fintype.card_fin]
      have hf_bij : Function.Bijective f := hf_inj.bijective_of_nat_card_le hcard_eq.le
      refine ⟨{
        a := a
        ι := ι
        act_a := h_act
        pow_a_n := by
          change a ^ 2 = ι (Multiplicative.ofAdd (2 : ZMod 4), 1)
          rw [hι_apply, hιU_ofAdd2]
          have : ιV (1 : CyclicGroup 2) = 1 := map_one ιV
          rw [this, mul_one]
        equiv := Equiv.ofBijective f hf_bij
        equiv_apply := fun _ _ => rfl
      }⟩
    · -- v = (1, ofAdd 1), ψ = ψ₅: slide via `a' = a · z_H` where `z_H = e'.symm (ofAdd 1, 1)`.
      -- The shift sends glue v_b = (1, ofAdd 1) → v_a = (ofAdd 2, 1) and preserves
      -- τ_H (since H is abelian via the iso to K_8 = C_4 × C_2). Emits ext_16_4.
      right; right; left
      -- H is abelian (via the iso `e' : H ≃* CyclicGroup 4 × CyclicGroup 2`).
      have h_H_comm : ∀ y z : H, (y : G) * (z : G) = (z : G) * (y : G) := by
        intro y z
        have hyz : (y * z : H) = (z * y : H) := by
          apply e'.injective
          rw [map_mul, map_mul, mul_comm]
        exact congrArg Subtype.val hyz
      -- Set up the shift element.
      set z_K : CyclicGroup 4 × CyclicGroup 2 := (Multiplicative.ofAdd 1, 1) with hz_K_def
      set z_H : H := e'.symm z_K with hz_H_def
      have hez_H : e' z_H = z_K := e'.apply_symm_apply _
      set a' : G := a * (z_H : G) with ha'_def
      have ha'_notMem : a' ∉ H := h_b_notMem z_H
      have ha'_sq : a' ^ 2 ∈ H := h_b_sq_mem z_H
      -- Build new realisation with `a'`.
      obtain ⟨τ_H', hmap_H', hpow_H', hconj_H', R_H'⟩ :=
        realise_from_normal_index_two_with_conj H h_index a' ha'_notMem ha'_sq
      -- Show τ_H' = τ_H using abelianness of H.
      have hτ_eq : τ_H' = τ_H := by
        apply MulEquiv.ext
        intro x
        apply Subtype.ext
        have h1 := hconj_H' x
        have h2 := hconj_H x
        rw [h1, h2, ha'_def]
        have hcomm : (z_H : G) * (x : G) = (x : G) * (z_H : G) := h_H_comm z_H x
        rw [mul_inv_rev]
        calc a * (z_H : G) * (x : G) * ((z_H : G)⁻¹ * a⁻¹)
            = a * ((z_H : G) * (x : G)) * (z_H : G)⁻¹ * a⁻¹ := by group
          _ = a * ((x : G) * (z_H : G)) * (z_H : G)⁻¹ * a⁻¹ := by rw [hcomm]
          _ = a * (x : G) * a⁻¹ := by group
      -- Compute the new glue under e': it equals (ofAdd 2, 1) = ext_16_4.glue.
      have ha'_sq_in_H_eq : (⟨a' ^ 2, ha'_sq⟩ : H) = τ_H z_H * ⟨a ^ 2, ha_sq⟩ * z_H := by
        apply Subtype.ext
        exact h_b_sq_subtype z_H
      have h_new_glue : e' (⟨a' ^ 2, ha'_sq⟩ : H) = (Multiplicative.ofAdd 2, 1) := by
        rw [ha'_sq_in_H_eq, map_mul, map_mul, hτH_eq' z_H, h_conj_eq, hσ, hez_H,
            ← hv_K'_def, hv]
        decide
      -- act_conj for new realisation matches ext_16_4.act = psi5.
      have act_conj : (e'.symm.trans τ_H').trans e' = ext_16_4.act := by
        rw [hτ_eq, h_conj_eq, hσ]
      refine ⟨RealiseExtType.transfer_along_extEquiv R_H' realise_16_4
        { hn := rfl
          φ := e'
          act_conj := act_conj.symm
          act_glue := h_new_glue.symm }⟩
    · -- v = (1, ofAdd 1), ψ = ψ₆: rule out via fixed-point constraint.
      -- v must be ψ₆-fixed (via map_glue), but ψ₆(1, ofAdd 1) = (c4Half, ofAdd 1) ≠ v.
      exfalso
      have h_fix : psi6 v_K' = v_K' := by
        have h1 := hmap_H
        have h2 : e' (τ_H ⟨a ^ 2, ha_sq⟩) = e' ⟨a ^ 2, ha_sq⟩ := by
          rw [h1]
        rw [hτH_eq' ⟨a ^ 2, ha_sq⟩, h_conj_eq, hσ] at h2
        exact h2
      rw [hv] at h_fix
      revert h_fix
      decide
    -- v = (ofAdd 2, ofAdd 1) cases
    · -- v = (ofAdd 2, ofAdd 1), ψ = 1: slide via α to (1, ofAdd 1) and emit ext_16_2.
      left
      -- α : K_8 → K_8 by (a, b) ↦ (a · c4Half^{toAdd b}, b), involutive.
      let α : MulAut (CyclicGroup 4 × CyclicGroup 2) :=
        { toFun := fun ab => (ab.1 * c4Half ^ (Multiplicative.toAdd ab.2).val, ab.2)
          invFun := fun ab => (ab.1 * c4Half ^ (Multiplicative.toAdd ab.2).val, ab.2)
          left_inv := by decide
          right_inv := by decide
          map_mul' := by decide }
      set e'' : H ≃* CyclicGroup 4 × CyclicGroup 2 := e'.trans α with he''_def
      have h_conj_eq'' : (e''.symm.trans τ_H).trans e'' = α * (σ * τ_K * σ⁻¹) * α⁻¹ := by
        apply MulEquiv.ext
        intro x
        change α (e' (τ_H (e'.symm (α.symm x)))) = α ((σ * τ_K * σ⁻¹) (α⁻¹ x))
        have hcong := DFunLike.congr_fun h_conj_eq (α.symm x)
        change e' (τ_H (e'.symm (α.symm x))) = (σ * τ_K * σ⁻¹) (α.symm x) at hcong
        rw [hcong]
        rfl
      have act_conj : (e''.symm.trans τ_H).trans e'' = ext_16_2.act := by
        rw [h_conj_eq'', hσ]
        change α * 1 * α⁻¹ = (1 : MulAut (CyclicGroup 4 × CyclicGroup 2))
        rw [mul_one, mul_inv_cancel]
      have h_glue'' : e'' (⟨a ^ 2, ha_sq⟩ : H) = ext_16_2.glue := by
        change α (e' (⟨a ^ 2, ha_sq⟩ : H)) = (1, Multiplicative.ofAdd 1)
        rw [← hv_K'_def, hv]
        decide
      refine ⟨RealiseExtType.transfer_along_extEquiv R_H realise_16_2
        { hn := rfl
          φ := e''
          act_conj := act_conj.symm
          act_glue := h_glue''.symm }⟩
    · -- v = (ofAdd 2, ofAdd 1), ψ = ψ₃: structural case requiring K_8-subgroup switch.
      sorry
    · -- v = (ofAdd 2, ofAdd 1), ψ = ψ₅: rule out via h_contra_helper.
      exfalso
      set x : H := e'.symm ((Multiplicative.ofAdd 1, 1) :
        CyclicGroup 4 × CyclicGroup 2) with hx_def
      have hex : e' x = (Multiplicative.ofAdd 1, 1) := e'.apply_symm_apply _
      have h_eq_one :
          (e' ((τ_H x) * ⟨a ^ 2, ha_sq⟩ * x) : CyclicGroup 4 × CyclicGroup 2) = 1 := by
        rw [map_mul, map_mul, ← hv_K'_def, hv, hτH_eq' x, hex, h_conj_eq, hσ]
        decide
      have := h_contra_helper x h_eq_one
      omega
    · -- v = (ofAdd 2, ofAdd 1), ψ = ψ₆: rule out via fixed-point constraint.
      exfalso
      have h_fix : psi6 v_K' = v_K' := by
        have h1 := hmap_H
        have h2 : e' (τ_H ⟨a ^ 2, ha_sq⟩) = e' ⟨a ^ 2, ha_sq⟩ := by
          rw [h1]
        rw [hτH_eq' ⟨a ^ 2, ha_sq⟩, h_conj_eq, hσ] at h2
        exact h2
      rw [hv] at h_fix
      revert h_fix
      decide

end OrderSixteen
