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

This proof handles the `orderOf a = 2` branch in full (yielding one of
`ext_16_{5,6,7,8}` according to the automorphism `τ`), and leaves the
`orderOf a ∈ {4, 16}` branches as `sorry`. -/
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
  obtain ⟨τ_H, hmap_H, hpow_H, R_H⟩ :=
    realise_from_normal_index_two H h_index a ha_notMem ha_sq
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
    · -- o(a) ∈ {4, 8} cases left as sorry; see milestones.md
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
