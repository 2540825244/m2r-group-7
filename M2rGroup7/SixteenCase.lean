import «M2rGroup7».SmallGroupsLibrary
import «M2rGroup7».PqCase
import Mathlib

namespace OrderSixteen

/-- Isomorphism for Wild's Fact 1. -/
noncomputable def fact1_mulEquiv
    {G : Type*} [Group G] (H₁ H₂ : Subgroup G)
    (h_disj : H₁ ⊓ H₂ = ⊥)
    (h_comm : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x) :
    (H₁ × H₂) ≃* ↑(H₁ ⊔ H₂) :=
  sorry

/-- Wild's Fact 1: If `H₁` and `H₂` are subgroups of `G` such that `H₁ ⊓ H₂ = {e}`
    and `∀ x ∈ H₁, ∀ y ∈ H₂, xy = yx`,
    then `H₁H₂` is a subgroup isomorphic to the direct product  `H₁ × H₂`. -/
lemma fact1 {G : Type*} [Group G] (H₁ H₂ : Subgroup G)
    (h_disj : H₁ ⊓ H₂ = ⊥)
    (h_comm : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x) :
    Nonempty (H₁ × H₂ ≃* ↑(H₁ ⊔ H₂)) :=
  ⟨fact1_mulEquiv H₁ H₂ h_disj h_comm⟩


/-- Wild's Fact 2, first part: If the order of each member of `G` is at most 2,
    then `G` is abelian. -/
lemma fact2_part1 {G : Type*} [Group G] (h : ∀ x : G, x ^ 2 = 1) :
    IsMulCommutative G := sorry

/-- Wild's Fact 2, second part: If the order of each member of `G` is at most 2
    and `G` is finite, then `G ≃ C₂ × ⋯ × C₂`. -/
lemma fact2_part2 {G : Type*} [Group G] [Finite G] (h : ∀ x : G, x ^ 2 = 1) :
    ∃ n : ℕ, Nonempty (G ≃* (Fin n → CyclicGroup 2)) := sorry

structure ExtensionType where
  N : Type*
  [g : Group N]
  n : Nat
  act : MulAut N
  glue : N
  map_glue : act glue = glue
  pow_n : act^ n = MulAut.conj glue

instance (E : ExtensionType) : Group E.N := E.g

structure RealiseExtType (G : Type*) [Group G] (E : ExtensionType) where
  /-- The inducing element `a` in `G` -/
  a : G
  /-- The embedding of `N` into `G` (acts as the inclusion of the normal subgroup) -/
  ι : E.N →* G
  /-- The action of `a` on `N` by conjugation matches `E.act` (`r` in the text) -/
  act_a : ∀ x : E.N, a * ι x * a⁻¹ = ι (E.act x)
  /-- The `n`-th power of `a` is the glue element (`v` in the text) -/
  pow_a_n : a ^ E.n = ι E.glue
  /-- Every element in `G` can be written exactly once as `ι x * a^i` for `0 ≤ i < n`.
      Using an equivalence (`≃`) guarantees both existence and uniqueness. -/
  equiv : E.N × Fin E.n ≃ G
  /-- The equivalence formally maps pairs `(x, i)` to `ι x * a^i` -/
  equiv_apply : ∀ (x : E.N) (i : Fin E.n), equiv (x, i) = ι x * a ^ (i : ℕ)

@[ext]
structure ExtEquiv (E_1 E_2 : ExtensionType) where
  φ : E_1.N ≃* E_2.N
  act_conj : E_2.act = (φ.symm.trans E_1.act).trans φ
  act_glue : E_2.glue = φ E_1.glue

namespace ExtEquiv

def refl (E : ExtensionType) : ExtEquiv E E where
  φ := MulEquiv.refl E.N
  act_conj := by
    -- Proof that the identity mapping satisfies the conjugation rule
    sorry
  act_glue := by
    -- Proof that the identity mapping fixes the glue
    sorry

def symm {E_1 E_2 : ExtensionType}
    (e : ExtEquiv E_1 E_2) :
    ExtEquiv E_2 E_1 where
  φ := e.φ.symm
  act_conj := by sorry
  act_glue := by sorry

def trans {E_1 E_2 E_3 : ExtensionType}
    (e_12 : ExtEquiv E_1 E_2) (e_23 : ExtEquiv E_2 E_3) :
    ExtEquiv E_1 E_3 where
  φ := e_12.φ.trans e_23.φ
  act_conj := by sorry
  act_glue := by sorry

noncomputable def realisingEquiv
    {E_1 E_2 : ExtensionType} {G_1 G_2 : Type*}
    [Group G_1] [Group G_2]
    (ext_equiv : ExtEquiv E_1 E_2)
    (R_1 : RealiseExtType G_1 E_1)
    (R_2 : RealiseExtType G_2 E_2) :
    G_1 ≃* G_2 where
  toFun g :=
    -- 1. Deconstruct the element g into its normal form (x, i) inside G_1
    let ⟨x, i⟩ := R_1.equiv.symm g
    -- 2. Map x using the blueprint isomorphism φ, and swap a_1 for a_2
    R_2.ι (ext_equiv.φ x) * R_2.a ^ (i : ℕ)

  invFun g :=
    -- 1. Deconstruct the element g into its normal form (x, i) inside G_2
    let ⟨x, i⟩ := R_2.equiv.symm g
    -- 2. Map x backwards using φ⁻¹, and swap a_2 for a_1
    R_1.ι (ext_equiv.φ.symm x) * R_1.a ^ (i : ℕ)

  -- Proof that Φ⁻¹(Φ(g)) = g
  left_inv g := by
    sorry

  -- Proof that Φ(Φ⁻¹(g)) = g
  right_inv g := by
    sorry

  -- The Homomorphism Proof (Equation 4 from the paper)
  map_mul' g h := by
    sorry

end ExtEquiv

/-- Two families of cyclic extensions over N share the same set of isomorphism classes when
    the glue elements v and w are related by an automorphism of N and the action set S is a
    union of conjugacy classes of Aut(N).

    Concretely, G_fam τ realises the extension (N, n, τ, v) and F_fam τ realises (N, n, τ, w)
    for each τ ∈ S. The conclusion asserts the range of isomorphism classes coincides:
    for every G_τ there exists F_σ isomorphic to it (and vice versa). -/
theorem extension_families_same_isoClasses
    {N : Type*} [Group N]
    (n : ℕ)
    (v w : N)
    -- v and w lie in the same Aut(N)-orbit: φ(v) = w
    (φ : MulAut N) (hφ : φ v = w)
    -- S ⊆ Aut(N) is closed under conjugation (a union of conjugacy classes)
    (S : Set (MulAut N))
    (hS : ∀ τ ∈ S, ∀ α : MulAut N, α * τ * α⁻¹ ∈ S)
    -- Validity of the v-extension family: each τ ∈ S fixes v and τⁿ = conj_v
    (hv_map : ∀ τ : S, τ.val v = v)
    (hv_pow : ∀ τ : S, τ.val ^ n = MulAut.conj v)
    -- Validity of the w-extension family: each τ ∈ S fixes w and τⁿ = conj_w
    (hw_map : ∀ τ : S, τ.val w = w)
    (hw_pow : ∀ τ : S, τ.val ^ n = MulAut.conj w)
    -- Families of groups indexed by S
    (G_fam F_fam : S → Type*)
    [∀ τ : S, Group (G_fam τ)]
    [∀ τ : S, Group (F_fam τ)]
    -- Each G_fam τ realises the extension type (N, n, τ, v)
    (R_G : ∀ τ : S, RealiseExtType (G_fam τ)
        { N := N, n := n, act := τ, glue := v,
          map_glue := hv_map τ, pow_n := hv_pow τ })
    -- Each F_fam τ realises the extension type (N, n, τ, w)
    (R_F : ∀ τ : S, RealiseExtType (F_fam τ)
        { N := N, n := n, act := τ, glue := w,
          map_glue := hw_map τ, pow_n := hw_pow τ }) :
    -- Conclusion: the two families produce the same set of isomorphism classes
    (∀ τ : S, ∃ σ : S, Nonempty (G_fam τ ≃* F_fam σ)) ∧
    (∀ τ : S, ∃ σ : S, Nonempty (F_fam τ ≃* G_fam σ)) := by
  sorry

noncomputable def conjugateActEquiv
    {N : Type*} [Group N]
    (n : ℕ)
    -- v is characteristic in N
    (v : N) (hv : ∀ φ : MulAut N, φ v = v)
    -- σ and τ are in the same conjugacy class
    (σ τ : MulAut N)
    (h_conj : ∃ α : MulAut N, α * τ * α⁻¹ = σ)
    (G G' : Type*)
    [Group G] [Group G']
    -- Validity proofs for the blueprints
    (hpow_σ : σ ^ n = MulAut.conj v)
    (hpow_τ : τ ^ n = MulAut.conj v)
    -- G realizes σ, G' realizes τ
    (R_G : RealiseExtType G
        { N := N, n := n, act := σ, glue := v,
          map_glue := hv σ, pow_n := hpow_σ })
    (R_G' : RealiseExtType G'
        { N := N, n := n, act := τ, glue := v,
          map_glue := hv τ, pow_n := hpow_τ }) :
    G ≃* G' := by
  sorry

end OrderSixteen
