import «M2rGroup7».SmallGroupsLibrary
import Mathlib

namespace OrderSixteen

structure ExtensionType where
  N : Type*
  [g : Group N]
  n : Nat
  act : MulAut N
  glue : N
  map_glue : act glue = glue
  pow_n : act ^ n = MulAut.conj glue

instance (E : ExtensionType) : Group E.N := E.g

structure RealiseExtType (G : Type*) [Group G] (E : ExtensionType) where
  /-- The inducing element `a` in `G` -/
  a : G
  /-- The embedding of `N` into `G` (acts as the inclusion of the normal subgroup) -/
  ι : E.N →* G
  /-- The action of `a` on `N` by conjugation matches `E.act` -/
  act_a : ∀ x : E.N, a * ι x * a⁻¹ = ι (E.act x)
  /-- The `n`-th power of `a` is the glue element -/
  pow_a_n : a ^ E.n = ι E.glue
  /-- Every element in `G` can be written exactly once as `ι x * a^i` for `0 ≤ i < n`.
      Using an equivalence (`≃`) guarantees both existence and uniqueness. -/
  equiv : E.N × Fin E.n ≃ G
  /-- The equivalence formally maps pairs `(x, i)` to `ι x * a^i` -/
  equiv_apply : ∀ (x : E.N) (i : Fin E.n), equiv (x, i) = ι x * a ^ (i : ℕ)

@[ext]
structure ExtEquiv (E_1 E_2 : ExtensionType) where
  hn : E_1.n = E_2.n
  φ : E_1.N ≃* E_2.N
  act_conj : E_2.act = (φ.symm.trans E_1.act).trans φ
  act_glue : E_2.glue = φ E_1.glue

namespace ExtEquiv

def refl (E : ExtensionType) : ExtEquiv E E where
  hn := rfl
  φ := MulEquiv.refl E.N
  act_conj := by
    ext x
    simp
  act_glue := by
    simp

def symm {E_1 E_2 : ExtensionType}
    (e : ExtEquiv E_1 E_2) :
    ExtEquiv E_2 E_1 where
  hn := e.hn.symm
  φ := e.φ.symm
  act_conj := by
    ext x
    simp only [MulEquiv.trans_apply, MulEquiv.symm_symm]
    have h := DFunLike.congr_fun e.act_conj (e.φ x)
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h
    rw [h, MulEquiv.symm_apply_apply]
  act_glue := by
    rw [e.act_glue, MulEquiv.symm_apply_apply]

def trans {E_1 E_2 E_3 : ExtensionType}
    (e_12 : ExtEquiv E_1 E_2) (e_23 : ExtEquiv E_2 E_3) :
    ExtEquiv E_1 E_3 where
  hn := e_12.hn.trans e_23.hn
  φ := e_12.φ.trans e_23.φ
  act_conj := by
    ext x
    simp only [MulEquiv.trans_apply, MulEquiv.symm_trans_apply]
    have h2 := DFunLike.congr_fun e_23.act_conj x
    have h1 := DFunLike.congr_fun e_12.act_conj (e_23.φ.symm x)
    simp only [MulEquiv.trans_apply] at h1 h2
    rw [h2, h1]
  act_glue := by
    simp only [MulEquiv.trans_apply]
    rw [e_23.act_glue, e_12.act_glue]

private lemma slide_pow {G : Type*} [Group G] {E : ExtensionType}
    (R : RealiseExtType G E) (k : ℕ) (y : E.N) :
    R.a ^ k * R.ι y = R.ι ((E.act ^ k) y) * R.a ^ k := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    have step : ∀ z : E.N, R.a * R.ι z = R.ι (E.act z) * R.a := fun z => by
      calc R.a * R.ι z
          = R.a * R.ι z * R.a⁻¹ * R.a := by group
        _ = R.ι (E.act z) * R.a := by rw [R.act_a]
    calc R.a ^ (k + 1) * R.ι y
        = R.a * R.a ^ k * R.ι y := by rw [pow_succ']
      _ = R.a * (R.ι ((E.act ^ k) y) * R.a ^ k) := by rw [mul_assoc, ih]
      _ = R.ι (E.act ((E.act ^ k) y)) * (R.a * R.a ^ k) := by
            rw [← mul_assoc, step, mul_assoc]
      _ = R.ι ((E.act ^ (k + 1)) y) * R.a ^ (k + 1) := by
            rw [← pow_succ']
            congr 1
            rw [pow_succ', MulAut.mul_apply]

private lemma act_conj_pow {E_1 E_2 : ExtensionType} (e : ExtEquiv E_1 E_2)
    (k : ℕ) (y : E_1.N) : e.φ ((E_1.act ^ k) y) = (E_2.act ^ k) (e.φ y) := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    have step : ∀ z : E_1.N, e.φ (E_1.act z) = E_2.act (e.φ z) := fun z => by
      have h := DFunLike.congr_fun e.act_conj (e.φ z)
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h
      exact h.symm
    simp only [pow_succ', MulAut.mul_apply]
    rw [step, ih]

private lemma toFun_ι_a_pow
    {G_1 G_2 : Type*} [Group G_1] [Group G_2]
    {E_1 E_2 : ExtensionType} (ext_equiv : ExtEquiv E_1 E_2)
    (R_1 : RealiseExtType G_1 E_1) (R_2 : RealiseExtType G_2 E_2)
    (z : E_1.N) (k : ℕ) :
    (fun g => let ⟨x, i⟩ := R_1.equiv.symm g; R_2.ι (ext_equiv.φ x) * R_2.a ^ (i : ℕ))
      (R_1.ι z * R_1.a ^ k) = R_2.ι (ext_equiv.φ z) * R_2.a ^ k := by
  have hn_pos : 0 < E_1.n := Fin.pos (R_1.equiv.symm 1).2
  suffices h : ∀ k : ℕ, ∀ z : E_1.N,
      (fun g => let ⟨x, i⟩ := R_1.equiv.symm g; R_2.ι (ext_equiv.φ x) * R_2.a ^ (i : ℕ))
        (R_1.ι z * R_1.a ^ k) = R_2.ι (ext_equiv.φ z) * R_2.a ^ k from h k z
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro z
    rcases Nat.lt_or_ge k E_1.n with hk | hk
    · have h : R_1.equiv.symm (R_1.ι z * R_1.a ^ k) = (z, ⟨k, hk⟩) :=
        R_1.equiv.symm_apply_eq.mpr (R_1.equiv_apply z ⟨k, hk⟩).symm
      simp [h]
    · have hlt : k - E_1.n < k := Nat.sub_lt (Nat.lt_of_lt_of_le hn_pos hk) hn_pos
      have hkn : k = E_1.n + (k - E_1.n) := (Nat.add_sub_cancel' hk).symm
      have heq1 : R_1.ι z * R_1.a ^ k = R_1.ι (z * E_1.glue) * R_1.a ^ (k - E_1.n) := by
        conv_lhs => rw [hkn]
        rw [pow_add, ← mul_assoc, mul_assoc (R_1.ι z), R_1.pow_a_n,
            ← mul_assoc, ← map_mul]
      have hkn2 : k = E_2.n + (k - E_1.n) := by rw [← ext_equiv.hn]; exact hkn
      have heq2 : R_2.ι (ext_equiv.φ z) * R_2.a ^ k =
          R_2.ι (ext_equiv.φ z * E_2.glue) * R_2.a ^ (k - E_1.n) := by
        conv_lhs => rw [hkn2]
        rw [pow_add, ← mul_assoc, mul_assoc (R_2.ι _), R_2.pow_a_n,
            ← mul_assoc, ← map_mul]
      rw [heq1, ih (k - E_1.n) hlt, heq2, map_mul, ext_equiv.act_glue]

noncomputable def realisingEquiv
    {E_1 E_2 : ExtensionType} {G_1 G_2 : Type*}
    [Group G_1] [Group G_2]
    (ext_equiv : ExtEquiv E_1 E_2)
    (R_1 : RealiseExtType G_1 E_1)
    (R_2 : RealiseExtType G_2 E_2) :
    G_1 ≃* G_2 where
  toFun g :=
    let p := R_1.equiv.symm g
    R_2.ι (ext_equiv.φ p.1) * R_2.a ^ (p.2 : ℕ)

  invFun g :=
    let p := R_2.equiv.symm g
    R_1.ι (ext_equiv.φ.symm p.1) * R_1.a ^ (p.2 : ℕ)

  left_inv g := by
    have hg : g = R_1.ι (R_1.equiv.symm g).1 * R_1.a ^ ((R_1.equiv.symm g).2 : ℕ) := by
      rw [← R_1.equiv_apply, Prod.mk.eta, R_1.equiv.apply_symm_apply]
    set x := (R_1.equiv.symm g).1
    set i := (R_1.equiv.symm g).2
    change R_1.ι (ext_equiv.φ.symm (R_2.equiv.symm
        (R_2.ι (ext_equiv.φ x) * R_2.a ^ (i : ℕ))).1) *
        R_1.a ^ ((R_2.equiv.symm (R_2.ι (ext_equiv.φ x) * R_2.a ^ (i : ℕ))).2 : ℕ) = g
    have h : R_2.equiv.symm (R_2.ι (ext_equiv.φ x) * R_2.a ^ (i : ℕ)) =
        (ext_equiv.φ x, Fin.cast ext_equiv.hn i) := by
      apply R_2.equiv.symm_apply_eq.mpr
      rw [R_2.equiv_apply]
      rfl
    rw [h]
    simp only [MulEquiv.symm_apply_apply, Fin.val_cast]
    exact hg.symm

  right_inv g := by
    have hg : g = R_2.ι (R_2.equiv.symm g).1 * R_2.a ^ ((R_2.equiv.symm g).2 : ℕ) := by
      rw [← R_2.equiv_apply, Prod.mk.eta, R_2.equiv.apply_symm_apply]
    set x := (R_2.equiv.symm g).1
    set i := (R_2.equiv.symm g).2
    change R_2.ι (ext_equiv.φ (R_1.equiv.symm
        (R_1.ι (ext_equiv.φ.symm x) * R_1.a ^ (i : ℕ))).1) *
        R_2.a ^ ((R_1.equiv.symm (R_1.ι (ext_equiv.φ.symm x) * R_1.a ^ (i : ℕ))).2 : ℕ) = g
    have h : R_1.equiv.symm (R_1.ι (ext_equiv.φ.symm x) * R_1.a ^ (i : ℕ)) =
        (ext_equiv.φ.symm x, Fin.cast ext_equiv.hn.symm i) := by
      apply R_1.equiv.symm_apply_eq.mpr
      rw [R_1.equiv_apply]
      rfl
    rw [h]
    simp only [MulEquiv.apply_symm_apply, Fin.val_cast]
    exact hg.symm

  map_mul' g h := by
    set x := (R_1.equiv.symm g).1 with hx
    set i := (R_1.equiv.symm g).2 with hi
    set y := (R_1.equiv.symm h).1 with hy
    set j := (R_1.equiv.symm h).2 with hj
    have hg : g = R_1.ι x * R_1.a ^ (i : ℕ) := by
      rw [← R_1.equiv_apply, hx, hi, Prod.mk.eta, R_1.equiv.apply_symm_apply]
    have hh : h = R_1.ι y * R_1.a ^ (j : ℕ) := by
      rw [← R_1.equiv_apply, hy, hj, Prod.mk.eta, R_1.equiv.apply_symm_apply]
    change R_2.ι (ext_equiv.φ (R_1.equiv.symm (g * h)).1) *
        R_2.a ^ ((R_1.equiv.symm (g * h)).2 : ℕ) =
        R_2.ι (ext_equiv.φ x) * R_2.a ^ (i : ℕ) *
        (R_2.ι (ext_equiv.φ y) * R_2.a ^ (j : ℕ))
    have prod_eq : g * h =
        R_1.ι (x * (E_1.act ^ (i : ℕ)) y) * R_1.a ^ ((i : ℕ) + (j : ℕ)) := by
      rw [hg, hh, mul_assoc, ← mul_assoc (R_1.a ^ (i : ℕ)), slide_pow R_1 (i : ℕ) y,
          mul_assoc, ← mul_assoc (R_1.ι _), ← R_1.ι.map_mul, pow_add]
    rw [prod_eq]
    have key := toFun_ι_a_pow ext_equiv R_1 R_2 (x * (E_1.act ^ (i : ℕ)) y) ((i : ℕ) + (j : ℕ))
    have key' : R_2.ι (ext_equiv.φ (R_1.equiv.symm
          (R_1.ι (x * (E_1.act ^ (i : ℕ)) y) * R_1.a ^ ((i : ℕ) + (j : ℕ)))).1) *
        R_2.a ^ ((R_1.equiv.symm (R_1.ι (x * (E_1.act ^ (i : ℕ)) y) *
          R_1.a ^ ((i : ℕ) + (j : ℕ)))).2 : ℕ) =
        R_2.ι (ext_equiv.φ (x * (E_1.act ^ (i : ℕ)) y)) *
          R_2.a ^ ((i : ℕ) + (j : ℕ)) := by
      convert key using 2
    rw [key']
    rw [mul_assoc, ← mul_assoc (R_2.a ^ (i : ℕ)),
        slide_pow R_2 (i : ℕ) (ext_equiv.φ y),
        mul_assoc, ← mul_assoc (R_2.ι _), ← map_mul, pow_add]
    congr 2
    rw [map_mul, act_conj_pow ext_equiv]

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
  constructor
  · intro τ
    have hσ : φ * τ.val * φ⁻¹ ∈ S := hS τ.val τ.2 φ
    refine ⟨⟨φ * τ.val * φ⁻¹, hσ⟩, ⟨?_⟩⟩
    exact ExtEquiv.realisingEquiv
      (E_1 := { N := N, n := n, act := τ.val, glue := v,
                map_glue := hv_map τ, pow_n := hv_pow τ })
      (E_2 := { N := N, n := n, act := φ * τ.val * φ⁻¹, glue := w,
                map_glue := hw_map ⟨φ * τ.val * φ⁻¹, hσ⟩,
                pow_n := hw_pow ⟨φ * τ.val * φ⁻¹, hσ⟩ })
      (ext_equiv := {
        hn := rfl
        φ := φ
        act_conj := by
          ext x
          change (φ * τ.val * φ⁻¹) x = φ (τ.val (φ.symm x))
          rw [MulAut.mul_apply, MulAut.mul_apply]
          rfl
        act_glue := hφ.symm })
      (R_G τ) (R_F ⟨φ * τ.val * φ⁻¹, hσ⟩)
  · intro τ
    have hσ : φ⁻¹ * τ.val * (φ⁻¹)⁻¹ ∈ S := hS τ.val τ.2 φ⁻¹
    simp only [inv_inv] at hσ
    refine ⟨⟨φ⁻¹ * τ.val * φ, hσ⟩, ⟨?_⟩⟩
    exact ExtEquiv.realisingEquiv
      (E_1 := { N := N, n := n, act := τ.val, glue := w,
                map_glue := hw_map τ, pow_n := hw_pow τ })
      (E_2 := { N := N, n := n, act := φ⁻¹ * τ.val * φ, glue := v,
                map_glue := hv_map ⟨φ⁻¹ * τ.val * φ, hσ⟩,
                pow_n := hv_pow ⟨φ⁻¹ * τ.val * φ, hσ⟩ })
      (ext_equiv := {
        hn := rfl
        φ := φ⁻¹
        act_conj := by
          ext x
          change (φ⁻¹ * τ.val * φ) x = φ⁻¹ (τ.val ((φ⁻¹).symm x))
          rw [MulAut.mul_apply, MulAut.mul_apply]
          rfl
        act_glue := by
          change v = φ⁻¹ w
          rw [← hφ]
          exact (MulEquiv.symm_apply_apply φ v).symm })
      (R_F τ) (R_G ⟨φ⁻¹ * τ.val * φ, hσ⟩)

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
    -- G realises σ, G' realises τ
    (R_G : RealiseExtType G
        { N := N, n := n, act := σ, glue := v,
          map_glue := hv σ, pow_n := hpow_σ })
    (R_G' : RealiseExtType G'
        { N := N, n := n, act := τ, glue := v,
          map_glue := hv τ, pow_n := hpow_τ }) :
    G ≃* G' := by
  classical
  let α : MulAut N := h_conj.choose
  have hα : α * τ * α⁻¹ = σ := h_conj.choose_spec
  refine ExtEquiv.realisingEquiv
    (E_1 := { N := N, n := n, act := σ, glue := v,
              map_glue := hv σ, pow_n := hpow_σ })
    (E_2 := { N := N, n := n, act := τ, glue := v,
              map_glue := hv τ, pow_n := hpow_τ })
    (ext_equiv := {
      hn := rfl
      φ := α⁻¹
      act_conj := ?_
      act_glue := (hv α⁻¹).symm })
    R_G R_G'
  ext x
  change τ x = α⁻¹ (σ ((α⁻¹).symm x))
  have h : (α⁻¹).symm = α := rfl
  rw [h]
  have step : τ = α⁻¹ * σ * α := by
    rw [← hα]; group
  rw [DFunLike.congr_fun step x, MulAut.mul_apply, MulAut.mul_apply]

end OrderSixteen
