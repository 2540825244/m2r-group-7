import «M2rGroup7».SmallGroupsLibrary
import «M2rGroup7».PqCase
import Mathlib

namespace OrderSixteen

section Preliminary

/-- Wild's Fact 1: If `H₁ ⊓ H₂ = ⊥` and elements of `H₁` commute with elements of `H₂`,
    the multiplication map `H₁ × H₂ → H₁ ⊔ H₂` is a group isomorphism.
    Proved via `Subgroup.coe_mul_of_right_le_normalizer_left`. -/
noncomputable def mulEquiv_sup_of_disjoint_comm
    {G : Type*} [Group G] (H₁ H₂ : Subgroup G)
    (h_disj : H₁ ⊓ H₂ = ⊥)
    (h_comm : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x) :
    (H₁ × H₂) ≃* ↑(H₁ ⊔ H₂) := by
  -- H₂ normalises H₁: commutativity forces conjugation y * x * y⁻¹ = x
  have hH₂_norm : H₂ ≤ Subgroup.normalizer H₁ := fun y hy => by
    rw [Subgroup.mem_normalizer_iff]; intro x; constructor
    · intro hx
      have : y * x * y⁻¹ = x :=
        calc y * x * y⁻¹ = x * y * y⁻¹ := by rw [← h_comm x hx y hy]
          _ = x := by group
      rwa [this]
    · intro hyx
      have comm_z : y * x * y⁻¹ * y⁻¹ = y⁻¹ * (y * x * y⁻¹) :=
        h_comm (y * x * y⁻¹) hyx y⁻¹ (H₂.inv_mem hy)
      have hxz : x = y * x * y⁻¹ :=
        calc x = y⁻¹ * (y * x * y⁻¹) * y := by group
          _ = y * x * y⁻¹ * y⁻¹ * y := by rw [← comm_z]
          _ = y * x * y⁻¹ := by group
      rwa [hxz]
  let φ : H₁ × H₂ →* ↑(H₁ ⊔ H₂) :=
    { toFun := fun p => ⟨↑p.1 * ↑p.2,
        (H₁ ⊔ H₂).mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        simp only [Prod.mul_def, Subgroup.coe_mul]
        calc (↑a.1 : G) * ↑b.1 * (↑a.2 * ↑b.2)
            = ↑a.1 * (↑b.1 * ↑a.2) * ↑b.2 := by group
          _ = ↑a.1 * (↑a.2 * ↑b.1) * ↑b.2 := by rw [h_comm ↑b.1 b.1.2 ↑a.2 a.2.2]
          _ = ↑a.1 * ↑a.2 * (↑b.1 * ↑b.2) := by group) }
  refine MulEquiv.ofBijective φ ⟨?_, ?_⟩
  · intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ hab
    have hab' : (↑a₁ : G) * ↑a₂ = ↑b₁ * ↑b₂ := Subtype.ext_iff.mp hab
    have key : (↑a₁ : G)⁻¹ * ↑b₁ ∈ H₁ ⊓ H₂ := Subgroup.mem_inf.mpr ⟨
      H₁.mul_mem (H₁.inv_mem a₁.2) b₁.2,
      show (↑a₁ : G)⁻¹ * ↑b₁ ∈ H₂ from by
        have heq : (↑a₁ : G)⁻¹ * ↑b₁ = ↑a₂ * (↑b₂ : G)⁻¹ :=
          calc (↑a₁ : G)⁻¹ * ↑b₁
              = (↑a₁ : G)⁻¹ * (↑b₁ * ↑b₂) * (↑b₂ : G)⁻¹ := by group
            _ = (↑a₁ : G)⁻¹ * (↑a₁ * ↑a₂) * (↑b₂ : G)⁻¹ := by rw [← hab']
            _ = ↑a₂ * (↑b₂ : G)⁻¹ := by group
        rw [heq]; exact H₂.mul_mem a₂.2 (H₂.inv_mem b₂.2)⟩
    rw [h_disj] at key
    have hval₁ : (↑a₁ : G) = ↑b₁ := inv_mul_eq_one.mp (Subgroup.mem_bot.mp key)
    have hval₂ : (↑a₂ : G) = ↑b₂ :=
      calc (↑a₂ : G) = (↑a₁ : G)⁻¹ * (↑a₁ * ↑a₂) := by group
        _ = (↑a₁ : G)⁻¹ * (↑b₁ * ↑b₂) := by rw [hab']
        _ = ↑b₂ := by rw [← hval₁]; group
    exact Prod.ext (Subtype.ext hval₁) (Subtype.ext hval₂)
  · open scoped Pointwise in
    intro ⟨g, hg⟩
    have hg' : g ∈ (H₁ : Set G) * H₂ := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left H₁ H₂ hH₂_norm]
      exact SetLike.mem_coe.mpr hg
    obtain ⟨h₁, h₁_mem, h₂, h₂_mem, heq⟩ := Set.mem_mul.mp hg'
    exact ⟨⟨⟨h₁, h₁_mem⟩, ⟨h₂, h₂_mem⟩⟩, Subtype.ext heq⟩

/-- Wild's Fact 2, first part: If every element of `G` squares to 1, then `G` is abelian.
    Follows from `Commute.of_orderOf_dvd_two`. -/
lemma isMulCommutative_of_sq_eq_one {G : Type*} [Group G] (h : ∀ x : G, x ^ 2 = 1) :
    IsMulCommutative G where
  is_comm := ⟨fun a b =>
    (Commute.of_orderOf_dvd_two (fun x => orderOf_dvd_of_pow_eq_one (h x)) a b).eq⟩

/-- Wild's Fact 2, second part: If every element of `G` squares to 1 and `G` is finite,
    then `G ≃ Fin n → C₂` for some `n`. -/
lemma mulEquiv_pi_cyclicTwo_of_sq_eq_one {G : Type*} [Group G] [Finite G]
    (h : ∀ x : G, x ^ 2 = 1) :
    ∃ n : ℕ, Nonempty (G ≃* (Fin n → CyclicGroup 2)) := sorry

/-- Wild's Fact 3: `Aut(C₄) ≃ C₂`. -/
lemma aut_C4_iso_C2 : Nonempty (MulAut (CyclicGroup 4) ≃* CyclicGroup 2) := sorry

/-- Wild's Fact 3: `Aut(C₈) ≃ C₂ × C₂`. -/
lemma aut_C8_iso_C2_prod_C2 : Nonempty (MulAut (CyclicGroup 8) ≃* CyclicGroup 2 × CyclicGroup 2) := sorry

/-- Wild's Fact 4: `Aut(K₈) ≃ D₈`, where `K₈ = C₄ × C₂`. -/
lemma aut_C4_prod_C2_iso_D8 :
    Nonempty (MulAut (CyclicGroup 4 × CyclicGroup 2) ≃* DihedralGroup 4) := sorry

/-- Wild's Fact 5: For any element `v` in a finite group `G`,
    `|class(v)| · |C(v)| = |G|` (orbit-stabilizer for conjugation).
    Follows from `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`. -/
lemma card_conj_orbit_mul_card_centralizer {G : Type*} [Group G] [Finite G] (v : G) :
    Nat.card (MulAction.orbit (ConjAct G) (ConjAct.toConjAct v)) *
    Nat.card (MulAction.stabilizer (ConjAct G) (ConjAct.toConjAct v)) =
    Nat.card G := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  simp only [Nat.card_eq_fintype_card]
  exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) (ConjAct.toConjAct v)

/-- Wild's Fact 6: If `|G| = pⁿ` with `n > 0` for a prime `p`, then `p ∣ |Z(G)|`.
    Follows from `IsPGroup.card_center_eq_prime_pow`. -/
lemma prime_dvd_card_center {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : Nat.Prime p) {n : ℕ} (hn : Nat.card G = p ^ n) (hn_pos : 0 < n) :
    p ∣ Nat.card (Subgroup.center G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsPGroup p G := IsPGroup.of_card hn
  obtain ⟨k, hk_pos, hk⟩ := IsPGroup.card_center_eq_prime_pow hn hn_pos
  exact hk ▸ dvd_pow_self p hk_pos.ne'

end Preliminary

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
  -- Strong induction on k with z generalised
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
    -- 1. Deconstruct the element g into its normal form (x, i) inside G_1
    let p := R_1.equiv.symm g
    -- 2. Map x using the blueprint isomorphism φ, and swap a_1 for a_2
    R_2.ι (ext_equiv.φ p.1) * R_2.a ^ (p.2 : ℕ)

  invFun g :=
    -- 1. Deconstruct the element g into its normal form (x, i) inside G_2
    let p := R_2.equiv.symm g
    -- 2. Map x backwards using φ⁻¹, and swap a_2 for a_1
    R_1.ι (ext_equiv.φ.symm p.1) * R_1.a ^ (p.2 : ℕ)

  -- Proof that Φ⁻¹(Φ(g)) = g
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

  -- Proof that Φ(Φ⁻¹(g)) = g
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

  -- The Homomorphism Proof (Equation 4 from the paper)
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
    -- unfold the lambda+match in key into projection form so it matches the goal
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

lemma exists_normal_C8_or_C4_C2
    {G : Type*} [Group G]
    (hn : Nat.card G = 16)
    (h_non_iso : IsEmpty (G ≃* CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2)) :
    (∃ H : Subgroup G, H.Normal ∧ Nonempty (H ≃* CyclicGroup 8)) ∨
    (∃ H : Subgroup G, H.Normal ∧ Nonempty (H ≃* CyclicGroup 4 × CyclicGroup 2)) := by
  by_cases h_order_8 : ∃ x : G , orderOf x = 8
  . -- There is element of order 8, then C8 ◃ G
    left
    obtain ⟨x, hx⟩ := h_order_8
    let H := Subgroup.zpowers x
    use H
    have hi : H.index = 2 := by
      sorry
    haveI : H.Normal := Subgroup.normal_of_index_eq_two hi
    have h_card : Nat.card H = 8 := by
      sorry
    haveI : IsCyclic H := by
      sorry
    let iso : H ≃* CyclicGroup 8 := mulEquivOfCyclicCardEq (
        by simp only [h_card, card_cyclicGroup]
      )
    tauto
  . -- There are no elements of order 8, then K8 ◃ G
    right
    have h_max_order : ∃ z : G , orderOf z = 4 := by
      sorry
    obtain ⟨z, hz⟩ : ∃ z : G, orderOf z = 2 := by
      -- fact 6
      sorry
    let H := Subgroup.zpowers z
    haveI : H.Normal := by
      sorry
    by_cases hx : ∃ x : G , orderOf x = 4 ∧ x^2 ≠ z
    . -- There is x of order 4 such that x^2 ≠ z
      obtain ⟨x, hx⟩ := hx
      let L := Subgroup.zpowers x
      have h_disj : H ⊓ L = ⊥ := by
        sorry
      let K := Subgroup.closure {x, z}
      use K
      haveI : K.Normal := by
        sorry
      let iso : K ≃* CyclicGroup 4 × CyclicGroup 2 := by
        have h_card : Nat.card H = 2 := by
          sorry
        letI : H ≃* CyclicGroup 2 := mulEquivOfCyclicCardEq (
            by simp only [h_card, card_cyclicGroup]
          )
        have l_card : Nat.card L = 4 := by
          sorry
        letI : L ≃* CyclicGroup 4 := mulEquivOfCyclicCardEq (
            by simp only [l_card, card_cyclicGroup]
          )
        -- apply fact 1
        sorry
      tauto
    . -- Every x of order 4 has x^2 = z
      have hx : ∀ x : G, orderOf x = 4 → x^2 = z := by simp_all
      sorry

/-- Universal equivalence between the index `Fin 2` and the quotient group `CyclicGroup 2`. -/
def fin2EquivC2 : Fin 2 ≃ CyclicGroup 2 where
  toFun i := match i with | ⟨0, _⟩ => 1 | ⟨1, _⟩ => Multiplicative.ofAdd 1
  invFun x := if x = 1 then 0 else 1
  left_inv i := by fin_cases i <;> rfl
  right_inv x := by revert x; decide

/-! ## Auxiliary automorphisms used in the order-16 blueprints. -/

/-- The non-trivial action of `C_2` on `C_8` by `x ↦ x^7 = x⁻¹`. -/
def c2OnC8Pow7 : CyclicGroup 2 →* MulAut (CyclicGroup 8) :=
  have h : ∀ x : CyclicGroup 8, (x ^ 7) ^ 7 = x := by decide
  let pow7 : MulAut (CyclicGroup 8) :=
    { toFun := (· ^ 7)
      invFun := (· ^ 7)
      left_inv := h
      right_inv := h
      map_mul' := fun a b => mul_pow a b 7 }
  cyclicHom 2 pow7 (by
    ext x
    change (x ^ 7) ^ 7 = x
    exact h x)

/-- The order-2 automorphism `(a, b) ↦ (a³, b)` of `K_8 = C_4 × C_2`. -/
def psi3 : MulAut (CyclicGroup 4 × CyclicGroup 2) where
  toFun ab := (ab.1 ^ 3, ab.2)
  invFun ab := (ab.1 ^ 3, ab.2)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

/-- The order-2 automorphism of `K_8 = C_4 × C_2` sending `x = (gen_C4, 1) ↦ xy` and
    `y = (1, gen_C2) ↦ y`. Concretely `(a, b) ↦ (a, b · (gen_C2)^{a_index})`. -/
def psi5 : MulAut (CyclicGroup 4 × CyclicGroup 2) where
  toFun ab :=
    (ab.1,
     ab.2 * (show CyclicGroup 2 from
       (Multiplicative.ofAdd 1 : CyclicGroup 2) ^ (Multiplicative.toAdd ab.1).val))
  invFun ab :=
    (ab.1,
     ab.2 * (show CyclicGroup 2 from
       (Multiplicative.ofAdd 1 : CyclicGroup 2) ^ (Multiplicative.toAdd ab.1).val))
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

/-! ## The 13 cyclic-extension blueprints for groups of order 16.

Indexing follows the `retrieve 16 i` table from `SmallGroupsLibrary.lean`. -/

/-- Blueprint `(C₈, 2, id, x)` realised by `CyclicGroup 16`. -/
@[reducible] def ext_16_1 : ExtensionType where
  N := CyclicGroup 8
  n := 2
  act := 1
  glue := Multiplicative.ofAdd 1
  map_glue := rfl
  pow_n := by ext y; revert y; decide

noncomputable def realise_16_1 : RealiseExtType (CyclicGroup 16) ext_16_1 :=
  let a : CyclicGroup 16 := Multiplicative.ofAdd 1
  let ι : CyclicGroup 8 →* CyclicGroup 16 := cyclicHom 8 (Multiplicative.ofAdd 2) (by decide)
  { a := a
    ι := ι
    act_a := by intro x; simp
    pow_a_n := by decide
    equiv := Equiv.ofBijective
      (fun p : CyclicGroup 8 × Fin 2 => ι p.1 * a ^ (p.2 : ℕ))
      (by decide)
    equiv_apply := fun _ _ => rfl }

/-- Blueprint `(K₈, 2, id, y)` realised by `CyclicGroup 4 × CyclicGroup 4`. -/
@[reducible] def ext_16_2 : ExtensionType where
  N := CyclicGroup 4 × CyclicGroup 2
  n := 2
  act := 1
  glue := (1, Multiplicative.ofAdd 1)
  map_glue := rfl
  pow_n := by ext y <;> (revert y; decide)

noncomputable def realise_16_2 : RealiseExtType (CyclicGroup 4 × CyclicGroup 4) ext_16_2 :=
  let a : CyclicGroup 4 × CyclicGroup 4 := (1, Multiplicative.ofAdd 1)
  let ι : CyclicGroup 4 × CyclicGroup 2 →* CyclicGroup 4 × CyclicGroup 4 :=
    { toFun := fun ab =>
        (ab.1,
         (show CyclicGroup 4 from
           (Multiplicative.ofAdd 2 : CyclicGroup 4) ^ (Multiplicative.toAdd ab.2).val))
      map_one' := by decide
      map_mul' := by intro a b; revert a b; decide }
  { a := a
    ι := ι
    act_a := by intro x; simp [mul_comm]
    pow_a_n := by decide
    equiv := Equiv.ofBijective
      (fun p : (CyclicGroup 4 × CyclicGroup 2) × Fin 2 => ι p.1 * a ^ (p.2 : ℕ))
      (by decide)
    equiv_apply := fun _ _ => rfl }

/-- Blueprint `(K₈, 2, ψ₅, e)` realised by `(C₂ × C₂) ⋊[c4OnC2sqSwap] C₄`. -/
@[reducible] def ext_16_3 : ExtensionType where
  N := CyclicGroup 4 × CyclicGroup 2
  n := 2
  act := psi5
  glue := (1, 1)
  map_glue := by decide
  pow_n := by ext y <;> (revert y; decide)

noncomputable def realise_16_3 :
    RealiseExtType ((CyclicGroup 2 × CyclicGroup 2) ⋊[c4OnC2sqSwap] CyclicGroup 4) ext_16_3 :=
  let G : Type := (CyclicGroup 2 × CyclicGroup 2) ⋊[c4OnC2sqSwap] CyclicGroup 4
  let ξ : G := ⟨(1, 1), Multiplicative.ofAdd 1⟩
  let ζ : G := ⟨(Multiplicative.ofAdd 1, Multiplicative.ofAdd 1), 1⟩
  let a : G := ⟨(Multiplicative.ofAdd 1, 1), 1⟩
  let ι : CyclicGroup 4 × CyclicGroup 2 →* G :=
    { toFun := fun ab => ξ ^ (Multiplicative.toAdd ab.1).val * ζ ^ (Multiplicative.toAdd ab.2).val
      map_one' := by decide
      map_mul' := by intro a b; revert a b; decide }
  { a := a
    ι := ι
    act_a := by intro x; revert x; decide
    pow_a_n := by decide
    equiv := Equiv.ofBijective
      (fun p : (CyclicGroup 4 × CyclicGroup 2) × Fin 2 => ι p.1 * a ^ (p.2 : ℕ))
      (by decide)
    equiv_apply := fun _ _ => rfl }

/-- Blueprint `(K₈, 2, ψ₅, x²)` realised by `C₄ ⋊[c4OnC4Inv] C₄`. -/
@[reducible] def ext_16_4 : ExtensionType where
  N := CyclicGroup 4 × CyclicGroup 2
  n := 2
  act := psi5
  glue := (Multiplicative.ofAdd 2, 1)
  map_glue := by decide
  pow_n := by ext y <;> (revert y; decide)

noncomputable def realise_16_4 :
    RealiseExtType (CyclicGroup 4 ⋊[c4OnC4Inv] CyclicGroup 4) ext_16_4 :=
  let G : Type := CyclicGroup 4 ⋊[c4OnC4Inv] CyclicGroup 4
  let x4 : G := ⟨1, Multiplicative.ofAdd 1⟩
  let x2 : G := ⟨Multiplicative.ofAdd 2, 1⟩
  let a : G := ⟨Multiplicative.ofAdd 1, Multiplicative.ofAdd 1⟩
  let ι : CyclicGroup 4 × CyclicGroup 2 →* G :=
    { toFun := fun ab =>
        x4 ^ (Multiplicative.toAdd ab.1).val * x2 ^ (Multiplicative.toAdd ab.2).val
      map_one' := by decide
      map_mul' := by intro a b; revert a b; decide }
  { a := a
    ι := ι
    act_a := by intro x; revert x; decide
    pow_a_n := by decide
    equiv := Equiv.ofBijective
      (fun p : (CyclicGroup 4 × CyclicGroup 2) × Fin 2 => ι p.1 * a ^ (p.2 : ℕ))
      (by decide)
    equiv_apply := fun _ _ => rfl }

/-- Blueprint `(C₈, 2, id, e)` realised by `CyclicGroup 8 × CyclicGroup 2`. -/
@[reducible] def ext_16_5 : ExtensionType where
  N := CyclicGroup 8
  n := 2
  act := 1
  glue := 1
  map_glue := rfl
  pow_n := by ext y; revert y; decide

noncomputable def realise_16_5 :
    RealiseExtType (CyclicGroup 8 × CyclicGroup 2) ext_16_5 :=
  let a : CyclicGroup 8 × CyclicGroup 2 := (1, Multiplicative.ofAdd 1)
  let ι : CyclicGroup 8 →* CyclicGroup 8 × CyclicGroup 2 :=
    MonoidHom.inl (CyclicGroup 8) (CyclicGroup 2)
  { a := a
    ι := ι
    act_a := by intro x; simp [mul_comm]
    pow_a_n := by decide
    equiv := Equiv.ofBijective
      (fun p : CyclicGroup 8 × Fin 2 => ι p.1 * a ^ (p.2 : ℕ))
      (by decide)
    equiv_apply := fun _ _ => rfl }

/-- Blueprint `(C₈, 2, x ↦ x⁵, e)` realised by `C₈ ⋊[c2OnC8Pow5] C₂`. -/
@[reducible] def ext_16_6 : ExtensionType where
  N := CyclicGroup 8
  n := 2
  act := c2OnC8Pow5 (Multiplicative.ofAdd 1)
  glue := 1
  map_glue := by decide
  pow_n := by ext y; revert y; decide

noncomputable def realise_16_6 :
    RealiseExtType (CyclicGroup 8 ⋊[c2OnC8Pow5] CyclicGroup 2) ext_16_6 :=
  let G : Type := CyclicGroup 8 ⋊[c2OnC8Pow5] CyclicGroup 2
  let a : G := ⟨1, Multiplicative.ofAdd 1⟩
  let ι : CyclicGroup 8 →* G := SemidirectProduct.inl
  { a := a
    ι := ι
    act_a := by intro x; revert x; decide
    pow_a_n := by decide
    equiv := Equiv.ofBijective
      (fun p : CyclicGroup 8 × Fin 2 => ι p.1 * a ^ (p.2 : ℕ))
      (by decide)
    equiv_apply := fun _ _ => rfl }

/-- Blueprint `(C₈, 2, x ↦ x⁷, e)` realised by `DihedralGroup 8`. -/
@[reducible] def ext_16_7 : ExtensionType where
  N := CyclicGroup 8
  n := 2
  act := c2OnC8Pow7 (Multiplicative.ofAdd 1)
  glue := 1
  map_glue := by decide
  pow_n := by ext y; revert y; decide

noncomputable def realise_16_7 : RealiseExtType (DihedralGroup 8) ext_16_7 :=
  let a : DihedralGroup 8 := DihedralGroup.sr 0
  let ι : CyclicGroup 8 →* DihedralGroup 8 := cyclicHom 8 (DihedralGroup.r 1) (by decide)
  { a := a
    ι := ι
    act_a := by intro x; revert x; decide
    pow_a_n := by decide
    equiv := Equiv.ofBijective
      (fun p : CyclicGroup 8 × Fin 2 => ι p.1 * a ^ (p.2 : ℕ))
      (by decide)
    equiv_apply := fun _ _ => rfl }

/-- Blueprint `(C₈, 2, x ↦ x³, e)` realised by `C₈ ⋊[c2OnC8Pow3] C₂`. -/
@[reducible] def ext_16_8 : ExtensionType where
  N := CyclicGroup 8
  n := 2
  act := c2OnC8Pow3 (Multiplicative.ofAdd 1)
  glue := 1
  map_glue := by decide
  pow_n := by ext y; revert y; decide

noncomputable def realise_16_8 :
    RealiseExtType (CyclicGroup 8 ⋊[c2OnC8Pow3] CyclicGroup 2) ext_16_8 :=
  let G : Type := CyclicGroup 8 ⋊[c2OnC8Pow3] CyclicGroup 2
  let a : G := ⟨1, Multiplicative.ofAdd 1⟩
  let ι : CyclicGroup 8 →* G := SemidirectProduct.inl
  { a := a
    ι := ι
    act_a := by intro x; revert x; decide
    pow_a_n := by decide
    equiv := Equiv.ofBijective
      (fun p : CyclicGroup 8 × Fin 2 => ι p.1 * a ^ (p.2 : ℕ))
      (by decide)
    equiv_apply := fun _ _ => rfl }

/-- Blueprint `(C₈, 2, x ↦ x⁷, x⁴)` realised by `QuaternionGroup 4`. -/
@[reducible] def ext_16_9 : ExtensionType where
  N := CyclicGroup 8
  n := 2
  act := c2OnC8Pow7 (Multiplicative.ofAdd 1)
  glue := Multiplicative.ofAdd 4
  map_glue := by decide
  pow_n := by ext y; revert y; decide

noncomputable def realise_16_9 : RealiseExtType (QuaternionGroup 4) ext_16_9 :=
  let a : QuaternionGroup 4 := QuaternionGroup.xa 0
  let ι : CyclicGroup 8 →* QuaternionGroup 4 :=
    cyclicHom 8 (QuaternionGroup.a 1) (by decide)
  { a := a
    ι := ι
    act_a := by intro x; revert x; decide
    pow_a_n := by decide
    equiv := Equiv.ofBijective
      (fun p : CyclicGroup 8 × Fin 2 => ι p.1 * a ^ (p.2 : ℕ))
      (by decide)
    equiv_apply := fun _ _ => rfl }

/-- Blueprint `(K₈, 2, id, e)` realised by `(C₄ × C₂) × C₂`. -/
@[reducible] def ext_16_10 : ExtensionType where
  N := CyclicGroup 4 × CyclicGroup 2
  n := 2
  act := 1
  glue := (1, 1)
  map_glue := rfl
  pow_n := by ext y <;> (revert y; decide)

noncomputable def realise_16_10 :
    RealiseExtType ((CyclicGroup 4 × CyclicGroup 2) × CyclicGroup 2) ext_16_10 :=
  let a : (CyclicGroup 4 × CyclicGroup 2) × CyclicGroup 2 := (1, Multiplicative.ofAdd 1)
  let ι : CyclicGroup 4 × CyclicGroup 2 →* (CyclicGroup 4 × CyclicGroup 2) × CyclicGroup 2 :=
    MonoidHom.inl (CyclicGroup 4 × CyclicGroup 2) (CyclicGroup 2)
  { a := a
    ι := ι
    act_a := by intro x; simp [mul_comm]
    pow_a_n := by decide
    equiv := Equiv.ofBijective
      (fun p : (CyclicGroup 4 × CyclicGroup 2) × Fin 2 => ι p.1 * a ^ (p.2 : ℕ))
      (by decide)
    equiv_apply := fun _ _ => rfl }

/-- Blueprint `(K₈, 2, ψ₃, e)` realised by `C₂ × DihedralGroup 4`. -/
@[reducible] def ext_16_11 : ExtensionType where
  N := CyclicGroup 4 × CyclicGroup 2
  n := 2
  act := psi3
  glue := (1, 1)
  map_glue := by decide
  pow_n := by ext y <;> (revert y; decide)

noncomputable def realise_16_11 :
    RealiseExtType (CyclicGroup 2 × DihedralGroup 4) ext_16_11 :=
  let a : CyclicGroup 2 × DihedralGroup 4 := (Multiplicative.ofAdd 1, DihedralGroup.sr 0)
  let ι : CyclicGroup 4 × CyclicGroup 2 →* CyclicGroup 2 × DihedralGroup 4 :=
    { toFun := fun ab => (ab.2, DihedralGroup.r (Multiplicative.toAdd ab.1))
      map_one' := by decide
      map_mul' := by intro a b; revert a b; decide }
  { a := a
    ι := ι
    act_a := by intro x; revert x; decide
    pow_a_n := by decide
    equiv := Equiv.ofBijective
      (fun p : (CyclicGroup 4 × CyclicGroup 2) × Fin 2 => ι p.1 * a ^ (p.2 : ℕ))
      (by decide)
    equiv_apply := fun _ _ => rfl }

/-- Blueprint `(K₈, 2, ψ₃, x²)` realised by `C₂ × QuaternionGroup 2`. -/
@[reducible] def ext_16_12 : ExtensionType where
  N := CyclicGroup 4 × CyclicGroup 2
  n := 2
  act := psi3
  glue := (Multiplicative.ofAdd 2, 1)
  map_glue := by decide
  pow_n := by ext y <;> (revert y; decide)

noncomputable def realise_16_12 :
    RealiseExtType (CyclicGroup 2 × QuaternionGroup 2) ext_16_12 :=
  let a : CyclicGroup 2 × QuaternionGroup 2 := (Multiplicative.ofAdd 1, QuaternionGroup.xa 0)
  let ι : CyclicGroup 4 × CyclicGroup 2 →* CyclicGroup 2 × QuaternionGroup 2 :=
    { toFun := fun ab => (ab.2, QuaternionGroup.a (Multiplicative.toAdd ab.1))
      map_one' := by decide
      map_mul' := by intro a b; revert a b; decide }
  { a := a
    ι := ι
    act_a := by intro x; revert x; decide
    pow_a_n := by decide
    equiv := Equiv.ofBijective
      (fun p : (CyclicGroup 4 × CyclicGroup 2) × Fin 2 => ι p.1 * a ^ (p.2 : ℕ))
      (by decide)
    equiv_apply := fun _ _ => rfl }

/-- Blueprint `(K₈, 2, ψ₆, e)` realised by `(C₄ × C₂) ⋊[c2OnK8Psi6] C₂`. -/
@[reducible] def ext_16_13 : ExtensionType where
  N := CyclicGroup 4 × CyclicGroup 2
  n := 2
  act := c2OnK8Psi6 (Multiplicative.ofAdd 1)
  glue := (1, 1)
  map_glue := by decide
  pow_n := by ext y <;> (revert y; decide)

noncomputable def realise_16_13 :
    RealiseExtType ((CyclicGroup 4 × CyclicGroup 2) ⋊[c2OnK8Psi6] CyclicGroup 2) ext_16_13 :=
  let G : Type := (CyclicGroup 4 × CyclicGroup 2) ⋊[c2OnK8Psi6] CyclicGroup 2
  let a : G := ⟨1, Multiplicative.ofAdd 1⟩
  let ι : CyclicGroup 4 × CyclicGroup 2 →* G := SemidirectProduct.inl
  { a := a
    ι := ι
    act_a := by intro x; revert x; decide
    pow_a_n := by decide
    equiv := Equiv.ofBijective
      (fun p : (CyclicGroup 4 × CyclicGroup 2) × Fin 2 => ι p.1 * a ^ (p.2 : ℕ))
      (by decide)
    equiv_apply := fun _ _ => rfl }

end OrderSixteen
