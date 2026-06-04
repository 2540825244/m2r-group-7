import «M2rGroup7».SixteenClassification.Extensions

namespace OrderSixteen

/-- Universal equivalence between the index `Fin 2` and the quotient group `CyclicGroup 2`. -/
def fin2EquivC2 : Fin 2 ≃ CyclicGroup 2 where
  toFun i := match i with | ⟨0, _⟩ => 1 | ⟨1, _⟩ => Multiplicative.ofAdd 1
  invFun x := if x = 1 then 0 else 1
  left_inv i := by fin_cases i <;> rfl
  right_inv x := by revert x; decide

section OrderSixteenBlueprints

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
    `y = (1, gen_C2) ↦ y`. Concretely `(a, b) ↦ (a, b + a mod 2)` in additive ZMod form. -/
def psi5 : MulAut (CyclicGroup 4 × CyclicGroup 2) where
  toFun ab :=
    (ab.1,
     Multiplicative.ofAdd
       (Multiplicative.toAdd ab.2 + ((Multiplicative.toAdd ab.1).val : ZMod 2)))
  invFun ab :=
    (ab.1,
     Multiplicative.ofAdd
       (Multiplicative.toAdd ab.2 + ((Multiplicative.toAdd ab.1).val : ZMod 2)))
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

end OrderSixteenBlueprints

end OrderSixteen
