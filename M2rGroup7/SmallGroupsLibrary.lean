import Mathlib.Algebra.Group.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.OrderOfElement


/- Cyclic group generator -/
def CyclicGroup (n : Nat) := Multiplicative (ZMod n)

instance (n : Nat) : Group (CyclicGroup n) := by
  delta CyclicGroup
  infer_instance

/- Alternating group generator -/
def AlternatingGroup (n : Nat) := ↥(alternatingGroup (Fin n))

instance (n : Nat) : Group (AlternatingGroup n) := by
  delta AlternatingGroup
  infer_instance

instance (n : Nat) : CommGroup (CyclicGroup n) := by
  delta CyclicGroup
  infer_instance

instance (n : Nat) : IsCyclic (CyclicGroup n) := by
  delta CyclicGroup
  exact isCyclic_multiplicative

instance (n : Nat) : DecidableEq (CyclicGroup n) := by
  delta CyclicGroup
  infer_instance

instance (n : Nat) [NeZero n] : Fintype (CyclicGroup n) := by
  delta CyclicGroup
  infer_instance

theorem card_cyclicGroup (n : Nat) : Nat.card (CyclicGroup n) = n := by
  -- 1. Unfold your type synonym definition
  delta CyclicGroup

  -- 2. Strip away the 'Multiplicative' tag (Nat.card is invariant under type tags)
  rw [Nat.card_congr Multiplicative.toAdd]


  -- 3. Use Mathlib's built-in theorem for the Nat.card of ZMod n
  exact Nat.card_zmod n

/-- Build a monoid hom out of `CyclicGroup n` from an element whose `n`th power is `1`. -/
def cyclicHom (n : Nat) {G : Type*} [Group G] (a : G) (h : a ^ n = 1) :
    CyclicGroup n →* G :=
  AddMonoidHom.toMultiplicativeLeft <| ZMod.lift n
    ⟨zmultiplesHom (Additive G) (Additive.ofMul a), by
      change (n : ℤ) • Additive.ofMul a = 0
      rw [← ofMul_zpow, zpow_natCast, h, ofMul_one]⟩

/-- The non-trivial swap action of `C_4` on `C_2 × C_2`, factoring through `C_4/C_2 = C_2`. -/
def c4OnC2sqSwap : CyclicGroup 4 →* MulAut (CyclicGroup 2 × CyclicGroup 2) :=
  let swap : MulAut (CyclicGroup 2 × CyclicGroup 2) := MulEquiv.prodComm
  cyclicHom 4 swap (by
    have h2 : swap ^ 2 = 1 := by ext ⟨a, b⟩ <;> rfl
    change swap ^ 4 = 1
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, one_pow])

/-- The non-trivial action of `C_4` on `C_4` by inversion, factoring through `C_4/C_2 = C_2`. -/
def c4OnC4Inv : CyclicGroup 4 →* MulAut (CyclicGroup 4) :=
  let inv : MulAut (CyclicGroup 4) := MulEquiv.inv (CyclicGroup 4)
  cyclicHom 4 inv (by
    have h2 : inv ^ 2 = 1 := by
      ext x
      change (x⁻¹)⁻¹ = x
      exact inv_inv x
    change inv ^ (2 * 2) = 1
    rw [pow_mul, h2, one_pow])

/-- The non-trivial action of `C_2` on `C_8` by `x ↦ x^5`. -/
def c2OnC8Pow5 : CyclicGroup 2 →* MulAut (CyclicGroup 8) :=
  have h25 : ∀ x : CyclicGroup 8, (x ^ 5) ^ 5 = x := by decide
  let pow5 : MulAut (CyclicGroup 8) :=
    { toFun := (· ^ 5)
      invFun := (· ^ 5)
      left_inv := h25
      right_inv := h25
      map_mul' := fun a b => mul_pow a b 5 }
  cyclicHom 2 pow5 (by
    ext x
    change (x ^ 5) ^ 5 = x
    exact h25 x)

/-- The non-trivial action of `C_2` on `C_8` by `x ↦ x^3`. -/
def c2OnC8Pow3 : CyclicGroup 2 →* MulAut (CyclicGroup 8) :=
  have h9 : ∀ x : CyclicGroup 8, (x ^ 3) ^ 3 = x := by decide
  let pow3 : MulAut (CyclicGroup 8) :=
    { toFun := (· ^ 3)
      invFun := (· ^ 3)
      left_inv := h9
      right_inv := h9
      map_mul' := fun a b => mul_pow a b 3 }
  cyclicHom 2 pow3 (by
    ext x
    change (x ^ 3) ^ 3 = x
    exact h9 x)

/-- The unique element of order 2 in `CyclicGroup 4`. -/
def c4Half : CyclicGroup 4 := Multiplicative.ofAdd (2 : ZMod 4)

/-- The order-2 automorphism of `K_8 = C_4 × C_2` sending `x ↦ x^3` and `y ↦ x²y`, where
`x` generates `C_4` and `y` generates `C_2`. On pairs: `(a, b) ↦ (a^3 · c4Half^b, b)`. -/
def psi6 : MulAut (CyclicGroup 4 × CyclicGroup 2) where
  toFun ab := (ab.1 ^ 3 * c4Half ^ (Multiplicative.toAdd ab.2).val, ab.2)
  invFun ab := (ab.1 ^ 3 * c4Half ^ (Multiplicative.toAdd ab.2).val, ab.2)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

/-- The action of `C_2` on `K_8 = C_4 × C_2` via the `psi6` automorphism. -/
def c2OnK8Psi6 : CyclicGroup 2 →* MulAut (CyclicGroup 4 × CyclicGroup 2) :=
  cyclicHom 2 psi6 (by
    rw [pow_two]
    apply MulEquiv.ext
    intro x
    exact psi6.left_inv x)

instance : Group Unit where
  mul _ _ := ()
  mul_assoc _ _ _ := by rfl
  one := ()
  one_mul _ := by rfl
  mul_one _ := by rfl
  inv _ := ()
  inv_mul_cancel _ := by rfl

def retrieve (n : Nat) (i : Nat) : Type :=
  match n, i with
  | 1, 1 => Unit
  | 2, 1 => CyclicGroup 2
  | 3, 1 => CyclicGroup 3
  | 4, 1 => CyclicGroup 4
  | 4, 2 => CyclicGroup 2 × CyclicGroup 2
  | 5, 1 => CyclicGroup 5
  | 6, 1 => DihedralGroup 3
  | 6, 2 => CyclicGroup 6
  | 7, 1 => CyclicGroup 7
  | 8, 1 => CyclicGroup 8
  | 8, 2 => CyclicGroup 4 × CyclicGroup 2
  | 8, 3 => DihedralGroup 4
  | 8, 4 => QuaternionGroup 2
  | 8, 5 => CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2
  | 9, 1 => CyclicGroup 9
  | 9, 2 => CyclicGroup 3 × CyclicGroup 3
  | 10, 1 => DihedralGroup 5
  | 10, 2 => CyclicGroup 10
  | 11, 1 => CyclicGroup 11
  | 12, 1 => QuaternionGroup 3
  | 12, 2 => CyclicGroup 12
  | 12, 3 => AlternatingGroup 4
  | 12, 4 => DihedralGroup 6
  | 12, 5 => CyclicGroup 6 × CyclicGroup 2
  | 13, 1 => CyclicGroup 13
  | 14, 1 => DihedralGroup 7
  | 14, 2 => CyclicGroup 14
  | 15, 1 => CyclicGroup 15
  | 16, 1 => CyclicGroup 16
  | 16, 2 => CyclicGroup 4 × CyclicGroup 4
  | 16, 3 => (CyclicGroup 2 × CyclicGroup 2) ⋊[c4OnC2sqSwap] CyclicGroup 4
  | 16, 4 => CyclicGroup 4 ⋊[c4OnC4Inv] CyclicGroup 4
  | 16, 5 => CyclicGroup 8 × CyclicGroup 2
  | 16, 6 => CyclicGroup 8 ⋊[c2OnC8Pow5] CyclicGroup 2
  | 16, 7 => DihedralGroup 8
  | 16, 8 => CyclicGroup 8 ⋊[c2OnC8Pow3] CyclicGroup 2
  | 16, 9 => QuaternionGroup 4
  | 16, 10 => CyclicGroup 4 × CyclicGroup 2 × CyclicGroup 2
  | 16, 11 => CyclicGroup 2 × DihedralGroup 4
  | 16, 12 => CyclicGroup 2 × QuaternionGroup 2
  | 16, 13 => (CyclicGroup 4 × CyclicGroup 2) ⋊[c2OnK8Psi6] CyclicGroup 2
  | 16, 14 => CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2
  | _, _ => CyclicGroup n -- Fallback to make retrieve total

-- Tell compiler that groups we get are groups
instance (o : Nat) (i : Nat) : Group (retrieve o i) := by
  unfold retrieve
  split <;> try infer_instance
