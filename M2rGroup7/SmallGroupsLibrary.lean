import Mathlib.Algebra.Group.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic
import Mathlib.RingTheory.ZMod.UnitsCyclic

abbrev maximumOrder : Nat := 17

/-- Cyclic group generator -/
def CyclicGroup (n : Nat) [NeZero n] := Multiplicative (ZMod n)
  deriving DecidableEq, Group, CommGroup, IsCyclic, Fintype, DivisionCommMonoid

/-- Alternating group generator -/
def AlternatingGroup (n : Nat) [NeZero n] := ↥(alternatingGroup (Fin n))
  deriving DecidableEq, Group, Fintype

theorem card_cyclicGroup (n : Nat) [NeZero n] : Nat.card (CyclicGroup n) = n := by
  delta CyclicGroup
  rw [Nat.card_congr Multiplicative.toAdd]
  exact Nat.card_zmod n

/-- Build a monoid hom out of `CyclicGroup n` from an element whose `n`th power is `1`. -/
def cyclicHom (n : Nat) [NeZero n] {G : Type*} [Group G] (a : G) (h : a ^ n = 1) :
    CyclicGroup n →* G :=
  AddMonoidHom.toMultiplicativeLeft <| ZMod.lift n
    ⟨zmultiplesHom (Additive G) (Additive.ofMul a), by
      change (n : ℤ) • Additive.ofMul a = 0
      rw [← ofMul_zpow, zpow_natCast, h, ofMul_one]⟩

instance {p : ℕ} [h : Fact p.Prime] {n : ℕ} : NeZero (p ^ n) := by
  have hp : Nat.Prime p := h.out
  exact ⟨(pow_pos hp.pos n).ne'⟩

instance {p : ℕ} [h : Fact p.Prime] : NeZero (p * (p - 1)) := by
  have hp : Nat.Prime p := h.out
  have h2 : 2 ≤ p := hp.two_le
  exact ⟨Nat.mul_ne_zero (by omega) (by omega)⟩

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

-- SemidirectProduct N ⋊[φ] G is structurally N × G, so Fintype and DecidableEq lift directly.
instance {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N} [Fintype N] [Fintype G] :
    Fintype (N ⋊[φ] G) :=
  Fintype.ofEquiv (N × G) {
    toFun   := fun p => ⟨p.1, p.2⟩
    invFun  := fun x => ⟨x.left, x.right⟩
    left_inv  := fun _ => rfl
    right_inv := fun _ => rfl
  }

instance {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N} [DecidableEq N] [DecidableEq G] :
    DecidableEq (N ⋊[φ] G) :=
  fun a b => decidable_of_iff (a.left = b.left ∧ a.right = b.right)
    ⟨fun ⟨hl, hr⟩ => SemidirectProduct.ext hl hr, fun h => ⟨congr_arg _ h, congr_arg _ h⟩⟩

instance : Group Unit where
  mul _ _ := ()
  mul_assoc _ _ _ := by rfl
  one := ()
  one_mul _ := by rfl
  mul_one _ := by rfl
  inv _ := ()
  inv_mul_cancel _ := by rfl

@[reducible]
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
  | 17, 1 => CyclicGroup 17
  | _, _ => PUnit -- Fallback to make retrieve total

@[reducible]
def num_entries (n : Nat) : Nat :=
  match n with
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 1
  | 6 => 2
  | 7 => 1
  | 8 => 5
  | 9 => 2
  | 10 => 2
  | 11 => 1
  | 12 => 5
  | 13 => 1
  | 14 => 2
  | 15 => 1
  | 16 => 14
  | 17 => 1
  | _ => 0

def validIndex (n i : Nat) : Bool :=
  decide (n > 0 ∧ n ≤ maximumOrder ∧ i > 0 ∧ i ≤ num_entries n)

class ValidIndex (n : Nat) (i : Nat) : Prop where
  n_pos : n > 0
  n_range : n ≤ maximumOrder
  i_pos : i > 0
  i_range : i ≤ num_entries n

instance (n i : Nat) : Decidable (ValidIndex n i) :=
  decidable_of_iff (validIndex n i = true) (by
    simp only [validIndex, decide_eq_true_eq]
    exact ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩,
           fun h => ⟨h.n_pos, h.n_range, h.i_pos, h.i_range⟩⟩)

instance (n : Nat) (i : Nat) [hv : ValidIndex n i] : Group (retrieve n i) := by
  unfold retrieve
  split <;> try infer_instance

theorem retrieve_card (n : Nat) (i : Nat) [hv : ValidIndex n i] : Nat.card (retrieve n i) = n := by
  obtain ⟨hn_pos, hn_range, hi_pos, hi_range⟩ := hv
  rw [maximumOrder] at hn_range
  interval_cases n <;>
    simp only [num_entries] at hi_range <;>
    interval_cases i <;>
      simp only [retrieve] <;>
      simp_all only [Fintype.card_prod, Fintype.card_unique, Nat.card_eq_fintype_card,
        Nat.ofNat_pos, Nat.one_le_ofNat, Nat.reduceLeDiff, Order.lt_one_iff, Order.lt_two_iff,
        Std.le_refl, gt_iff_lt, zero_le] <;>
      rfl
