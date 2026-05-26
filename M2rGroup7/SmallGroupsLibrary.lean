import Mathlib.Algebra.Group.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion


/- Cyclic group generator -/
def CyclicGroup (n : Nat) := Multiplicative (ZMod n)

instance (n : Nat) : Group (CyclicGroup n) := by
  delta CyclicGroup
  infer_instance

instance (n : Nat) : CommGroup (CyclicGroup n) := by
  delta CyclicGroup
  infer_instance

instance (n : Nat) : IsCyclic (CyclicGroup n) := by
  delta CyclicGroup
  exact isCyclic_multiplicative

theorem card_cyclicGroup (n : Nat) : Nat.card (CyclicGroup n) = n := by
  -- 1. Unfold your type synonym definition
  delta CyclicGroup

  -- 2. Strip away the 'Multiplicative' tag (Nat.card is invariant under type tags)
  rw [Nat.card_congr Multiplicative.toAdd]


  -- 3. Use Mathlib's built-in theorem for the Nat.card of ZMod n
  exact Nat.card_zmod n

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
  | 8, 4 => QuaternionGroup 8
  | 8, 5 => CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2
  | 9, 1 => CyclicGroup 9
  | 9, 2 => CyclicGroup 3 × CyclicGroup 3
  | 10, 1 => DihedralGroup 5
  | 10, 2 => CyclicGroup 10
  | 11, 1 => CyclicGroup 11
  | _, _ => CyclicGroup n -- Fallback to make retrieve total

-- Tell compiler that groups we get are groups
instance (o : Nat) (i : Nat) : Group (retrieve o i) := by
  unfold retrieve
  split <;> try infer_instance
