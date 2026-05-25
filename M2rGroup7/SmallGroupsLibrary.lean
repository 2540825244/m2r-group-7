import Mathlib.Algebra.Group.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion

abbrev maximumOrder : Nat := 11

/- Cyclic group generator -/
def CyclicGroup (n : Nat) [NeZero n] := Multiplicative (ZMod n)
  deriving DecidableEq

instance (n : Nat) [NeZero n] : Group (CyclicGroup n) := by
  delta CyclicGroup
  infer_instance

instance (n : Nat) [NeZero n] : IsCyclic (CyclicGroup n) := by
  delta CyclicGroup
  exact isCyclic_multiplicative

instance (n : Nat) [NeZero n] : Fintype (CyclicGroup n) := by
  delta CyclicGroup
  exact Fintype.ofEquiv (ZMod n) Multiplicative.toAdd.symm

theorem card_cyclicGroup (n : Nat) [NeZero n] : Nat.card (CyclicGroup n) = n := by
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
  | 8, 4 => QuaternionGroup 2
  | 8, 5 => CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2
  | 9, 1 => CyclicGroup 9
  | 9, 2 => CyclicGroup 3 × CyclicGroup 3
  | 10, 1 => DihedralGroup 5
  | 10, 2 => CyclicGroup 10
  | 11, 1 => CyclicGroup 11
  | _, _ => Empty -- Fallback to make retrieve total

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
  | _ => 0

structure ValidIndex (n : Nat) (i : Nat) : Prop where
  n_pos : n > 0
  n_range : n <= maximumOrder
  i_pos : i > 0
  i_range : i <= num_entries n
  deriving DecidableEq

instance (n : Nat) (i : Nat) : Decidable (ValidIndex n i) :=
  decidable_of_iff (n > 0 ∧ n ≤ maximumOrder ∧ i > 0 ∧ i ≤ num_entries n)
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩,
      fun h => ⟨h.n_pos, h.n_range, h.i_pos, h.i_range⟩⟩

-- Tell compiler that groups we get are groups
-- @[reducible]
-- instance (n : Nat) (i : Nat) [hv : Fact (ValidIndex n i)] : Group (retrieve n i) := by
--   obtain ⟨hn_pos, hn_range, hi_pos, hi_range⟩ := hv
--   rw [maximumOrder] at hn_range
--   interval_cases n <;>
--     simp only [num_entries] at hi_range <;>
--     interval_cases i <;>
--       simp only [retrieve] <;>
--       infer_instance

instance (n : Nat) (i : Nat) [hv : Fact (ValidIndex n i)] : Group (retrieve n i) := by
  unfold retrieve
  split <;> first
    | infer_instance
    | (exfalso
       obtain ⟨hn_pos, hn_range, hi_pos, hi_range⟩ := hv
       simp only [num_entries, maximumOrder] at *
       split at hi_range <;> simp_all <;> omega)

theorem retrieve_card (n : Nat) (i : Nat) [hv : Fact (ValidIndex n i)] : Nat.card (retrieve n i) = n := by
  obtain ⟨hn_pos, hn_range, hi_pos, hi_range⟩ := hv
  rw [maximumOrder] at hn_range
  interval_cases n <;>
    simp only [num_entries] at hi_range <;>
    interval_cases i <;>
      simp only [retrieve] <;>
      simp only [Nat.card_eq_fintype_card, Fintype.card_unique] <;>
      decide
