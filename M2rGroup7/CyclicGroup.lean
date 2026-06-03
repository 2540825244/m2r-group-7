import Mathlib
import OrderPQ

/-!
# CyclicGroup — minimal definitions extracted to break import cycles

`GroupTheoryLemmas` needs `CyclicGroup` and `card_cyclicGroup` but is imported by
`SmallGroupsLibrary` (transitively). Keeping these three definitions here lets both
`SmallGroupsLibrary` and `GroupTheoryLemmas` import this file without circularity,
so `SmallGroupsLibrary` can import `CycPGroupClassification` directly.
-/

/-- Cyclic group of order n. -/
def CyclicGroup (n : Nat) [NeZero n] := Multiplicative (ZMod n)
  deriving DecidableEq, Group, CommGroup, IsCyclic, Fintype, DivisionCommMonoid

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
