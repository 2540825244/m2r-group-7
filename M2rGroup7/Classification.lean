import Mathlib.Logic.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Equiv.Basic
import «M2rGroup7».CpSqAction
import «M2rGroup7».SmallGroupsLibrary
import «M2rGroup7».PqCase
import «M2rGroup7».SixteenCase
import «M2rGroup7».P2qClassification.PqClassification
import «M2rGroup7».UT3
import «M2rGroup7».CaseA
import «M2rGroup7».CaseB
import «M2rGroup7».CaseC
import «M2rGroup7».OddCaseA
import «M2rGroup7».OddCaseB
import «M2rGroup7».OddCaseC
import «M2rGroup7».Order8Classification
import «M2rGroup7».TwentyFourCase
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Logic.Unique
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Fintype.Defs
import Mathlib.SetTheory.Cardinal.Defs
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.PNat.Prime
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.PGroup
import OrderPQ
import Mathlib.Algebra.Group.Defs

import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Data.Bracket
import Mathlib.Algebra.Group.TypeTags.Basic
import Paperproof
import Mathlib.SetTheory.Cardinal.Finite

open scoped commutatorElement

lemma AddSubgroup.closure_singleton_int_one_eq_top : closure ({1} : Set ℤ) = ⊤ := by
  ext
  simp only [Int.addSubgroupClosure_one, mem_top]

variable (n : ℕ) (G : Type*) [Group G]


theorem order_odd_prime_cubed_classification {p : ℕ} [hn : Fact p.Prime] (hp : p ≠ 2)
    (h : Nat.card G = p ^ 3) :
    (Nonempty (MulEquiv G (CyclicGroup (p^3)))) ∨
    (Nonempty (MulEquiv G (CyclicGroup (p^2) × CyclicGroup p))) ∨
    (Nonempty (MulEquiv G (CyclicGroup p × CyclicGroup p × CyclicGroup p))) ∨
    (Nonempty (MulEquiv G (UT3 p))) ∨
    (Nonempty (MulEquiv G (CyclicGroup (p^2) ⋊[cpSqAction p] CyclicGroup p))) := by
  rcases order_p_cubed_classification (G := G) h with
    h1 | h2 | h3 | ⟨h4, _⟩ | ⟨h4, _⟩ | ⟨_, h6⟩ | ⟨_, h7⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact absurd h4 hp
  · exact absurd h4 hp
  · exact Or.inr (Or.inr (Or.inr (Or.inl h6)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h7)))

macro "classify_prime_cubed_odd" p:num h:term : tactic => `(tactic|(
  haveI : Fact (Nat.Prime $p) := ⟨by decide⟩
  exact order_odd_prime_cubed_classification (by decide) ($h |>.trans (by norm_num))))

macro "classify_prime" p:num h:term : tactic => `(tactic|(
  have : Fact (Nat.Prime $p) := ⟨by decide⟩
  use 1
  haveI hv : ValidIndex $p 1 := by decide
  use hv
  exact prime_classification_of_group $h))

macro "classify_prime_sq" p:num h:term : tactic => `(tactic|(
  haveI : Fact (Nat.Prime $p) := ⟨by decide⟩
  obtain (hiso | hiso) := p_squared_classification (p := $p) ($h |>.trans (by decide))
  · exact ⟨1, by decide , hiso⟩
  · exact ⟨2, by decide, hiso⟩))

-- For n = p*q where BOTH cyclic and non-cyclic groups exist (p ∣ q - 1).
-- The non-cyclic SDP in `retrieve (p*q) 1` is built from the same
-- `canonicalCpOnCqAction`, so the bridge is `rfl` (proof irrelevance).
macro "classify_pq" p:num q:num h:term : tactic => `(tactic|(
  haveI : Fact (Nat.Prime $p) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime $q) := ⟨by norm_num⟩
  rcases pq_classification (p := $p) (q := $q) (by norm_num)
      (Eq.trans $h (by norm_num)) with ⟨⟨e⟩⟩ | ⟨hr, ⟨e⟩⟩
  · exact ⟨2, by decide, ⟨e⟩⟩
  · refine ⟨1, by decide, ⟨e.trans ?_⟩⟩
    exact MulEquiv.refl _))

-- For n = p*q where p ∤ q - 1, so only the cyclic group exists.
macro "classify_pq_cyclic" p:num q:num h:term : tactic => `(tactic|(
  haveI : Fact (Nat.Prime $p) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime $q) := ⟨by norm_num⟩
  have ⟨e⟩ : Nonempty (_ ≃* CyclicGroup ($p * $q)) :=
    (pq_classification (p := $p) (q := $q) (by norm_num) (Eq.trans $h (by norm_num))).resolve_right
      (fun ⟨hr, _⟩ => absurd hr (by native_decide))
  exact ⟨1, by decide, ⟨e⟩⟩))

theorem order12_classification {G : Type*} [Group G] (h : Nat.card G = 12) :
    Nonempty (G ≃* retrieve 12 1) ∨
    Nonempty (G ≃* retrieve 12 2) ∨
    Nonempty (G ≃* retrieve 12 3) ∨
    Nonempty (G ≃* retrieve 12 4) ∨
    Nonempty (G ≃* retrieve 12 5) := by
  rcases classification_4q (q := 3) (h_ge_3 := by norm_num)
      (h := h.trans (by norm_num)) with
    h1 | h2 | h3 | ⟨h1mod4, _⟩ | h5 | ⟨_, h6⟩ <;>
  · tauto

theorem order20_classification {G : Type*} [Group G] (h : Nat.card G = 20) :
    Nonempty (G ≃* retrieve 20 1) ∨
    Nonempty (G ≃* retrieve 20 2) ∨
    Nonempty (G ≃* retrieve 20 3) ∨
    Nonempty (G ≃* retrieve 20 4) ∨
    Nonempty (G ≃* retrieve 20 5) := by
  rcases classification_4q (q := 5) (h_ge_3 := by norm_num)
      (h := h.trans (by norm_num)) with
    h1 | h2 | h3 | ⟨_, h4⟩ | h5 | ⟨h5eq3, _⟩ <;>
  · tauto

theorem order18_classification {G : Type*} [Group G] (h : Nat.card G = 18) :
    Nonempty (G ≃* retrieve 18 1) ∨
    Nonempty (G ≃* retrieve 18 2) ∨
    Nonempty (G ≃* retrieve 18 3) ∨
    Nonempty (G ≃* retrieve 18 4) ∨
    Nonempty (G ≃* retrieve 18 5) := by
  rcases classification_2p2 (p := 3) (h_ge_3 := by norm_num)
      (h := h.trans (by norm_num)) with
    h1 | h2 | h3 | h4 | h5 <;>
  · tauto

private noncomputable def c3_c8_iso_c24 :
    CyclicGroup 3 × CyclicGroup 8 ≃* CyclicGroup 24 :=
  CyclicGroup.prodMulEquiv (by decide : Nat.Coprime 3 8)

private noncomputable def c3_c4c2_iso_c2c12 :
    CyclicGroup 3 × (CyclicGroup 4 × CyclicGroup 2) ≃* CyclicGroup 2 × CyclicGroup 12 :=
  (MulEquiv.prodAssoc (M := CyclicGroup 3) (N := CyclicGroup 4) (P := CyclicGroup 2)).symm.trans
    (((CyclicGroup.prodMulEquiv (by decide : Nat.Coprime 3 4)).prodCongr
        (MulEquiv.refl _)).trans
      (MulEquiv.prodComm (M := CyclicGroup 12) (N := CyclicGroup 2)))

theorem order28_classification {G : Type*} [Group G] (h : Nat.card G = 28) :
    Nonempty (G ≃* retrieve 28 1) ∨
    Nonempty (G ≃* retrieve 28 2) ∨
    Nonempty (G ≃* retrieve 28 3) ∨
    Nonempty (G ≃* retrieve 28 4) := by
  rcases classification_4q (q := 7) (h_ge_3 := by norm_num)
      (h := h.trans (by norm_num)) with
    h1 | h2 | h3 | ⟨h1mod4, _⟩ | h5 | ⟨h7eq3, _⟩ <;>
  · tauto

theorem order30_classification {G : Type*} [Group G] (h : Nat.card G = 30) :
    Nonempty (G ≃* retrieve 30 1) ∨
    Nonempty (G ≃* retrieve 30 2) ∨
    Nonempty (G ≃* retrieve 30 3) ∨
    Nonempty (G ≃* retrieve 30 4) := by
  rcases classification_30 h with h1 | h2 | h3 | h4 <;>
  · tauto

/-- A group of order at most `maximumOrder` is isomorphic to some group obtained by `retrieve`. -/
theorem classification [hpos : NeZero n] [hmax : Fact (n <= maximumOrder)] (h : Nat.card G = n) :
  ∃ i : Nat, ∃ hv : ValidIndex n i, Nonempty (MulEquiv G (retrieve n i))
 := by
  have h1 : n ≥ 1 := NeZero.pos n
  have h2 : n ≤ maximumOrder := hmax.out
  interval_cases n

  -- n = 1
  · use 1
    haveI hv : ValidIndex 1 1 := by decide
    use hv
    apply Nonempty.intro

    have : Unique (retrieve 1 1) := by
      have hr : retrieve 1 1 = Unit := by rfl
      rw [hr]
      infer_instance

    have hg := Nat.card_eq_one_iff_unique.mp h
    have h_nonempty := hg.right
    have : Subsingleton G := hg.left
    have : Inhabited G := Classical.inhabited_of_nonempty h_nonempty
    have h_unique := Unique.mk' G

    exact MulEquiv.ofUnique

  -- n = 2
  · classify_prime 2 h

  -- n = 3
  · classify_prime 3 h

  -- n = 4
  · classify_prime_sq 2 h

  -- n = 5
  · classify_prime 5 h

  -- n = 6 = 2 * 3
  · classify_pq 2 3 h

  -- n = 7
  · classify_prime 7 h

  -- n = 8
  · rcases order8_classification h with h1 | h2 | h3 | h4 | h5
    · exact ⟨1, by decide, h1⟩
    · exact ⟨2, by decide, h2⟩
    · exact ⟨5, by decide, h3⟩
    · exact ⟨3, by decide, h4⟩
    · exact ⟨4, by decide, h5⟩

  -- n = 9
  · classify_prime_sq 3 h

  -- n = 10 = 2 * 5
  · classify_pq 2 5 h

  -- n = 11
  · classify_prime 11 h

  -- n = 12
  · rcases order12_classification h with h1 | h2 | h3 | h4 | h5
    · exact ⟨1, by decide, h1⟩
    · exact ⟨2, by decide, h2⟩
    · exact ⟨3, by decide, h3⟩
    · exact ⟨4, by decide, h4⟩
    · exact ⟨5, by decide, h5⟩

  -- n = 13
  · classify_prime 13 h

  -- n = 14 = 2 * 7
  · classify_pq 2 7 h

  -- n = 15 = 3 * 5  (only cyclic: 3 ∤ 4)
  · classify_pq_cyclic 3 5 h

  -- n = 16
  · exact OrderSixteen.order_sixteen_retrieve h

  -- n = 17
  · classify_prime 17 h

  -- n = 18
  · rcases order18_classification h with h1 | h2 | h3 | h4 | h5
    · exact ⟨1, by decide, h1⟩
    · exact ⟨2, by decide, h2⟩
    · exact ⟨3, by decide, h3⟩
    · exact ⟨4, by decide, h4⟩
    · exact ⟨5, by decide, h5⟩

  -- n = 19
  · classify_prime 19 h

  -- n = 20
  · rcases order20_classification h with h1 | h2 | h3 | h4 | h5
    · exact ⟨1, by decide, h1⟩
    · exact ⟨2, by decide, h2⟩
    · exact ⟨3, by decide, h3⟩
    · exact ⟨4, by decide, h4⟩
    · exact ⟨5, by decide, h5⟩

  -- n = 21
  · classify_pq 3 7 h

  -- n = 22
  · classify_pq 2 11 h

  -- n = 23
  · classify_prime 23 h

  -- n = 24
  · rcases order24_classification h with
      h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
    · obtain ⟨e⟩ := h1
      exact ⟨2, by decide, ⟨e.trans c3_c8_iso_c24⟩⟩
    · obtain ⟨e⟩ := h2
      exact ⟨9, by decide, ⟨e.trans c3_c4c2_iso_c2c12⟩⟩
    · exact ⟨15, by decide, h3⟩
    · exact ⟨10, by decide, h4⟩
    · exact ⟨11, by decide, h5⟩
    · exact ⟨1, by decide, h6⟩
    · exact ⟨5, by decide, h7⟩
    · exact ⟨7, by decide, h8⟩
    · exact ⟨14, by decide, h9⟩
    · exact ⟨6, by decide, h10⟩
    · exact ⟨4, by decide, h11⟩
    · exact ⟨8, by decide, h12⟩
    · exact ⟨12, by decide, h13⟩
    · exact ⟨13, by decide, h14⟩
    · exact ⟨3, by decide, h15⟩

  -- n = 25
  · classify_prime_sq 5 h

  -- n = 26
  · classify_pq 2 13 h

  -- n = 27
  · sorry

  -- n = 28
  · rcases order28_classification h with h1 | h2 | h3 | h4
    · exact ⟨1, by decide, h1⟩
    · exact ⟨2, by decide, h2⟩
    · exact ⟨3, by decide, h3⟩
    · exact ⟨4, by decide, h4⟩

  -- n = 29
  · classify_prime 29 h

  -- n = 30
  · rcases order30_classification h with h1 | h2 | h3 | h4
    · exact ⟨1, by decide, h1⟩
    · exact ⟨2, by decide, h2⟩
    · exact ⟨3, by decide, h3⟩
    · exact ⟨4, by decide, h4⟩

  -- n = 31
  · classify_prime 31 h
