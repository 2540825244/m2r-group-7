/-
Blueprint: Conjugacy classes of subgroups of order q of GL_2(p)

This file is self-contained — it does not import any other file from the
M2rGroup7 project. All work for this blueprint lives in this single new
module so it is separate from the rest of the project.
-/

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.BigOperators

namespace ConjugacyClassesOrderQ

open scoped Pointwise
open Matrix

/-- Shorthand for `GL_2(F_p)`. -/
abbrev GLF (p : ℕ) [Fact p.Prime] : Type := GL (Fin 2) (ZMod p)

/-- Two subgroups `H K ≤ G` are *conjugate* in `G` iff some inner
automorphism of `G` carries `H` to `K`. -/
def Subgroup.IsConjGp {G : Type*} [Group G] (H K : Subgroup G) : Prop :=
  ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom

lemma Subgroup.IsConjGp.refl {G : Type*} [Group G] (H : Subgroup G) :
    Subgroup.IsConjGp H H := by
  refine ⟨1, ?_⟩
  ext x
  simp [Subgroup.mem_map]

lemma Subgroup.IsConjGp.symm {G : Type*} [Group G] {H K : Subgroup G}
    (h : Subgroup.IsConjGp H K) : Subgroup.IsConjGp K H := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨g⁻¹, ?_⟩
  ext x
  constructor
  · intro hx
    refine ⟨g * x * g⁻¹, ⟨x, hx, ?_⟩, ?_⟩ <;> simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hz

lemma Subgroup.IsConjGp.trans {G : Type*} [Group G] {H K L : Subgroup G}
    (h₁ : Subgroup.IsConjGp H K) (h₂ : Subgroup.IsConjGp K L) :
    Subgroup.IsConjGp H L := by
  obtain ⟨g, rfl⟩ := h₁
  obtain ⟨g', rfl⟩ := h₂
  refine ⟨g' * g, ?_⟩
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨z, hz, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(MulAut.conj g) y, ⟨y, hy, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

/-- The equivalence relation "conjugate in `G`" on subgroups of `G`. -/
def subgroupConjSetoid (G : Type*) [Group G] : Setoid (Subgroup G) where
  r := Subgroup.IsConjGp
  iseqv := ⟨Subgroup.IsConjGp.refl, Subgroup.IsConjGp.symm, Subgroup.IsConjGp.trans⟩

/-- The set of subgroups of `G` of order `n`. -/
def subgroupsOfOrder (G : Type*) [Group G] (n : ℕ) : Set (Subgroup G) :=
  {H : Subgroup G | Nat.card H = n}

/-- The number of conjugacy classes of subgroups of order `n` in `G`.

This is the cardinality of the orbit set of the conjugation action of `G`
on the set of subgroups of order `n`, viewed as a subtype. -/
noncomputable def numConjClassesOfOrder (G : Type*) [Group G] (n : ℕ) : ℕ :=
  Nat.card (Quotient
    ((subgroupConjSetoid G).comap (fun H : subgroupsOfOrder G n => (H : Subgroup G))))

/-! ### Helper lemmas. -/

/-- The order of `GL_2(F_p)` equals `(p^2 - 1) * (p^2 - p)`. -/
lemma card_GL_two (p : ℕ) [Fact p.Prime] :
    Nat.card (GLF p) = (p ^ 2 - 1) * (p ^ 2 - p) := by
  classical
  have h := Matrix.card_GL_field (𝔽 := ZMod p) (n := 2)
  rw [ZMod.card] at h
  rw [h, Fin.prod_univ_two]
  simp

/-- An element of order `q ≠ p` in `GL_2(F_p)` forces `q ∣ (p-1)(p+1)`. -/
lemma order_q_divides_p2_sub_one (p q : ℕ) [hp : Fact p.Prime] (hq : q.Prime)
    (hpq : p ≠ q) (M : GLF p) (hM : orderOf M = q) :
    q ∣ (p - 1) * (p + 1) := by
  have hdvd : q ∣ Nat.card (GLF p) := hM ▸ orderOf_dvd_natCard M
  rw [card_GL_two] at hdvd
  -- (p^2-1)(p^2-p) = (p-1)(p+1) * p*(p-1)
  have h1 : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    have := Nat.sq_sub_sq p 1
    rw [one_pow] at this
    rw [this, mul_comm]
  have h2 : p ^ 2 - p = p * (p - 1) := by
    rw [Nat.mul_sub_one, pow_two]
  rw [h1, h2] at hdvd
  -- q prime, q ∣ ((p-1)*(p+1)) * (p * (p-1)). Use q ∤ p.
  have hqnep : q ≠ p := fun h => hpq h.symm
  have hq_ndvd_p : ¬ q ∣ p := by
    intro h
    exact hqnep ((Nat.prime_dvd_prime_iff_eq hq hp.out).mp h)
  rcases (hq.dvd_mul.mp hdvd) with h | h
  · exact h
  · -- q ∣ p * (p - 1) ⟹ q ∣ p ∨ q ∣ (p - 1)
    rcases (hq.dvd_mul.mp h) with h' | h'
    · exact (hq_ndvd_p h').elim
    · -- q ∣ (p - 1) ⟹ q ∣ (p-1)*(p+1)
      exact h'.mul_right _

/-- If a prime `q ≠ p` divides neither `p - 1` nor `p + 1`, then
`GL_2(F_p)` has no element of order `q`. -/
lemma no_element_of_order_q (p q : ℕ) [Fact p.Prime] (hq : q.Prime)
    (hpq : p ≠ q) (h1 : ¬ q ∣ (p - 1)) (h2 : ¬ q ∣ (p + 1)) :
    ∀ M : GLF p, orderOf M ≠ q := by
  intro M hM
  have h := order_q_divides_p2_sub_one p q hq hpq M hM
  rcases hq.dvd_mul.mp h with h' | h'
  · exact h1 h'
  · exact h2 h'

/-- If `q ∤ (p-1)` and `q ∤ (p+1)` then there are no subgroups of order `q`
in `GL_2(F_p)`. -/
lemma no_subgroup_of_order_q (p q : ℕ) [Fact p.Prime] (hq : q.Prime)
    (hpq : p ≠ q) (h1 : ¬ q ∣ (p - 1)) (h2 : ¬ q ∣ (p + 1)) :
    subgroupsOfOrder (GLF p) q = ∅ := by
  ext H
  simp only [subgroupsOfOrder, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hH
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fintype H := Fintype.ofFinite H
  have hfincard : Fintype.card H = q := by rw [← Nat.card_eq_fintype_card]; exact hH
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := H) q (hfincard ▸ dvd_refl q)
  -- Lift x to an element of GLF p with the same order via the subtype monoid hom
  have hxG : orderOf ((x : H) : GLF p) = q := by
    have h := orderOf_injective H.subtype Subtype.val_injective x
    exact h.trans hx
  exact no_element_of_order_q p q hq hpq h1 h2 ((x : H) : GLF p) hxG

/-! ### Case analysis. -/

/-- Case `q ∣ p+1`: there is exactly one conjugacy class of subgroups
of order `q` in `GL_2(F_p)`. -/
lemma case_q_dvd_p_plus_one (p q : ℕ) [Fact p.Prime] (hq : q.Prime)
    (hq2 : 2 < q) (hpq : p ≠ q) (hdvd : q ∣ (p + 1)) :
    numConjClassesOfOrder (GLF p) q = 1 := by
  sorry

/-- Case `q ∣ p-1`: there are exactly `(q+3)/2` conjugacy classes of
subgroups of order `q` in `GL_2(F_p)`. -/
lemma case_q_dvd_p_minus_one (p q : ℕ) [Fact p.Prime] (hq : q.Prime)
    (hq2 : 2 < q) (hpq : p ≠ q) (hdvd : q ∣ (p - 1)) :
    numConjClassesOfOrder (GLF p) q = (q + 3) / 2 := by
  sorry

/-! ### Main theorem. -/

/-- When there are no subgroups of order `n` in `G`, the count of conjugacy
classes of such subgroups is zero. -/
lemma numConjClassesOfOrder_of_empty (G : Type*) [Group G] (n : ℕ)
    (h : subgroupsOfOrder G n = ∅) : numConjClassesOfOrder G n = 0 := by
  unfold numConjClassesOfOrder
  haveI : IsEmpty (subgroupsOfOrder G n) := by
    rw [h]
    exact Set.isEmpty_coe_sort.mpr rfl
  have hempty : IsEmpty (Quotient
      ((subgroupConjSetoid G).comap (fun H : subgroupsOfOrder G n => (H : Subgroup G)))) := by
    refine ⟨fun q => ?_⟩
    induction q using Quot.ind with
    | mk x => exact this.false x
  rw [Nat.card_eq_zero]
  exact Or.inl hempty

/-- Distinct primes `p`, `q` with `q > 2` cannot have `q` dividing both
`p - 1` and `p + 1`. -/
lemma not_both_divide (p q : ℕ) [hp : Fact p.Prime] (hq2 : 2 < q) :
    ¬ (q ∣ (p - 1) ∧ q ∣ (p + 1)) := by
  rintro ⟨h1, h2⟩
  have hp2 : 2 ≤ p := hp.out.two_le
  have hdiff : (p + 1) - (p - 1) = 2 := by omega
  have hq2dvd : q ∣ 2 := by
    rw [← hdiff]
    exact Nat.dvd_sub h2 h1
  have : q ≤ 2 := Nat.le_of_dvd (by norm_num) hq2dvd
  omega

/-- **Main theorem.** Let `p` and `q` be distinct primes with `q > 2`. The
number of conjugacy classes of subgroups of order `q` in `GL_2(F_p)` is

  `(if q ∣ p-1 then (q+3)/2 else 0) + (if q ∣ p+1 then 1 else 0)`.

This encodes the two cases of the informal proof: when `q ∣ p-1` there
are `(q+3)/2` classes, when `q ∣ p+1` there is one class, and otherwise
there are none. Distinct primes `p ≠ q` with `q > 2` cannot have `q`
divide both `p-1` and `p+1`. -/
theorem conjClasses_order_q_GL_two
    (p q : ℕ) [Fact p.Prime] (hq : q.Prime) (hq2 : 2 < q) (hpq : p ≠ q) :
    numConjClassesOfOrder (GLF p) q =
      (if q ∣ (p - 1) then (q + 3) / 2 else 0)
        + (if q ∣ (p + 1) then 1 else 0) := by
  by_cases hm : q ∣ (p - 1)
  · -- Case q ∣ p-1. Then q ∤ p+1 (else q ∣ 2, but q > 2).
    have hnp : ¬ q ∣ (p + 1) := fun h => not_both_divide p q hq2 ⟨hm, h⟩
    rw [case_q_dvd_p_minus_one p q hq hq2 hpq hm]
    simp [hm, hnp]
  · by_cases hp1 : q ∣ (p + 1)
    · -- Case q ∣ p+1, q ∤ p-1.
      rw [case_q_dvd_p_plus_one p q hq hq2 hpq hp1]
      simp [hm, hp1]
    · -- Neither.
      rw [numConjClassesOfOrder_of_empty _ q
        (no_subgroup_of_order_q p q hq hpq hm hp1)]
      simp [hm, hp1]

end ConjugacyClassesOrderQ
