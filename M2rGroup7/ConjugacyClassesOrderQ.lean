/-
Blueprint: Conjugacy classes of subgroups of order q of GL_2(p)

This file is self-contained — it does not import any other file from the
M2rGroup7 project. All work for this blueprint lives in this single new
module so it is separate from the rest of the project.
-/

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.BigOperators

-- NOTE: The library lemma
-- `M2rGroup7.Lemmas.GroupTheoryLemmas.cyclic_subgroup_of_cyclic_group_is_unique`
-- would normally be imported and used here to avoid duplication. However, the
-- project currently has two top-level declarations named `prime_classification`
-- (one in `M2rGroup7.Classification`, one in `M2rGroup7.Lemmas.GroupTheoryLemmas`),
-- so importing the latter triggers a name collision when the aggregator
-- `M2rGroup7.lean` is built. Until that collision is resolved (e.g. by
-- namespacing one of the two declarations), we keep a small local helper below.

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

/-- There is an injective group homomorphism `(GaloisField p 2)ˣ → GL 2 (ZMod p)`. -/
private lemma exists_inj_F_p2_to_GLF (p : ℕ) [Fact p.Prime] :
    ∃ (φ : (GaloisField p 2)ˣ →* GLF p), Function.Injective φ := by
  classical
  haveI : Module.Finite (ZMod p) (GaloisField p 2) :=
    Module.Finite.of_finite (R := ZMod p)
  haveI : Module.Free (ZMod p) (GaloisField p 2) := Module.Free.of_divisionRing _ _
  haveI : Fintype (GaloisField p 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p 2) = p ^ 2 := by
    have h2 : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by norm_num)
    rwa [Nat.card_eq_fintype_card] at h2
  have hp_card : Fintype.card (ZMod p) = p := ZMod.card p
  have hfinrank : Module.finrank (ZMod p) (GaloisField p 2) = 2 := by
    have h := Module.card_eq_pow_finrank (K := ZMod p) (V := GaloisField p 2)
    rw [hcard, hp_card] at h
    have hp_2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have heq := Nat.pow_right_injective hp_2 h
    omega
  let b : Module.Basis (Fin 2) (ZMod p) (GaloisField p 2) :=
    (Module.finBasis (ZMod p) (GaloisField p 2)).reindex (finCongr hfinrank)
  refine ⟨Units.map (Algebra.leftMulMatrix b).toRingHom.toMonoidHom, ?_⟩
  intro x y h
  apply Units.ext
  apply Algebra.leftMulMatrix_injective b
  exact congrArg (Units.val) h

/-- In `GL 2 (ZMod p)`, there exists a cyclic subgroup of order `p^2 - 1`. -/
private lemma exists_cyclic_subgroup_p2_sub_one (p : ℕ) [Fact p.Prime] :
    ∃ H : Subgroup (GLF p), IsCyclic H ∧ Nat.card H = p ^ 2 - 1 := by
  classical
  obtain ⟨φ, hφ⟩ := exists_inj_F_p2_to_GLF p
  refine ⟨φ.range, ?_, ?_⟩
  · -- Subgroup of units of integral domain is cyclic via subgroup_units_cyclic
    -- But we have it through (GaloisField p 2)ˣ.
    -- φ.range ≃ (GaloisField p 2)ˣ since φ is injective.
    -- and (GaloisField p 2)ˣ is cyclic by instIsCyclicUnitsOfFinite
    haveI : Fintype (GaloisField p 2) := Fintype.ofFinite _
    haveI : IsCyclic (GaloisField p 2)ˣ := inferInstance
    -- φ.range = MonoidHom.range φ; it's isomorphic to (GaloisField p 2)ˣ.
    -- Use isCyclic_of_surjective with the codomain corestriction.
    have hsurj : Function.Surjective (φ.rangeRestrict) :=
      MonoidHom.rangeRestrict_surjective φ
    exact isCyclic_of_surjective _ hsurj
  · -- card φ.range = card (GaloisField p 2)ˣ = p^2 - 1
    have hcard_GF : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by norm_num)
    have hcard_GFu : Nat.card (GaloisField p 2)ˣ = p ^ 2 - 1 := by
      rw [Nat.card_units, hcard_GF]
    -- Use that injective hom ⇒ card range = card domain
    have hrange : Nat.card φ.range = Nat.card (GaloisField p 2)ˣ := by
      symm
      apply Nat.card_eq_of_bijective φ.rangeRestrict
      refine ⟨?_, MonoidHom.rangeRestrict_surjective φ⟩
      intro x y h
      exact hφ (by simpa using congrArg Subtype.val h)
    rw [hrange, hcard_GFu]

/-- In a finite cyclic group, any two subgroups of the same order are equal.

This is a local re-statement of
`M2rGroup7.Lemmas.GroupTheoryLemmas.cyclic_subgroup_of_cyclic_group_is_unique`.
We keep a local copy because of a pre-existing name collision on
`prime_classification` between `M2rGroup7.Classification` and
`M2rGroup7.Lemmas.GroupTheoryLemmas` that blocks importing the latter from
this file. -/
private lemma unique_subgroup_of_card_in_cyclic
    {G : Type*} [Group G] [Finite G] [IsCyclic G] {n : ℕ} (hn : 0 < n)
    (H K : Subgroup G) (hH : Nat.card H = n) (hK : Nat.card K = n) : H = K := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype H := Fintype.ofFinite _
  haveI : Fintype K := Fintype.ofFinite _
  set S : Finset G := (Finset.univ : Finset G).filter (fun x => x ^ n = 1)
  have hcardS : S.card ≤ n := IsCyclic.card_pow_eq_one_le hn
  have hcardH : Fintype.card H = n := by rw [← Nat.card_eq_fintype_card]; exact hH
  have hcardK : Fintype.card K = n := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hxn (H' : Subgroup G) (hH' : Nat.card H' = n) {x : G} (hx : x ∈ H') :
      x ^ n = 1 := by
    have hpow : (⟨x, hx⟩ : H') ^ n = 1 := by
      rw [← hH']; exact pow_card_eq_one'
    have hpow2 : ((⟨x, hx⟩ : H')^ n : G) = ((1 : H') : G) := by exact_mod_cast hpow
    simpa using hpow2
  have hHsub : (H : Set G).toFinset ⊆ S := by
    intro x hx
    simp only [Set.mem_toFinset, SetLike.mem_coe] at hx
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hxn H hH hx
  have hKsub : (K : Set G).toFinset ⊆ S := by
    intro x hx
    simp only [Set.mem_toFinset, SetLike.mem_coe] at hx
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hxn K hK hx
  have hHcard : (H : Set G).toFinset.card = n := by
    rw [Set.toFinset_card]; convert hcardH using 1
  have hKcard : (K : Set G).toFinset.card = n := by
    rw [Set.toFinset_card]; convert hcardK using 1
  have hHeqS : (H : Set G).toFinset = S :=
    Finset.eq_of_subset_of_card_le hHsub (by rw [hHcard]; exact hcardS)
  have hKeqS : (K : Set G).toFinset = S :=
    Finset.eq_of_subset_of_card_le hKsub (by rw [hKcard]; exact hcardS)
  have hHK : (H : Set G).toFinset = (K : Set G).toFinset := hHeqS.trans hKeqS.symm
  ext x
  have : x ∈ (H : Set G).toFinset ↔ x ∈ (K : Set G).toFinset := by rw [hHK]
  simpa [Set.mem_toFinset] using this

/-- Two subgroups of `G` of the same order, both contained in a cyclic subgroup
`S`, are equal. -/
private lemma unique_subgroup_of_card_in_cyclic_le
    {G : Type*} [Group G] [Finite G] {S : Subgroup G} [IsCyclic S]
    {n : ℕ} (hn : 0 < n)
    {H K : Subgroup G} (hH : H ≤ S) (hK : K ≤ S)
    (hHcard : Nat.card H = n) (hKcard : Nat.card K = n) :
    H = K := by
  let H' : Subgroup S := H.subgroupOf S
  let K' : Subgroup S := K.subgroupOf S
  have hH'card : Nat.card H' = n := by
    have hHfin : Nat.card H = Nat.card H' := by
      apply Nat.card_eq_of_bijective
        (fun (x : H) => (⟨⟨x.1, hH x.2⟩, x.2⟩ : H'))
      refine ⟨fun x y hxy => Subtype.ext (by exact congrArg (·.1.1) hxy), ?_⟩
      rintro ⟨⟨y, _⟩, hy⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    rw [← hHfin]; exact hHcard
  have hK'card : Nat.card K' = n := by
    have hKfin : Nat.card K = Nat.card K' := by
      apply Nat.card_eq_of_bijective
        (fun (x : K) => (⟨⟨x.1, hK x.2⟩, x.2⟩ : K'))
      refine ⟨fun x y hxy => Subtype.ext (by exact congrArg (·.1.1) hxy), ?_⟩
      rintro ⟨⟨y, _⟩, hy⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    rw [← hKfin]; exact hKcard
  have hHK' : H' = K' :=
    unique_subgroup_of_card_in_cyclic hn H' K' hH'card hK'card
  apply le_antisymm
  · intro x hx
    have hx_in_H' : (⟨x, hH hx⟩ : S) ∈ H' := hx
    rw [hHK'] at hx_in_H'
    exact hx_in_H'
  · intro x hx
    have hx_in_K' : (⟨x, hK hx⟩ : S) ∈ K' := hx
    rw [← hHK'] at hx_in_K'
    exact hx_in_K'

/-- Case `q ∣ p+1`: there is exactly one conjugacy class of subgroups
of order `q` in `GL_2(F_p)`. -/
lemma case_q_dvd_p_plus_one (p q : ℕ) [Fact p.Prime] (hq : q.Prime)
    (hq2 : 2 < q) (hpq : p ≠ q) (hdvd : q ∣ (p + 1)) :
    numConjClassesOfOrder (GLF p) q = 1 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Finite (GLF p) := by
    haveI : Fintype (GLF p) := by
      unfold GLF
      infer_instance
    infer_instance
  -- q ∤ p-1
  have hp_two : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hndvd : ¬ q ∣ (p - 1) := by
    intro h
    -- (p+1) - (p-1) = 2 (since p ≥ 2), so q ∣ 2, contradicting q > 2.
    have hdiff : (p + 1) - (p - 1) = 2 := by omega
    have hq2dvd : q ∣ 2 := by rw [← hdiff]; exact Nat.dvd_sub hdvd h
    have : q ≤ 2 := Nat.le_of_dvd (by norm_num) hq2dvd
    omega
  -- Construct the cyclic subgroup C of order p^2 - 1
  obtain ⟨C, hCcyc, hCcard⟩ := exists_cyclic_subgroup_p2_sub_one p
  -- q ∣ p^2 - 1: q ∣ (p+1) | (p-1)(p+1) = p^2 - 1
  have hp_sq : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    have := Nat.sq_sub_sq p 1
    rw [one_pow] at this
    rw [this, mul_comm]
  have hq_dvd_p2 : q ∣ p ^ 2 - 1 := by
    rw [hp_sq]; exact hdvd.mul_left _
  -- In C, which is cyclic of order p^2-1, there's a subgroup H_0 of order q.
  haveI : IsCyclic C := hCcyc
  haveI : Finite C := by
    haveI : Fintype C := Fintype.ofFinite _
    infer_instance
  -- Use IsCyclic.exists_subgroup_of_card to get a subgroup of order q in C
  have hq_dvd_C : q ∣ Nat.card C := hCcard ▸ hq_dvd_p2
  -- Find an order-q subgroup of C as a subgroup of GLF p:
  -- C is cyclic, |C| divisible by q. Get a generator γ of C, then γ^(|C|/q) has order q.
  -- ⟨γ^(|C|/q)⟩ is the order-q subgroup.
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := C)
  -- orderOf γ = |C|
  haveI : Fintype C := Fintype.ofFinite _
  have hγ_order : orderOf γ = Nat.card C := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ]
  -- γ^(card C / q) has order q
  set k := Nat.card C / q
  have hCpos : 0 < Nat.card C := by
    rw [hCcard]
    have h1 : 4 ≤ p ^ 2 := by
      have : 2 * 2 ≤ p * p := Nat.mul_le_mul hp_two hp_two
      simpa [pow_two] using this
    omega
  have hk_mul : Nat.card C = k * q := (Nat.div_mul_cancel hq_dvd_C).symm
  have hγk_order : orderOf (γ ^ k) = q := by
    rw [orderOf_pow γ, hγ_order]
    rw [hk_mul]
    -- gcd (k*q) k = k
    have hgcd : Nat.gcd (k * q) k = k := by
      rw [Nat.gcd_comm, Nat.gcd_mul_right_right]
    rw [hgcd]
    -- (k*q) / k = q
    have hk_pos : 0 < k := by
      have hk_mul_pos : 0 < k * q := by rw [← hk_mul]; exact hCpos
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · rw [h0, Nat.zero_mul] at hk_mul_pos; omega
      · exact hpos
    exact Nat.mul_div_cancel_left q hk_pos
  -- H_0 = zpowers (γ ^ k) is a subgroup of C of order q
  let H₀ : Subgroup (GLF p) := Subgroup.zpowers ((γ ^ k : C) : GLF p)
  have hH₀_card : Nat.card H₀ = q := by
    change Nat.card (Subgroup.zpowers ((γ ^ k : C) : GLF p)) = q
    rw [Nat.card_zpowers]
    have h := orderOf_injective C.subtype Subtype.val_injective (γ ^ k)
    simp only [Subgroup.coe_subtype] at h
    rw [h]; exact hγk_order
  -- This gives the existence witness.
  -- Now uniqueness: every subgroup H of order q is conjugate to H₀.
  -- Step: prove every Sylow q-subgroup is cyclic.
  -- H₀ ≤ C (cyclic), so H₀ is in some Sylow q-subgroup of GLF p containing it.
  -- Actually, let's get a Sylow q-subgroup of GLF p containing H₀.
  -- Use IsPGroup.exists_le_sylow on H₀ (which is a q-group since |H₀| = q).
  have hH₀_p : IsPGroup q H₀ := IsPGroup.of_card (n := 1) (by rw [hH₀_card]; ring)
  -- Compute the q-factorization of |GLF p|.
  -- |GLF p| = (p^2-1)(p^2-p) = (p-1)(p+1)·p·(p-1).
  -- v_q = v_q(p-1)·2 + v_q(p) + v_q(p+1) = v_q(p+1) (since q ∤ p-1, q ≠ p).
  -- |C| = p^2-1 = (p-1)(p+1). v_q(|C|) = v_q(p+1) = v_q(|GLF p|).
  -- So the Sylow q-subgroup of C is also a Sylow q-subgroup of GLF p.
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hp_minus_one_pos : 0 < p - 1 := by omega
  have hp_plus_one_pos : 0 < p + 1 := by omega
  have hGLF_card : Nat.card (GLF p) = (p ^ 2 - 1) * (p ^ 2 - p) := card_GL_two p
  -- Setup: let k = v_q(p+1), claim factorizations match.
  set k := (p + 1).factorization q
  have hp_sub_p : p ^ 2 - p = p * (p - 1) := by
    rw [Nat.mul_sub_one, pow_two]
  have hC_sub : Nat.card C = (p - 1) * (p + 1) := by rw [hCcard]; exact hp_sq
  have hGLF_factored : Nat.card (GLF p) = ((p - 1) * (p + 1)) * (p * (p - 1)) := by
    rw [hGLF_card, hp_sq, hp_sub_p]
  -- factorization of |C| at q
  have hp_minus_one_ne : p - 1 ≠ 0 := by omega
  have hp_plus_one_ne : p + 1 ≠ 0 := by omega
  have hp_ne : p ≠ 0 := by omega
  have hq_ne_p : q ≠ p := fun h => hpq h.symm
  have hC_card_ne : Nat.card C ≠ 0 := by
    have h4 : 4 ≤ p ^ 2 := by
      have : 2 * 2 ≤ p * p := Nat.mul_le_mul hp_two hp_two
      simpa [pow_two] using this
    rw [hCcard]; omega
  have hC_factq : (Nat.card C).factorization q = k := by
    rw [hC_sub, Nat.factorization_mul hp_minus_one_ne hp_plus_one_ne]
    have h1 : (p - 1).factorization q = 0 := by
      rw [Nat.factorization_eq_zero_iff]; right; left; exact hndvd
    simp [h1, Finsupp.add_apply, k]
  have hGLF_factq : (Nat.card (GLF p)).factorization q = k := by
    rw [hGLF_factored]
    rw [Nat.factorization_mul (by exact Nat.mul_ne_zero hp_minus_one_ne hp_plus_one_ne)
        (by exact Nat.mul_ne_zero hp_ne hp_minus_one_ne)]
    rw [Nat.factorization_mul hp_minus_one_ne hp_plus_one_ne]
    rw [Nat.factorization_mul hp_ne hp_minus_one_ne]
    have h1 : (p - 1).factorization q = 0 := by
      rw [Nat.factorization_eq_zero_iff]; right; left; exact hndvd
    have h2 : p.factorization q = 0 := by
      rw [Nat.factorization_eq_zero_iff]; right; left
      intro h
      have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).mp h
      exact hq_ne_p hqp
    simp [h1, h2, Finsupp.add_apply, k]
  -- Now use Sylow.ofCard on a subgroup of GLF p with order q^k.
  -- Take the Sylow q-subgroup of C, which is cyclic of order q^k, and embed.
  let SC : Sylow q C := default
  have hSC_card : Nat.card SC = q ^ k := by
    have := SC.card_eq_multiplicity
    rw [← hC_factq]
    convert this using 1
  -- Map SC ≤ C as a subgroup of GLF p.
  let SC_GLF : Subgroup (GLF p) := (SC : Subgroup C).map C.subtype
  have hSC_GLF_card : Nat.card SC_GLF = q ^ k := by
    have hbij : Function.Bijective ((SC : Subgroup C).equivMapOfInjective
        C.subtype Subtype.val_injective) :=
      ((SC : Subgroup C).equivMapOfInjective C.subtype Subtype.val_injective).bijective
    have := Nat.card_eq_of_bijective _ hbij
    rw [← this, hSC_card]
  -- SC_GLF is a Sylow q-subgroup of GLF p
  let S₀ : Sylow q (GLF p) := Sylow.ofCard SC_GLF (by rw [hSC_GLF_card, hGLF_factq])
  -- S₀ is cyclic (as a subgroup of C, which is cyclic)
  haveI hS₀_cyc : IsCyclic S₀ := by
    have hSCcyc : IsCyclic SC := SC.toSubgroup.isCyclic
    -- SC_GLF ≃ SC as groups (via equivMapOfInjective)
    have hequiv := (SC : Subgroup C).equivMapOfInjective C.subtype Subtype.val_injective
    -- isCyclic transfers via MulEquiv
    have : IsCyclic SC_GLF := by
      have : IsCyclic (((SC : Subgroup C).map C.subtype) : Subgroup (GLF p)) :=
        isCyclic_of_surjective hequiv.toMonoidHom hequiv.surjective
      exact this
    exact this
  -- Now: every order-q subgroup is conjugate to a fixed one.
  -- The witness W_0: H₀ as a subgroup of GLF p, has order q, and is contained in S₀ (we hope).
  -- Actually H₀ ⊆ C and SC ≤ C. Is H₀ ≤ SC_GLF? Yes if the order-q sub of C is in SC.
  -- Since SC is the Sylow q-sub of C and H₀ ⊆ C has order q (a q-group), H₀ ≤ SC_GLF.

  -- Step 1: show H₀ ≤ SC_GLF.
  -- H₀ as subgroup of GLF p has its elements in C. Map them through... actually H₀ ⊆ C
  -- as Set, but H₀ is a Subgroup of GLF p, so this isn't trivial syntactically.
  -- Let's introduce H₀_in_C : Subgroup C.
  -- Actually simpler approach: Show every subgroup of order q is conjugate to H₀.
  -- Apply Nat.card_eq_one_iff_unique.
  rw [numConjClassesOfOrder, Nat.card_eq_one_iff_unique]
  refine ⟨?_, ?_⟩
  · -- Subsingleton: every H, K of order q have ⟦H⟧ = ⟦K⟧
    constructor
    intro a b
    induction a using Quotient.ind with | _ a =>
    induction b using Quotient.ind with | _ b =>
    apply Quotient.sound
    -- a, b : subgroupsOfOrder (GLF p) q
    -- need: Subgroup.IsConjGp a.1 b.1
    obtain ⟨a_sub, ha⟩ := a
    obtain ⟨b_sub, hb⟩ := b
    change Subgroup.IsConjGp a_sub b_sub
    -- ha : Nat.card a_sub = q, hb : Nat.card b_sub = q
    simp only [Set.mem_setOf_eq, subgroupsOfOrder] at ha hb
    -- Both are q-subgroups. Each contained in some Sylow q-subgroup. All Sylows conjugate.
    -- The unique order-q subgroup of S₀ is the canonical witness.
    have ha_p : IsPGroup q a_sub := IsPGroup.of_card (n := 1) (by rw [ha]; ring)
    have hb_p : IsPGroup q b_sub := IsPGroup.of_card (n := 1) (by rw [hb]; ring)
    obtain ⟨Pa, hPa⟩ := IsPGroup.exists_le_sylow ha_p
    obtain ⟨Pb, hPb⟩ := IsPGroup.exists_le_sylow hb_p
    -- Pa, Pb : Sylow q (GLF p)
    -- ∃ ga, ga • Pa = S₀
    obtain ⟨ga, hga⟩ := MulAction.exists_smul_eq (GLF p) Pa S₀
    obtain ⟨gb, hgb⟩ := MulAction.exists_smul_eq (GLF p) Pb S₀
    -- ga conjugates a_sub into S₀
    have hmap_eq (g : GLF p) (P : Sylow q (GLF p)) :
        (P : Subgroup (GLF p)).map (MulAut.conj g).toMonoidHom =
        (MulAut.conj g) • (P : Subgroup (GLF p)) := by
      rw [Subgroup.pointwise_smul_def]; rfl
    have hsmul_eq (g : GLF p) (P Q : Sylow q (GLF p)) (h : g • P = Q) :
        (P : Subgroup (GLF p)).map (MulAut.conj g).toMonoidHom =
        (Q : Subgroup (GLF p)) := by
      rw [hmap_eq]
      have h' : ((g • P : Sylow q (GLF p)) : Subgroup (GLF p)) =
                ((Q : Sylow q (GLF p)) : Subgroup (GLF p)) := by rw [h]
      rw [Sylow.coe_subgroup_smul] at h'
      exact h'
    have hga_a : a_sub.map (MulAut.conj ga).toMonoidHom ≤ (S₀ : Subgroup (GLF p)) := by
      have step1 : a_sub.map (MulAut.conj ga).toMonoidHom ≤
                   (Pa : Subgroup (GLF p)).map (MulAut.conj ga).toMonoidHom :=
        Subgroup.map_mono hPa
      rw [hsmul_eq ga Pa S₀ hga] at step1
      exact step1
    have hgb_b : b_sub.map (MulAut.conj gb).toMonoidHom ≤ (S₀ : Subgroup (GLF p)) := by
      have step1 : b_sub.map (MulAut.conj gb).toMonoidHom ≤
                   (Pb : Subgroup (GLF p)).map (MulAut.conj gb).toMonoidHom :=
        Subgroup.map_mono hPb
      rw [hsmul_eq gb Pb S₀ hgb] at step1
      exact step1
    -- Both ga•a and gb•b are order-q subgroups of S₀.
    -- a_sub mapped via conj ga is order q (conj preserves cardinality).
    have hcard_conj (g : GLF p) (H : Subgroup (GLF p)) (hH : Nat.card H = q) :
        Nat.card (H.map (MulAut.conj g).toMonoidHom) = q := by
      have hequiv : H ≃* H.map (MulAut.conj g).toMonoidHom :=
        Subgroup.equivMapOfInjective H _ (MulAut.conj g).injective
      have := Nat.card_eq_of_bijective hequiv hequiv.bijective
      omega
    have hcard_a : Nat.card (a_sub.map (MulAut.conj ga).toMonoidHom) = q :=
      hcard_conj ga a_sub ha
    have hcard_b : Nat.card (b_sub.map (MulAut.conj gb).toMonoidHom) = q :=
      hcard_conj gb b_sub hb
    -- The two mapped subgroups are equal because both are order-q subgroups of cyclic S₀.
    have heq : a_sub.map (MulAut.conj ga).toMonoidHom =
               b_sub.map (MulAut.conj gb).toMonoidHom := by
      apply unique_subgroup_of_card_in_cyclic_le (S := S₀) hq.pos
        hga_a hgb_b hcard_a hcard_b
    -- a_sub is conjugate to b_sub: gb⁻¹ * ga conjugates a_sub to b_sub.
    refine ⟨gb⁻¹ * ga, ?_⟩
    -- Need: b_sub = a_sub.map (MulAut.conj (gb⁻¹ * ga)).toMonoidHom
    -- From heq: a_sub.map (conj ga) = b_sub.map (conj gb)
    -- So b_sub = (a_sub.map (conj ga)).map (conj gb⁻¹) [apply gb⁻¹]
    -- But Subgroup.map is functorial: map (conj ga) ∘ map (conj gb⁻¹) = map (conj gb⁻¹ * ga)
    -- Wait, conj h(conj g x) = conj (h*g) x.
    -- Map composition: (map f) ∘ (map g) = map (f ∘ g).
    -- We want b_sub = a_sub.map (MulAut.conj (gb⁻¹ * ga)).
    have h1 : b_sub.map (MulAut.conj gb).toMonoidHom = a_sub.map (MulAut.conj ga).toMonoidHom :=
      heq.symm
    -- Apply MulAut.conj gb⁻¹ to both sides
    -- First: (S.map (conj gb)).map (conj gb⁻¹) = S
    have hb_inv : ∀ (T : Subgroup (GLF p)),
        (T.map (MulAut.conj gb).toMonoidHom).map (MulAut.conj gb⁻¹).toMonoidHom = T := by
      intro T
      rw [Subgroup.map_map]
      have hconj : ((MulAut.conj gb⁻¹).toMonoidHom).comp ((MulAut.conj gb).toMonoidHom) =
                   MonoidHom.id _ := by
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      rw [hconj]; exact Subgroup.map_id T
    have h2 := congrArg (·.map (MulAut.conj gb⁻¹).toMonoidHom) h1
    simp only at h2
    rw [hb_inv] at h2
    rw [h2]
    -- Now want a_sub.map (conj gb⁻¹) ∘ (conj ga) = a_sub.map (conj (gb⁻¹ * ga))
    -- i.e., (a_sub.map (conj ga)).map (conj gb⁻¹) = a_sub.map (conj (gb⁻¹ * ga))
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  · -- Nonempty
    refine ⟨Quotient.mk _ ⟨H₀, hH₀_card⟩⟩

/-! ### Helpers for the case `q ∣ p-1`. -/

/-- The diagonal vector `![u.1, v.1]` is invertible as a function. Helper. -/
private lemma diagonal_unit_mul_inv (p : ℕ) [Fact p.Prime] (u v : (ZMod p)ˣ) :
    (Matrix.diagonal ![(u : ZMod p), (v : ZMod p)] : Matrix (Fin 2) (Fin 2) (ZMod p)) *
      Matrix.diagonal ![((u⁻¹ : (ZMod p)ˣ) : ZMod p), ((v⁻¹ : (ZMod p)ˣ) : ZMod p)] = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  have huu : (u : ZMod p) * ((u⁻¹ : (ZMod p)ˣ) : ZMod p) = 1 := by
    rw [← Units.val_mul]; simp
  have hvv : (v : ZMod p) * ((v⁻¹ : (ZMod p)ˣ) : ZMod p) = 1 := by
    rw [← Units.val_mul]; simp
  have hfun : (fun i => (![(u : ZMod p), (v : ZMod p)] i) *
       (![((u⁻¹ : (ZMod p)ˣ) : ZMod p), ((v⁻¹ : (ZMod p)ˣ) : ZMod p)] i)) =
       (fun _ : Fin 2 => 1) := by
    funext i
    fin_cases i
    · exact huu
    · exact hvv
  rw [hfun]
  exact Matrix.diagonal_one

/-- Symmetric version. -/
private lemma diagonal_unit_inv_mul (p : ℕ) [Fact p.Prime] (u v : (ZMod p)ˣ) :
    (Matrix.diagonal ![((u⁻¹ : (ZMod p)ˣ) : ZMod p), ((v⁻¹ : (ZMod p)ˣ) : ZMod p)] :
      Matrix (Fin 2) (Fin 2) (ZMod p)) *
      Matrix.diagonal ![(u : ZMod p), (v : ZMod p)] = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  have huu : ((u⁻¹ : (ZMod p)ˣ) : ZMod p) * (u : ZMod p) = 1 := by
    rw [← Units.val_mul]; simp
  have hvv : ((v⁻¹ : (ZMod p)ˣ) : ZMod p) * (v : ZMod p) = 1 := by
    rw [← Units.val_mul]; simp
  have hfun : (fun i => (![((u⁻¹ : (ZMod p)ˣ) : ZMod p), ((v⁻¹ : (ZMod p)ˣ) : ZMod p)] i) *
       (![(u : ZMod p), (v : ZMod p)] i)) = (fun _ : Fin 2 => 1) := by
    funext i
    fin_cases i
    · exact huu
    · exact hvv
  rw [hfun]
  exact Matrix.diagonal_one

/-- The diagonal embedding `(ZMod p)ˣ × (ZMod p)ˣ → GLF p` sending `(u, v)`
to the diagonal matrix `diag(u, v)`. -/
private def diagEmbed (p : ℕ) [Fact p.Prime] :
    (ZMod p)ˣ × (ZMod p)ˣ →* GLF p where
  toFun := fun uv =>
    { val := Matrix.diagonal ![(uv.1 : ZMod p), (uv.2 : ZMod p)]
      inv := Matrix.diagonal ![((uv.1⁻¹ : (ZMod p)ˣ) : ZMod p),
                               ((uv.2⁻¹ : (ZMod p)ˣ) : ZMod p)]
      val_inv := diagonal_unit_mul_inv p uv.1 uv.2
      inv_val := diagonal_unit_inv_mul p uv.1 uv.2 }
  map_one' := by
    apply Units.ext
    show (Matrix.diagonal ![((1 : (ZMod p)ˣ) : ZMod p), ((1 : (ZMod p)ˣ) : ZMod p)] :
          Matrix (Fin 2) (Fin 2) (ZMod p)) = 1
    have h1 : (![((1 : (ZMod p)ˣ) : ZMod p), ((1 : (ZMod p)ˣ) : ZMod p)] : Fin 2 → ZMod p) =
              (fun _ => 1) := by
      funext i; fin_cases i <;> rfl
    rw [h1]
    exact Matrix.diagonal_one
  map_mul' x y := by
    apply Units.ext
    show (Matrix.diagonal ![((x.1 * y.1 : (ZMod p)ˣ) : ZMod p),
                            ((x.2 * y.2 : (ZMod p)ˣ) : ZMod p)] :
          Matrix (Fin 2) (Fin 2) (ZMod p)) =
         Matrix.diagonal ![(x.1 : ZMod p), (x.2 : ZMod p)] *
         Matrix.diagonal ![(y.1 : ZMod p), (y.2 : ZMod p)]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i
    · show ((x.1 * y.1 : (ZMod p)ˣ) : ZMod p) = (x.1 : ZMod p) * (y.1 : ZMod p)
      rw [Units.val_mul]
    · show ((x.2 * y.2 : (ZMod p)ˣ) : ZMod p) = (x.2 : ZMod p) * (y.2 : ZMod p)
      rw [Units.val_mul]

/-- The diagonal embedding is injective. -/
private lemma diagEmbed_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (diagEmbed p) := by
  intro x y h
  have h1 : (diagEmbed p x : Matrix (Fin 2) (Fin 2) (ZMod p)) =
            (diagEmbed p y : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    rw [h]
  have hdiag : (Matrix.diagonal ![(x.1 : ZMod p), (x.2 : ZMod p)] : Matrix (Fin 2) (Fin 2) (ZMod p)) =
               Matrix.diagonal ![(y.1 : ZMod p), (y.2 : ZMod p)] := h1
  have hvec : (![(x.1 : ZMod p), (x.2 : ZMod p)] : Fin 2 → ZMod p) =
              ![(y.1 : ZMod p), (y.2 : ZMod p)] :=
    Matrix.diagonal_injective hdiag
  have h00 : (x.1 : ZMod p) = (y.1 : ZMod p) := by
    have := congrFun hvec 0
    simpa using this
  have h11 : (x.2 : ZMod p) = (y.2 : ZMod p) := by
    have := congrFun hvec 1
    simpa using this
  refine Prod.ext (Units.ext ?_) (Units.ext ?_)
  · exact h00
  · exact h11

/-- The diagonal torus `D` is the image of `diagEmbed`. -/
private def torusD (p : ℕ) [Fact p.Prime] : Subgroup (GLF p) :=
  (diagEmbed p).range

/-- The 2x2 swap matrix `[[0,1],[1,0]]`. -/
private def swapMatM (p : ℕ) [Fact p.Prime] : Matrix (Fin 2) (Fin 2) (ZMod p) :=
  !![0, 1; 1, 0]

private lemma swapMatM_mul_self (p : ℕ) [Fact p.Prime] :
    swapMatM p * swapMatM p = 1 := by
  unfold swapMatM
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- The swap matrix as an element of `GLF p`. -/
private def swapMat (p : ℕ) [Fact p.Prime] : GLF p where
  val := swapMatM p
  inv := swapMatM p
  val_inv := swapMatM_mul_self p
  inv_val := swapMatM_mul_self p

private lemma swapMat_val (p : ℕ) [Fact p.Prime] :
    (swapMat p : Matrix (Fin 2) (Fin 2) (ZMod p)) = swapMatM p := rfl

private lemma swapMat_inv_eq (p : ℕ) [Fact p.Prime] :
    (swapMat p)⁻¹ = swapMat p := by
  apply Units.ext
  -- (swapMat p)⁻¹.val = (swapMat p).inv = swapMatM p
  rfl

/-- Conjugation by σ: σ · diag(u,v) · σ⁻¹ = diag(v,u). -/
private lemma swap_conj_diag (p : ℕ) [Fact p.Prime] (u v : (ZMod p)ˣ) :
    swapMat p * diagEmbed p (u, v) * (swapMat p)⁻¹ = diagEmbed p (v, u) := by
  apply Units.ext
  -- Compute on the matrix level.
  show (swapMatM p : Matrix (Fin 2) (Fin 2) (ZMod p)) *
       Matrix.diagonal ![(u : ZMod p), (v : ZMod p)] *
       ((swapMat p)⁻¹ : GLF p).val =
       Matrix.diagonal ![(v : ZMod p), (u : ZMod p)]
  rw [swapMat_inv_eq]
  show (swapMatM p : Matrix (Fin 2) (Fin 2) (ZMod p)) *
       Matrix.diagonal ![(u : ZMod p), (v : ZMod p)] *
       swapMatM p =
       Matrix.diagonal ![(v : ZMod p), (u : ZMod p)]
  -- Compute directly
  have h1 : (Matrix.diagonal ![(u : ZMod p), (v : ZMod p)] : Matrix (Fin 2) (Fin 2) (ZMod p)) =
            !![(u : ZMod p), 0; 0, (v : ZMod p)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  rw [h1]
  unfold swapMatM
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal,
            Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.head_cons]

/-- The cardinality of the diagonal torus `D` is `(p-1)^2`. -/
private lemma torusD_card (p : ℕ) [Fact p.Prime] :
    Nat.card (torusD p) = (p - 1) ^ 2 := by
  have h : Nat.card (torusD p) = Nat.card ((ZMod p)ˣ × (ZMod p)ˣ) := by
    unfold torusD
    symm
    -- range of injective hom has same cardinality as domain
    apply Nat.card_eq_of_bijective (diagEmbed p).rangeRestrict
    refine ⟨?_, MonoidHom.rangeRestrict_surjective _⟩
    intro x y hxy
    exact diagEmbed_injective p (by simpa using congrArg Subtype.val hxy)
  rw [h, Nat.card_prod, Nat.card_units]
  have : Nat.card (ZMod p) = p := Nat.card_zmod p
  rw [this]
  ring

/-- Pick an element of `(ZMod p)ˣ` of order `q`, given `q ∣ p - 1`. -/
private lemma exists_unit_order_q (p q : ℕ) [hp : Fact p.Prime] (hq : q.Prime)
    (hpq : p ≠ q) (hdvd : q ∣ (p - 1)) :
    ∃ a : (ZMod p)ˣ, orderOf a = q := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  -- (ZMod p)ˣ is cyclic of order p - 1
  haveI : IsCyclic (ZMod p)ˣ := inferInstance
  haveI : Fintype (ZMod p)ˣ := Fintype.ofFinite _
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units]; simp [Nat.card_zmod]
  have hq_dvd : q ∣ Fintype.card (ZMod p)ˣ := by
    rw [Fintype.card_eq_nat_card]; rw [hcard]; exact hdvd
  -- Use that in a finite cyclic group, for every divisor d of the order, there's an element of order d
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card (G := (ZMod p)ˣ) q hq_dvd
  exact ⟨a, ha⟩

/-- Helper: `diagEmbed p (a, b)` has order equal to `lcm (orderOf a) (orderOf b)`. -/
private lemma orderOf_diagEmbed (p : ℕ) [Fact p.Prime] (a b : (ZMod p)ˣ) :
    orderOf (diagEmbed p (a, b)) = Nat.lcm (orderOf a) (orderOf b) := by
  -- The diagonal map factors through ZMod p ˣ × ZMod p ˣ, and orderOf in a product
  -- equals lcm of orders. Then the injective hom preserves order.
  have h1 : orderOf (diagEmbed p (a, b)) = orderOf ((a, b) : (ZMod p)ˣ × (ZMod p)ˣ) :=
    orderOf_injective (diagEmbed p) (diagEmbed_injective p) (a, b)
  rw [h1, Prod.orderOf]

/-- For a unit a of order q (q prime), the order of `(a^i, a^j)` in `(ZMod p)ˣ × (ZMod p)ˣ`
is q unless both i and j are divisible by q (in which case it's 1). -/
private lemma orderOf_pair_unit_of_prime (a : (ZMod p)ˣ) (ha : orderOf a = q) (hq : q.Prime)
    (i j : ℕ) (h : ¬ (q ∣ i ∧ q ∣ j)) :
    orderOf ((a^i, a^j) : (ZMod p)ˣ × (ZMod p)ˣ) = q := by
  rw [Prod.orderOf]
  rw [orderOf_pow a, orderOf_pow a, ha]
  haveI : Fact q.Prime := ⟨hq⟩
  -- gcd(q, i) is 1 if q ∤ i, else q
  rcases em (q ∣ i) with hqi | hqi
  · rcases em (q ∣ j) with hqj | hqj
    · exact absurd ⟨hqi, hqj⟩ h
    · -- q ∣ i, q ∤ j
      have h1 : Nat.gcd q i = q := Nat.gcd_eq_left hqi
      have h2 : Nat.gcd q j = 1 := hq.coprime_iff_not_dvd.mpr hqj
      rw [h1, h2, Nat.div_self hq.pos, Nat.div_one]
      simp
  · -- q ∤ i
    have h1 : Nat.gcd q i = 1 := hq.coprime_iff_not_dvd.mpr hqi
    rw [h1, Nat.div_one]
    rcases em (q ∣ j) with hqj | hqj
    · have h2 : Nat.gcd q j = q := Nat.gcd_eq_left hqj
      rw [h2, Nat.div_self hq.pos]
      simp
    · have h2 : Nat.gcd q j = 1 := hq.coprime_iff_not_dvd.mpr hqj
      rw [h2, Nat.div_one]
      simp

/-- Helper: `(M * diag(u, v))(i, j) = M(i, j) * diag(u, v)(j, j)`. -/
private lemma mul_diag_entries (p : ℕ) [Fact p.Prime]
    (M : Matrix (Fin 2) (Fin 2) (ZMod p)) (u v : ZMod p) :
    M * Matrix.diagonal ![u, v] = !![M 0 0 * u, M 0 1 * v; M 1 0 * u, M 1 1 * v] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- Helper: `(diag(u, v) * M)(i, j) = diag(u, v)(i, i) * M(i, j)`. -/
private lemma diag_mul_entries (p : ℕ) [Fact p.Prime]
    (M : Matrix (Fin 2) (Fin 2) (ZMod p)) (u v : ZMod p) :
    Matrix.diagonal ![u, v] * M = !![u * M 0 0, u * M 0 1; v * M 1 0, v * M 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- A matrix M satisfies M*diag(u,v) = diag(u',v')*M iff entries pairwise constrained. -/
private lemma diag_mul_eq_iff (p : ℕ) [Fact p.Prime]
    (M : Matrix (Fin 2) (Fin 2) (ZMod p)) (u v u' v' : ZMod p) :
    M * Matrix.diagonal ![u, v] = Matrix.diagonal ![u', v'] * M ↔
    M 0 0 * u = u' * M 0 0 ∧ M 0 1 * v = u' * M 0 1 ∧
    M 1 0 * u = v' * M 1 0 ∧ M 1 1 * v = v' * M 1 1 := by
  rw [mul_diag_entries p M u v, diag_mul_entries p M u' v']
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := congrArg (· 0 0) h; simpa using this
    · have := congrArg (· 0 1) h; simpa using this
    · have := congrArg (· 1 0) h; simpa using this
    · have := congrArg (· 1 1) h; simpa using this
  · rintro ⟨h00, h01, h10, h11⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

/-- The diagonal embedding viewed as a matrix-level equation. -/
private lemma diagEmbed_val (p : ℕ) [Fact p.Prime] (u v : (ZMod p)ˣ) :
    (diagEmbed p (u, v) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
    Matrix.diagonal ![(u : ZMod p), (v : ZMod p)] := rfl

/-- A 2x2 matrix is determined by its entries. -/
private lemma mat_eq_of_entries (p : ℕ) [Fact p.Prime]
    (M N : Matrix (Fin 2) (Fin 2) (ZMod p))
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

/-- An invertible 2x2 matrix over `ZMod p`. If column 0 is `(0, 0)`, then det = 0,
contradicting invertibility. -/
private lemma not_both_zero_col0 (p : ℕ) [Fact p.Prime] (g : GLF p) :
    ¬ (g.val 0 0 = 0 ∧ g.val 1 0 = 0) := by
  rintro ⟨h0, h1⟩
  -- (inv * val)(0,0) = 1 but if first column of val is zero, this product entry is 0.
  have hinv : g.inv * g.val = 1 := g.inv_val
  have h00 : (g.inv * g.val) 0 0 = 1 := by rw [hinv]; simp [Matrix.one_apply]
  have h00' : (g.inv * g.val) 0 0 = 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, h0, h1]
  rw [h00'] at h00; exact one_ne_zero h00.symm

private lemma not_both_zero_col1 (p : ℕ) [Fact p.Prime] (g : GLF p) :
    ¬ (g.val 0 1 = 0 ∧ g.val 1 1 = 0) := by
  rintro ⟨h0, h1⟩
  have hinv : g.inv * g.val = 1 := g.inv_val
  have h11 : (g.inv * g.val) 1 1 = 1 := by rw [hinv]; simp [Matrix.one_apply]
  have h11' : (g.inv * g.val) 1 1 = 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, h0, h1]
  rw [h11'] at h11; exact one_ne_zero h11.symm

private lemma not_both_zero_row0 (p : ℕ) [Fact p.Prime] (g : GLF p) :
    ¬ (g.val 0 0 = 0 ∧ g.val 0 1 = 0) := by
  rintro ⟨h0, h1⟩
  have hinv : g.val * g.inv = 1 := g.val_inv
  have h00 : (g.val * g.inv) 0 0 = 1 := by rw [hinv]; simp [Matrix.one_apply]
  have h00' : (g.val * g.inv) 0 0 = 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, h0, h1]
  rw [h00'] at h00; exact one_ne_zero h00.symm

private lemma not_both_zero_row1 (p : ℕ) [Fact p.Prime] (g : GLF p) :
    ¬ (g.val 1 0 = 0 ∧ g.val 1 1 = 0) := by
  rintro ⟨h0, h1⟩
  have hinv : g.val * g.inv = 1 := g.val_inv
  have h11 : (g.val * g.inv) 1 1 = 1 := by rw [hinv]; simp [Matrix.one_apply]
  have h11' : (g.val * g.inv) 1 1 = 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, h0, h1]
  rw [h11'] at h11; exact one_ne_zero h11.symm

/-- The key 2x2 calculation: if `g` conjugates a non-scalar diagonal matrix to a diagonal
matrix, then `g` is itself diagonal or anti-diagonal. -/
private lemma conj_diag_to_diag_normalizes (p : ℕ) [Fact p.Prime]
    (g : GLF p) (u v u' v' : (ZMod p)ˣ) (huv : u ≠ v)
    (h : g * diagEmbed p (u, v) * g⁻¹ = diagEmbed p (u', v')) :
    g ∈ torusD p ∨ ∃ d : torusD p, g = (d : GLF p) * swapMat p := by
  -- Equation lifted to matrix level: g.val * diag(u,v) = diag(u',v') * g.val
  have hmat : (g : Matrix (Fin 2) (Fin 2) (ZMod p)) *
              Matrix.diagonal ![(u : ZMod p), (v : ZMod p)] =
              Matrix.diagonal ![(u' : ZMod p), (v' : ZMod p)] *
              (g : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    have heq : g * diagEmbed p (u, v) = diagEmbed p (u', v') * g := by
      have := congrArg (· * g) h
      simp [mul_assoc] at this
      exact this
    have h' : (g * diagEmbed p (u, v) : GLF p).val =
              (diagEmbed p (u', v') * g : GLF p).val :=
      congrArg Units.val heq
    -- The val of mul is matrix mul
    simpa [Units.val_mul, diagEmbed_val] using h'
  -- Get the four entry equations
  rw [diag_mul_eq_iff p _ ((u : ZMod p)) ((v : ZMod p)) ((u' : ZMod p)) ((v' : ZMod p))] at hmat
  obtain ⟨h00, h01, h10, h11⟩ := hmat
  -- u - v ≠ 0 in ZMod p (field)
  have huv_ne : (u : ZMod p) ≠ (v : ZMod p) := by
    intro hcontr
    apply huv
    exact Units.ext hcontr
  -- From h00: g 0 0 * u = u' * g 0 0 → g 0 0 * (u - u') = 0
  -- From h01: g 0 1 * v = u' * g 0 1 → g 0 1 * (v - u') = 0
  -- From h10: g 1 0 * u = v' * g 1 0 → g 1 0 * (u - v') = 0
  -- From h11: g 1 1 * v = v' * g 1 1 → g 1 1 * (v - v') = 0
  -- Case split: g 0 0 = 0 or g 0 0 ≠ 0 (gives u = u')
  have h00' : g.val 0 0 * ((u : ZMod p) - (u' : ZMod p)) = 0 := by linear_combination h00
  have h01' : g.val 0 1 * ((v : ZMod p) - (u' : ZMod p)) = 0 := by linear_combination h01
  have h10' : g.val 1 0 * ((u : ZMod p) - (v' : ZMod p)) = 0 := by linear_combination h10
  have h11' : g.val 1 1 * ((v : ZMod p) - (v' : ZMod p)) = 0 := by linear_combination h11
  -- Either col 0 has g 0 0 ≠ 0 or g 1 0 ≠ 0 (not both zero)
  -- Case: g 0 0 ≠ 0, hence u = u'. Then if g 1 0 ≠ 0, u = v'. Then u' = v'.
  --   The other column: not both g 0 1 and g 1 1 are zero.
  --   Case 1.1: g 0 1 ≠ 0, hence v = u' = u, contradicts u ≠ v.
  --   Case 1.2: g 0 1 = 0, so g 1 1 ≠ 0, hence v = v' = u' = u, contradicts u ≠ v.
  --   Either way: contradiction.
  --   So we must have g 1 0 = 0 (if g 0 0 ≠ 0). Then g is upper triangular.
  --   Now col 1: g 0 1 and g 1 1 not both zero. From h11: if g 1 1 ≠ 0, v = v'.
  --     Subcase: g 0 1 ≠ 0, v = u' = u, contradiction.
  --     Subcase: g 0 1 = 0, so g 1 1 ≠ 0, and g is diagonal. ✓
  -- Case: g 0 0 = 0, then g 1 0 ≠ 0, so u = v'. By symmetric argument, g 1 1 = 0.
  --   So g 0 1 ≠ 0, hence v = u'. So g is antidiagonal. ✓
  by_cases ha : g.val 0 0 = 0
  · -- a = 0 case → anti-diagonal
    have hc_ne : g.val 1 0 ≠ 0 := by
      intro hc
      exact not_both_zero_col0 p g ⟨ha, hc⟩
    have hv'_eq : (u : ZMod p) = (v' : ZMod p) := by
      have := mul_eq_zero.mp h10'
      rcases this with h | h
      · exact absurd h hc_ne
      · exact sub_eq_zero.mp h
    -- v' = u. So h11': g 1 1 * (v - u) = 0. Since v ≠ u, g 1 1 = 0.
    have hd_zero : g.val 1 1 = 0 := by
      have heq : g.val 1 1 * ((v : ZMod p) - (u : ZMod p)) = 0 := by
        rw [← hv'_eq] at h11'; exact h11'
      rcases mul_eq_zero.mp heq with h | h
      · exact h
      · exact absurd (sub_eq_zero.mp h) huv_ne.symm
    -- So g is anti-diagonal. g.val 0 1 ≠ 0 (col 1 nontrivial)
    have hb_ne : g.val 0 1 ≠ 0 := by
      intro hb
      exact not_both_zero_col1 p g ⟨hb, hd_zero⟩
    -- u' = v from h01': g 0 1 * (v - u') = 0, g 0 1 ≠ 0
    have hu'_eq : (v : ZMod p) = (u' : ZMod p) := by
      rcases mul_eq_zero.mp h01' with h | h
      · exact absurd h hb_ne
      · exact sub_eq_zero.mp h
    -- g = swap * diag(g.val 1 0, g.val 0 1)
    right
    -- d corresponds to diag(g.val 1 0, g.val 0 1). We need swap * diag(b, c) where b = g 0 1, c = g 1 0...
    -- Actually [0 b; c 0] = swap * [b 0; 0 c] · ?
    -- swap * [b 0; 0 c] = [0 c; b 0] -- not quite.
    -- Let's compute: d * swap where d = diag(d0, d1):
    -- diag(d0, d1) * [[0,1],[1,0]] = [[0, d0], [d1, 0]]
    -- So if g = [[0, b],[c, 0]] then g = diag(b, c) * swap with d0 = b = g 0 1, d1 = c = g 1 0.
    refine ⟨⟨diagEmbed p (Units.mk0 (g.val 0 1) hb_ne, Units.mk0 (g.val 1 0) hc_ne),
            MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩, ?_⟩
    apply Units.ext
    -- Need: g.val = (diag(g 0 1, g 1 0) * swap).val
    show (g : Matrix _ _ _) =
         (Matrix.diagonal ![g.val 0 1, g.val 1 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) *
         swapMatM p
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [swapMatM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, ha, hd_zero]
  · -- a ≠ 0 → diagonal case
    have hu'_eq : (u : ZMod p) = (u' : ZMod p) := by
      rcases mul_eq_zero.mp h00' with h | h
      · exact absurd h ha
      · exact sub_eq_zero.mp h
    -- Now h01': g.val 0 1 * (v - u') = g.val 0 1 * (v - u) = 0
    have hb_zero : g.val 0 1 = 0 := by
      have heq : g.val 0 1 * ((v : ZMod p) - (u : ZMod p)) = 0 := by
        rw [← hu'_eq] at h01'; exact h01'
      rcases mul_eq_zero.mp heq with h | h
      · exact h
      · exact absurd (sub_eq_zero.mp h) huv_ne.symm
    -- So g is lower triangular. Col 1 nontrivial: g 1 1 ≠ 0.
    have hd_ne : g.val 1 1 ≠ 0 := by
      intro hd
      exact not_both_zero_col1 p g ⟨hb_zero, hd⟩
    -- h11': g 1 1 * (v - v') = 0, g 1 1 ≠ 0, so v = v'.
    have hv'_eq : (v : ZMod p) = (v' : ZMod p) := by
      rcases mul_eq_zero.mp h11' with h | h
      · exact absurd h hd_ne
      · exact sub_eq_zero.mp h
    -- h10': g 1 0 * (u - v') = g 1 0 * (u - v) = 0. Since u ≠ v: g 1 0 = 0.
    have hc_zero : g.val 1 0 = 0 := by
      have heq : g.val 1 0 * ((u : ZMod p) - (v : ZMod p)) = 0 := by
        rw [← hv'_eq] at h10'; exact h10'
      rcases mul_eq_zero.mp heq with h | h
      · exact h
      · exact absurd (sub_eq_zero.mp h) huv_ne
    -- g is diagonal. g ∈ torusD.
    left
    -- g = diag(g 0 0, g 1 1). Need g ∈ range(diagEmbed)
    refine MonoidHom.mem_range.mpr
      ⟨(Units.mk0 (g.val 0 0) ha, Units.mk0 (g.val 1 1) hd_ne), ?_⟩
    apply Units.ext
    show (Matrix.diagonal ![g.val 0 0, g.val 1 1] : Matrix (Fin 2) (Fin 2) (ZMod p)) =
         (g : Matrix _ _ _)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, hb_zero, hc_zero]

/-- The torus is abelian: any two diagonal elements commute. -/
private instance torusD_commGroup (p : ℕ) [Fact p.Prime] : CommGroup (torusD p) where
  mul_comm := by
    rintro ⟨_, ⟨x, rfl⟩⟩ ⟨_, ⟨y, rfl⟩⟩
    apply Subtype.ext
    show diagEmbed p x * diagEmbed p y = diagEmbed p y * diagEmbed p x
    rw [← map_mul, ← map_mul]
    congr 1
    exact mul_comm x y

/-- Elements of the torus commute. -/
private lemma torusD_commute (p : ℕ) [Fact p.Prime] (g h : GLF p)
    (hg : g ∈ torusD p) (hh : h ∈ torusD p) : g * h = h * g := by
  rcases hg with ⟨x, rfl⟩
  rcases hh with ⟨y, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

/-- Conjugating a subgroup of `torusD` by a diagonal element fixes it. -/
private lemma conj_subgroup_torusD_by_diag (p : ℕ) [Fact p.Prime]
    {H : Subgroup (GLF p)} (hH : H ≤ torusD p) {d : GLF p} (hd : d ∈ torusD p) :
    H.map (MulAut.conj d).toMonoidHom = H := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyD : y ∈ torusD p := hH hy
    have hcomm : d * y = y * d := torusD_commute p d y hd hyD
    have heq : (MulAut.conj d) y = y := by
      change d * y * d⁻¹ = y
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [heq]; exact hy
  · intro hx
    refine ⟨x, hx, ?_⟩
    have hxD : x ∈ torusD p := hH hx
    have hcomm : d * x = x * d := torusD_commute p d x hd hxD
    change d * x * d⁻¹ = x
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

/-- If H ≤ D is a subgroup of order `q` (q prime ≥ 3, so q ≥ 2) and `g`
conjugates H to another subgroup H' ≤ D, then either H = H' or
H' = σ H σ⁻¹. (Uses `conj_diag_to_diag_normalizes`.) -/
private lemma conj_diag_subgroup_either_eq_or_swap (p : ℕ) [Fact p.Prime] (hq : q.Prime)
    (hq2 : 2 < q)
    {H H' : Subgroup (GLF p)} (hH : H ≤ torusD p) (hH' : H' ≤ torusD p)
    (hHcard : Nat.card H = q) (hH'card : Nat.card H' = q)
    {g : GLF p} (hconj : H' = H.map (MulAut.conj g).toMonoidHom) :
    H = H' ∨ H' = H.map (MulAut.conj (swapMat p)).toMonoidHom := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  -- Find a generator m of H with order q.
  haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hHcard]; exact hq.ne_zero)
  haveI : Fintype H := Fintype.ofFinite _
  obtain ⟨m₀, hm₀⟩ := exists_prime_orderOf_dvd_card (G := H) q
    (by rw [Fintype.card_eq_nat_card]; rw [hHcard])
  -- m₀ has order q in H, hence in GLF p.
  let m : GLF p := m₀
  have hm_order : orderOf m = q := by
    show orderOf (m₀ : GLF p) = q
    have := orderOf_injective H.subtype Subtype.val_injective m₀
    simp only [Subgroup.coe_subtype] at this
    rw [this]; exact hm₀
  -- m ∈ H ≤ D, so m is diagonal: m = diag(u, v).
  have hmD : m ∈ torusD p := hH m₀.property
  rcases hmD with ⟨⟨u, v⟩, hm_eq⟩
  -- u ≠ v: else m = diag(u, u) = u * I scalar, and orderOf (u*I) = orderOf u | q.
  -- If u = v, then m is a scalar matrix u * I.
  -- The order of m equals the order of u in (ZMod p)ˣ.
  -- orderOf m = lcm(orderOf u, orderOf v) = orderOf u (if u = v).
  -- This equals q (since orderOf m = q). But then m has order q, but m commutes
  -- with everything in GL, so H is in center. That's fine.
  -- Actually if u = v, then we still have m = diag(u, u) is a scalar. So
  -- H = ⟨m⟩ contained in center of GL_2. Conjugation by g fixes scalar matrices.
  -- So H' = H, and we are done.
  by_cases huv : u = v
  · -- Scalar case: m = diag(u, u) is central, so conj g H = H.
    left
    subst huv
    -- Every element of GLF commutes with m (m is u*I scalar).
    have hscal : Commute g m := by
      apply Units.ext
      show (g : Matrix (Fin 2) (Fin 2) (ZMod p)) * (m : Matrix (Fin 2) (Fin 2) (ZMod p)) =
             (m : Matrix (Fin 2) (Fin 2) (ZMod p)) * (g : Matrix (Fin 2) (Fin 2) (ZMod p))
      conv_lhs => rw [← hm_eq]
      conv_rhs => rw [← hm_eq]
      show (g : Matrix (Fin 2) (Fin 2) (ZMod p)) *
              Matrix.diagonal ![(u : ZMod p), (u : ZMod p)] =
             Matrix.diagonal ![(u : ZMod p), (u : ZMod p)] *
              (g : Matrix (Fin 2) (Fin 2) (ZMod p))
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.diagonal, Fin.sum_univ_two,
              Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
        ring
    -- H = ⟨m⟩ (both have cardinality q).
    have hH_eq : H = Subgroup.zpowers m := by
      -- Inside H (which has prime order q), the element m₀ ≠ 1 generates H.
      have hm₀_ne : (m₀ : H) ≠ 1 := by
        intro h
        have : orderOf (m₀ : H) = 1 := by rw [h]; exact orderOf_one
        rw [hm₀] at this
        omega
      have hH_card : Nat.card H = q := hHcard
      haveI : Fact q.Prime := ⟨hq⟩
      have htop : Subgroup.zpowers (m₀ : H) = ⊤ := zpowers_eq_top_of_prime_card hH_card hm₀_ne
      -- Lift via H.subtype.
      apply le_antisymm
      · intro x hx
        have hxH : (⟨x, hx⟩ : H) ∈ Subgroup.zpowers (m₀ : H) := by
          rw [htop]; trivial
        rcases Subgroup.mem_zpowers_iff.mp hxH with ⟨k, hk⟩
        have hk' : (m₀ : GLF p) ^ k = x := by
          have := congrArg (·.val) hk
          simp at this
          exact this
        exact ⟨k, hk'⟩
      · rw [Subgroup.zpowers_le]
        exact m₀.property
    -- conj g fixes every power of m, hence fixes H.
    have hg_fix_H : H.map (MulAut.conj g).toMonoidHom = H := by
      ext x
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hy_in : y ∈ Subgroup.zpowers m := hH_eq ▸ hy
        rcases Subgroup.mem_zpowers_iff.mp hy_in with ⟨k, rfl⟩
        have hcomm_zpow : Commute g (m ^ k) := hscal.zpow_right k
        have heq : (MulAut.conj g) (m ^ k) = m ^ k := by
          change g * m ^ k * g⁻¹ = m ^ k
          rw [hcomm_zpow.eq, mul_assoc, mul_inv_cancel, mul_one]
        rw [heq]; exact hy
      · intro hx
        refine ⟨x, hx, ?_⟩
        have hx_in : x ∈ Subgroup.zpowers m := hH_eq ▸ hx
        rcases Subgroup.mem_zpowers_iff.mp hx_in with ⟨k, rfl⟩
        have hcomm_zpow : Commute g (m ^ k) := hscal.zpow_right k
        change g * m ^ k * g⁻¹ = m ^ k
        rw [hcomm_zpow.eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [hconj, hg_fix_H]
  · -- u ≠ v: use conj_diag_to_diag_normalizes
    -- Conjugate m by g: g m g⁻¹ ∈ H' ≤ D, so it's diagonal.
    have hgmg : g * m * g⁻¹ ∈ torusD p := by
      have : g * m * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom := ⟨m, m₀.property, by
        simp [MulAut.conj_apply]; group⟩
      rw [← hconj] at this
      exact hH' this
    rcases hgmg with ⟨⟨u', v'⟩, hgmg_eq⟩
    have hconj_eq : g * m * g⁻¹ = diagEmbed p (u', v') := hgmg_eq.symm
    -- Apply conj_diag_to_diag_normalizes
    have hm_diag : m = diagEmbed p (u, v) := hm_eq.symm
    rw [hm_diag] at hconj_eq
    have := conj_diag_to_diag_normalizes p g u v u' v' huv hconj_eq
    rcases this with hg_diag | ⟨d, hg_eq⟩
    · -- g ∈ D. So conj g H = H by conj_subgroup_torusD_by_diag.
      left
      rw [hconj]
      exact (conj_subgroup_torusD_by_diag p hH hg_diag).symm
    · -- g = d * σ. So conj g H = conj d (conj σ H) = conj σ H (since d ∈ D and H ≤ D).
      right
      rw [hconj]
      rw [hg_eq]
      -- (H.map (conj (d σ))) = ((H.map (conj σ)).map (conj d))
      -- since conj (d * σ) = conj d ∘ conj σ
      have : H.map (MulAut.conj ((d : GLF p) * swapMat p)).toMonoidHom =
             (H.map (MulAut.conj (swapMat p)).toMonoidHom).map (MulAut.conj (d : GLF p)).toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      rw [this]
      -- Now H.map (conj σ) ≤ torusD (since σ normalizes D via swap_conj_diag)
      have hH_swap_le : H.map (MulAut.conj (swapMat p)).toMonoidHom ≤ torusD p := by
        rintro _ ⟨x, hx, rfl⟩
        -- x ∈ H ≤ D, so x = diag(u₀, v₀); swap conj diag = diag swapped.
        rcases hH hx with ⟨⟨u₀, v₀⟩, rfl⟩
        refine ⟨(v₀, u₀), ?_⟩
        have := swap_conj_diag p u₀ v₀
        simp [MulAut.conj_apply, this]
      exact conj_subgroup_torusD_by_diag p hH_swap_le d.property

/-! ### Helpers for the case `q ∣ p-1`: parametrized order-q subgroups. -/

/-- The "standard" order-q subgroups of `torusD`, indexed by `Fin q` (for the
`U_ℓ` family) together with one extra index for `U_∞`. The first family is
generated by `diag(a, a^ℓ)`; the extra one by `diag(1, a)`. -/
private noncomputable def U_param (p q : ℕ) [Fact p.Prime] (a : (ZMod p)ˣ)
    (ℓ : Fin q ⊕ Unit) : Subgroup (GLF p) :=
  match ℓ with
  | Sum.inl ℓ => Subgroup.zpowers (diagEmbed p (a, a ^ ℓ.val))
  | Sum.inr _ => Subgroup.zpowers (diagEmbed p (1, a))

/-- Each `U_param` subgroup has order `q`. -/
private lemma U_param_card (p q : ℕ) [hp : Fact p.Prime] (hq : q.Prime)
    (a : (ZMod p)ˣ) (ha : orderOf a = q) (ℓ : Fin q ⊕ Unit) :
    Nat.card (U_param p q a ℓ) = q := by
  haveI : Fact q.Prime := ⟨hq⟩
  rcases ℓ with ⟨i⟩ | ⟨⟩
  · -- U(inl i) = zpowers (diagEmbed p (a, a^i))
    show Nat.card (Subgroup.zpowers (diagEmbed p (a, a ^ i.val))) = q
    rw [Nat.card_zpowers, orderOf_diagEmbed, ha]
    -- orderOf (a^i) divides orderOf a = q, hence is 1 or q.
    -- In either case, lcm(q, orderOf(a^i)) = q.
    have hdvd : orderOf (a ^ i.val) ∣ q := ha ▸ orderOf_pow_dvd i.val
    have hpos : 0 < orderOf (a ^ i.val) :=
      orderOf_pos_iff.mpr (isOfFinOrder_of_finite _)
    rcases (Nat.dvd_prime hq).mp hdvd with h1 | h1
    · rw [h1]; simp
    · rw [h1]; simp
  · show Nat.card (Subgroup.zpowers (diagEmbed p (1, a))) = q
    rw [Nat.card_zpowers, orderOf_diagEmbed, ha, orderOf_one]
    simp

/-- Each `U_param` is contained in `torusD`. -/
private lemma U_param_le_torusD (p q : ℕ) [Fact p.Prime] (a : (ZMod p)ˣ)
    (ℓ : Fin q ⊕ Unit) : U_param p q a ℓ ≤ torusD p := by
  rcases ℓ with ⟨i⟩ | ⟨⟩
  · -- U(inl i) = zpowers (diagEmbed p (a, a^i))
    show Subgroup.zpowers (diagEmbed p (a, a ^ i.val)) ≤ torusD p
    rw [Subgroup.zpowers_le]
    exact ⟨_, rfl⟩
  · show Subgroup.zpowers (diagEmbed p (1, a)) ≤ torusD p
    rw [Subgroup.zpowers_le]
    exact ⟨_, rfl⟩

/-- Helper: if `u : (ZMod p)ˣ` has order dividing `q` (q prime) and `a` has
order `q`, then `u = a^i` for some `i : ℕ` with `i < q`. -/
private lemma exists_natpow_of_orderDvd (p q : ℕ) [Fact p.Prime] (hq : q.Prime)
    (a u : (ZMod p)ˣ) (ha : orderOf a = q) (hu : orderOf u ∣ q) :
    ∃ (i : ℕ), u = a ^ i ∧ i < q ∧ (orderOf u = 1 ↔ i = 0) := by
  haveI : Fact q.Prime := ⟨hq⟩
  classical
  -- Either orderOf u = 1 (u = 1) or orderOf u = q.
  rcases (Nat.dvd_prime hq).mp hu with hone | hqo
  · -- u = 1. Take i = 0.
    refine ⟨0, ?_, hq.pos, ?_⟩
    · rw [pow_zero]; exact orderOf_eq_one_iff.mp hone
    · constructor <;> intro _
      · rfl
      · exact hone
  · -- u has order q. ⟨u⟩ = ⟨a⟩.
    have hzp_eq : Subgroup.zpowers u = Subgroup.zpowers a := by
      apply unique_subgroup_of_card_in_cyclic hq.pos
      · rw [Nat.card_zpowers]; exact hqo
      · rw [Nat.card_zpowers]; exact ha
    have hu_in : u ∈ Subgroup.zpowers a := hzp_eq ▸ Subgroup.mem_zpowers u
    rcases Subgroup.mem_zpowers_iff.mp hu_in with ⟨k, hk⟩
    -- Convert k : ℤ to i : ℕ with i < q.
    let i : ℕ := (k % q).toNat
    have hq_ne : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have hpos : (0 : ℤ) ≤ k % q := Int.emod_nonneg k hq_ne
    have hlt : k % q < q := Int.emod_lt_of_pos k (by exact_mod_cast hq.pos)
    have hieq : (i : ℤ) = k % q := Int.toNat_of_nonneg hpos
    have hi_lt : i < q := by
      have : (i : ℤ) < q := by rw [hieq]; exact hlt
      exact_mod_cast this
    -- a^i = a^k because orderOf a = q.
    have haqone : a ^ (q : ℤ) = 1 := by
      rw [show (q : ℤ) = (q : ℕ) by simp, zpow_natCast, ← ha]
      exact pow_orderOf_eq_one a
    have hpow_eq : a ^ i = a ^ k := by
      have h1 : a ^ (i : ℕ) = a ^ ((i : ℤ)) := by simp [zpow_natCast]
      rw [h1, hieq]
      conv_rhs => rw [← Int.emod_add_ediv k q]
      rw [zpow_add, zpow_mul, haqone, one_zpow, mul_one]
    refine ⟨i, ?_, hi_lt, ?_⟩
    · rw [hpow_eq, hk]
    · -- orderOf u = q. So 1 = q is false. RHS: i = 0 iff a^i = 1 iff u = 1, but u has order q. So i ≠ 0.
      constructor
      · intro h; rw [hqo] at h; have := hq.one_lt; omega
      · intro h
        -- i = 0 → u = a^0 = 1 → orderOf u = 1, contradicting orderOf u = q.
        rw [h, pow_zero] at hpow_eq
        rw [← hk, ← hpow_eq] at hqo
        rw [orderOf_one] at hqo
        have := hq.one_lt; omega

/-- Every order-q element of `torusD` is `diagEmbed p (a^i, a^j)` for some
`i, j : ℕ` with not both `q ∣ i` and `q ∣ j` (in fact with `i, j < q`). -/
private lemma orderOf_q_torusD_eq (p q : ℕ) [Fact p.Prime] (hq : q.Prime)
    (a : (ZMod p)ˣ) (ha : orderOf a = q)
    (m : GLF p) (hmD : m ∈ torusD p) (hm_order : orderOf m = q) :
    ∃ (i j : ℕ), m = diagEmbed p (a ^ i, a ^ j) ∧ ¬ (q ∣ i ∧ q ∣ j) := by
  haveI : Fact q.Prime := ⟨hq⟩
  classical
  rcases hmD with ⟨⟨u, v⟩, hm_eq⟩
  have hord_eq : Nat.lcm (orderOf u) (orderOf v) = q := by
    rw [← orderOf_diagEmbed, hm_eq]; exact hm_order
  have hu_dvd : orderOf u ∣ q := by rw [← hord_eq]; exact Nat.dvd_lcm_left _ _
  have hv_dvd : orderOf v ∣ q := by rw [← hord_eq]; exact Nat.dvd_lcm_right _ _
  obtain ⟨i, hu_eq, hi_lt, hu_iff⟩ := exists_natpow_of_orderDvd p q hq a u ha hu_dvd
  obtain ⟨j, hv_eq, hj_lt, hv_iff⟩ := exists_natpow_of_orderDvd p q hq a v ha hv_dvd
  refine ⟨i, j, ?_, ?_⟩
  · rw [← hm_eq, hu_eq, hv_eq]
  · -- ¬ (q ∣ i ∧ q ∣ j): if q ∣ i and i < q, then i = 0, so orderOf u = 1.
    -- Similarly for j. Then lcm = 1 ≠ q.
    intro ⟨hqi, hqj⟩
    have hi0 : i = 0 := Nat.eq_zero_of_dvd_of_lt hqi hi_lt
    have hj0 : j = 0 := Nat.eq_zero_of_dvd_of_lt hqj hj_lt
    have hu1 : orderOf u = 1 := hu_iff.mpr hi0
    have hv1 : orderOf v = 1 := hv_iff.mpr hj0
    rw [hu1, hv1] at hord_eq
    simp at hord_eq
    have := hq.one_lt
    omega

/-- Step A: every order-q subgroup of `GLF p` is GLF-conjugate to a subgroup of
`torusD p`. Sylow-strategy: build a q-Sylow of GLF p that lies inside torusD. -/
private lemma exists_conj_into_torusD (p q : ℕ) [Fact p.Prime] (hq : q.Prime)
    (hq2 : 2 < q) (hpq : p ≠ q) (hdvd : q ∣ (p - 1))
    {H : Subgroup (GLF p)} (hHcard : Nat.card H = q) :
    ∃ g : GLF p, H.map (MulAut.conj g).toMonoidHom ≤ torusD p := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Finite (GLF p) := by
    haveI : Fintype (GLF p) := by unfold GLF; infer_instance
    infer_instance
  -- q ∤ p, q ∤ p+1.
  have hp_two : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hq_ne_p : q ≠ p := fun h => hpq h.symm
  have hq_ndvd_p : ¬ q ∣ p := by
    intro h
    exact hq_ne_p ((Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).mp h)
  have hq_ndvd_pp1 : ¬ q ∣ (p + 1) := by
    intro h2
    have hdiff : (p + 1) - (p - 1) = 2 := by omega
    have hq2dvd : q ∣ 2 := by rw [← hdiff]; exact Nat.dvd_sub h2 hdvd
    have : q ≤ 2 := Nat.le_of_dvd (by norm_num) hq2dvd
    omega
  -- factorization
  set k := (p - 1).factorization q with hkdef
  have hp_minus_one_pos : 0 < p - 1 := by omega
  have hp_minus_one_ne : p - 1 ≠ 0 := by omega
  have hp_plus_one_ne : p + 1 ≠ 0 := by omega
  have hp_ne : p ≠ 0 := by omega
  -- |torusD| = (p-1)^2
  have hD_card : Nat.card (torusD p) = (p - 1) ^ 2 := torusD_card p
  -- factorization of |torusD|.
  have hD_card_ne : Nat.card (torusD p) ≠ 0 := by
    rw [hD_card]; positivity
  have hD_factq : (Nat.card (torusD p)).factorization q = 2 * k := by
    rw [hD_card, pow_two, Nat.factorization_mul hp_minus_one_ne hp_minus_one_ne]
    simp [Finsupp.add_apply, k]; ring
  -- factorization of |GLF p|.
  have hGLF_card : Nat.card (GLF p) = (p ^ 2 - 1) * (p ^ 2 - p) := card_GL_two p
  have hp_sq : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    have := Nat.sq_sub_sq p 1
    rw [one_pow] at this; rw [this, mul_comm]
  have hp_sub_p : p ^ 2 - p = p * (p - 1) := by rw [Nat.mul_sub_one, pow_two]
  have hGLF_card2 : Nat.card (GLF p) = ((p - 1) * (p + 1)) * (p * (p - 1)) := by
    rw [hGLF_card, hp_sq, hp_sub_p]
  have hGLF_factq : (Nat.card (GLF p)).factorization q = 2 * k := by
    rw [hGLF_card2]
    rw [Nat.factorization_mul (Nat.mul_ne_zero hp_minus_one_ne hp_plus_one_ne)
        (Nat.mul_ne_zero hp_ne hp_minus_one_ne)]
    rw [Nat.factorization_mul hp_minus_one_ne hp_plus_one_ne]
    rw [Nat.factorization_mul hp_ne hp_minus_one_ne]
    have hpp1_zero : (p + 1).factorization q = 0 := by
      rw [Nat.factorization_eq_zero_iff]; right; left; exact hq_ndvd_pp1
    have hp_zero : p.factorization q = 0 := by
      rw [Nat.factorization_eq_zero_iff]; right; left; exact hq_ndvd_p
    simp [hpp1_zero, hp_zero, Finsupp.add_apply, k]; ring
  -- pick a q-Sylow of torusD; embed to GLF p.
  let SD : Sylow q (torusD p) := default
  have hSD_card : Nat.card SD = q ^ (2 * k) := by
    have := SD.card_eq_multiplicity
    rw [← hD_factq]; convert this using 1
  let SD_GLF : Subgroup (GLF p) := (SD : Subgroup (torusD p)).map (torusD p).subtype
  have hSD_GLF_card : Nat.card SD_GLF = q ^ (2 * k) := by
    have hbij : Function.Bijective ((SD : Subgroup (torusD p)).equivMapOfInjective
        (torusD p).subtype Subtype.val_injective) :=
      ((SD : Subgroup (torusD p)).equivMapOfInjective (torusD p).subtype
        Subtype.val_injective).bijective
    have := Nat.card_eq_of_bijective _ hbij
    rw [← this, hSD_card]
  -- SD_GLF is a Sylow q-subgroup of GLF p.
  let S₀ : Sylow q (GLF p) :=
    Sylow.ofCard SD_GLF (by rw [hSD_GLF_card, hGLF_factq])
  -- H is q-subgroup of GLF p, hence contained in some Sylow q-subgroup.
  have hH_p : IsPGroup q H := IsPGroup.of_card (n := 1) (by rw [hHcard]; ring)
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hH_p
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GLF p) P S₀
  refine ⟨g, ?_⟩
  have hmap_eq : ∀ (g : GLF p) (P : Sylow q (GLF p)),
      (P : Subgroup (GLF p)).map (MulAut.conj g).toMonoidHom =
      (MulAut.conj g) • (P : Subgroup (GLF p)) := by
    intros g P
    rw [Subgroup.pointwise_smul_def]; rfl
  have hsmul_eq : ∀ (g : GLF p) (P Q : Sylow q (GLF p)), g • P = Q →
      (P : Subgroup (GLF p)).map (MulAut.conj g).toMonoidHom = (Q : Subgroup (GLF p)) := by
    intros g P Q h
    rw [hmap_eq]
    have h' : ((g • P : Sylow q (GLF p)) : Subgroup (GLF p)) =
              ((Q : Sylow q (GLF p)) : Subgroup (GLF p)) := by rw [h]
    rw [Sylow.coe_subgroup_smul] at h'; exact h'
  have hH_to_S₀ : H.map (MulAut.conj g).toMonoidHom ≤ (S₀ : Subgroup (GLF p)) := by
    have step : H.map (MulAut.conj g).toMonoidHom ≤
                 (P : Subgroup (GLF p)).map (MulAut.conj g).toMonoidHom :=
      Subgroup.map_mono hP
    rw [hsmul_eq g P S₀ hg] at step
    exact step
  -- S₀ ≤ torusD by construction.
  have hS₀_le_D : (S₀ : Subgroup (GLF p)) ≤ torusD p := by
    intro x hx
    -- x ∈ S₀ = SD_GLF = image of SD in torusD ↪ GLF.
    show x ∈ torusD p
    -- hx : x ∈ S₀, but S₀ = ⟨Sylow.ofCard SD_GLF ..⟩, so x ∈ SD_GLF.
    have hxSD : x ∈ SD_GLF := hx
    -- SD_GLF = (SD : Subgroup _).map (torusD p).subtype
    rcases hxSD with ⟨y, _, rfl⟩
    exact y.property
  exact hH_to_S₀.trans hS₀_le_D

/-! ### Step B helpers: the swap involution on `Fin q ⊕ Unit`. -/

/-- The involution on `Fin q ⊕ Unit` corresponding to conjugation by the swap
matrix. It sends `inl 0 ↔ inr ()` and `inl ℓ ↔ inl ℓ⁻¹` for `ℓ ≠ 0` (mod `q`). -/
private noncomputable def swapIdx (q : ℕ) [hq : Fact q.Prime] :
    Fin q ⊕ Unit → Fin q ⊕ Unit :=
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  fun ℓ => match ℓ with
  | Sum.inl ℓ =>
      if ℓ.val = 0 then Sum.inr ()
      else Sum.inl ⟨((ℓ.val : ZMod q)⁻¹).val, ZMod.val_lt _⟩
  | Sum.inr () => Sum.inl ⟨0, hq.out.pos⟩

/-- Helper: zpowers of a conjugate equals conjugation of zpowers. -/
private lemma zpowers_conj (p : ℕ) [Fact p.Prime] (g x : GLF p) :
    (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers (g * x * g⁻¹) := by
  rw [MonoidHom.map_zpowers]
  rfl

/-- Two cyclic subgroups of the same finite cardinality with one containing
the other's generator are equal. -/
private lemma zpowers_eq_of_card_of_mem {G : Type*} [Group G]
    {x y : G} (n : ℕ) [Finite (Subgroup.zpowers y)]
    (hx : Nat.card (Subgroup.zpowers x) = n)
    (hy : Nat.card (Subgroup.zpowers y) = n) (hmem : x ∈ Subgroup.zpowers y) :
    Subgroup.zpowers x = Subgroup.zpowers y := by
  have h1 : Subgroup.zpowers x ≤ Subgroup.zpowers y := by
    rw [Subgroup.zpowers_le]; exact hmem
  have hcard_eq : Nat.card (Subgroup.zpowers x) = Nat.card (Subgroup.zpowers y) := by
    rw [hx, hy]
  exact Subgroup.eq_of_le_of_card_ge h1 (by rw [hcard_eq])

/-- `swapIdx q` is an involution. -/
private lemma swapIdx_involutive (q : ℕ) [hqf : Fact q.Prime] :
    Function.Involutive (swapIdx q) := by
  haveI : NeZero q := ⟨hqf.out.ne_zero⟩
  intro ℓ
  rcases ℓ with i | ⟨⟩
  · by_cases hi : i.val = 0
    · -- swapIdx (inl 0) = inr (); swapIdx (inr ()) = inl ⟨0, pos⟩.
      have h1 : swapIdx q (Sum.inl i) = Sum.inr () := by
        show (if i.val = 0 then Sum.inr () else _) = Sum.inr ()
        rw [if_pos hi]
      rw [h1]
      show Sum.inl (⟨0, hqf.out.pos⟩ : Fin q) = Sum.inl i
      congr 1
      apply Fin.ext; simp [hi]
    · -- inl i with i.val ≠ 0
      have hi_ne : (i.val : ZMod q) ≠ 0 := by
        intro h
        rw [ZMod.natCast_eq_zero_iff] at h
        have h1 : i.val < q := i.isLt
        exact hi (Nat.eq_zero_of_dvd_of_lt h h1)
      have h1 : swapIdx q (Sum.inl i) =
          Sum.inl ⟨((i.val : ZMod q)⁻¹).val, ZMod.val_lt _⟩ := by
        show (if i.val = 0 then Sum.inr () else _) = _
        rw [if_neg hi]
      rw [h1]
      -- swapIdx (inl ⟨(i⁻¹).val, _⟩). Need ((i⁻¹).val).val ≠ 0, which means (i⁻¹) ≠ 0.
      have hinv_ne : ((i.val : ZMod q)⁻¹).val ≠ 0 := by
        intro hv
        have hzero : ((i.val : ZMod q)⁻¹) = 0 := by
          rw [← ZMod.val_eq_zero]; exact hv
        have hmul_inv : (i.val : ZMod q) * (i.val : ZMod q)⁻¹ = 1 :=
          ZMod.mul_inv_of_unit _ (Ne.isUnit hi_ne)
        rw [hzero, mul_zero] at hmul_inv
        exact one_ne_zero hmul_inv.symm
      have h2 : swapIdx q (Sum.inl (⟨((i.val : ZMod q)⁻¹).val, ZMod.val_lt _⟩ : Fin q)) =
          Sum.inl ⟨(((((i.val : ZMod q)⁻¹).val : ZMod q))⁻¹).val, ZMod.val_lt _⟩ := by
        show (if (⟨((i.val : ZMod q)⁻¹).val, _⟩ : Fin q).val = 0 then Sum.inr () else _) = _
        rw [if_neg hinv_ne]
      rw [h2]
      -- Show: inl ⟨(((i⁻¹).val).cast.inv).val, _⟩ = inl i
      congr 1
      apply Fin.ext
      show (((((i.val : ZMod q)⁻¹).val : ZMod q))⁻¹).val = i.val
      have step1 : (((((i.val : ZMod q)⁻¹).val : ZMod q))⁻¹) = (i.val : ZMod q) := by
        rw [ZMod.natCast_val, ZMod.cast_id, inv_inv]
      rw [step1, ZMod.val_natCast]
      exact Nat.mod_eq_of_lt i.isLt
  · -- inr ()
    show swapIdx q (Sum.inl ⟨0, hqf.out.pos⟩) = Sum.inr ()
    show (if (⟨0, hqf.out.pos⟩ : Fin q).val = 0 then Sum.inr ()
          else Sum.inl ⟨(((⟨0, hqf.out.pos⟩ : Fin q).val : ZMod q)⁻¹).val, ZMod.val_lt _⟩)
          = Sum.inr ()
    rw [if_pos rfl]

/-- Conjugation by `swapMat` sends `U_param p q a ℓ` to `U_param p q a (swapIdx q ℓ)`. -/
private lemma U_param_conj_swap (p q : ℕ) [Fact p.Prime] [hqf : Fact q.Prime] (hq2 : 2 < q)
    (hpq : p ≠ q) (hdvd : q ∣ (p - 1)) (a : (ZMod p)ˣ) (ha : orderOf a = q) (ℓ : Fin q ⊕ Unit) :
    (U_param p q a ℓ).map (MulAut.conj (swapMat p)).toMonoidHom =
      U_param p q a (swapIdx q ℓ) := by
  haveI : NeZero q := ⟨hqf.out.ne_zero⟩
  haveI : Finite (GLF p) := by
    haveI : Fintype (GLF p) := by unfold GLF; infer_instance
    infer_instance
  rcases ℓ with i | ⟨⟩
  · -- inl i case
    show (Subgroup.zpowers (diagEmbed p (a, a ^ i.val))).map (MulAut.conj (swapMat p)).toMonoidHom
      = U_param p q a (swapIdx q (Sum.inl i))
    rw [zpowers_conj, swap_conj_diag]
    -- Now want: zpowers (diag(a^i, a)) = U_param (swapIdx (inl i))
    by_cases hi : i.val = 0
    · -- swapIdx (inl 0) = inr (). diag(a^0, a) = diag(1, a) = generator of U_param (inr ()).
      have hswap : swapIdx q (Sum.inl i) = Sum.inr () := by
        show (if i.val = 0 then Sum.inr () else _) = Sum.inr ()
        rw [if_pos hi]
      rw [hswap]
      -- U_param (inr ()) = zpowers (diag(1, a))
      show Subgroup.zpowers (diagEmbed p (a ^ i.val, a)) = Subgroup.zpowers (diagEmbed p (1, a))
      rw [hi, pow_zero]
    · -- i.val ≠ 0 case. swapIdx (inl i) = inl ((i⁻¹ : ZMod q).val).
      have hi_ne : (i.val : ZMod q) ≠ 0 := by
        intro h
        rw [ZMod.natCast_eq_zero_iff] at h
        have h1 : i.val < q := i.isLt
        have h2 : i.val = 0 := Nat.eq_zero_of_dvd_of_lt h h1
        exact hi h2
      -- Define the inverse index ℓ' = ((i.val : ZMod q)⁻¹).val.
      set ℓ' : Fin q := ⟨((i.val : ZMod q)⁻¹).val, ZMod.val_lt _⟩ with hℓ'def
      have hswap : swapIdx q (Sum.inl i) = Sum.inl ℓ' := by
        show (if i.val = 0 then Sum.inr () else _) = Sum.inl ℓ'
        rw [if_neg hi]
      rw [hswap]
      -- Goal: zpowers (diag(a^i, a)) = U_param (inl ℓ') = zpowers (diag(a, a^ℓ')).
      show Subgroup.zpowers (diagEmbed p (a ^ i.val, a)) =
            Subgroup.zpowers (diagEmbed p (a, a ^ ℓ'.val))
      -- Key idea: i.val * ℓ'.val ≡ 1 mod q. So (diag(a, a^ℓ'))^i.val = diag(a^i, a^(i*ℓ')).
      -- And a^(i.val * ℓ'.val) = a^1 since order q.
      -- We want: zpowers (diag(a^i, a)) = zpowers (diag(a, a^ℓ')).
      -- Key: a^(ℓ'.val * i.val) = a in (ZMod p)ˣ.
      have hl_eq : ((ℓ'.val : ZMod q)) = (i.val : ZMod q)⁻¹ := by
        rw [hℓ'def]
        show ((((i.val : ZMod q)⁻¹).val : ZMod q)) = (i.val : ZMod q)⁻¹
        rw [ZMod.natCast_val]; exact ZMod.cast_id q _
      have hmul_inv : (i.val : ZMod q) * (i.val : ZMod q)⁻¹ = 1 :=
        ZMod.mul_inv_of_unit _ (Ne.isUnit hi_ne)
      have hpowa : a ^ (ℓ'.val * i.val) = a := by
        -- The point: (ℓ'.val * i.val : ZMod q) = (1 : ZMod q).
        have hcast : ((ℓ'.val * i.val : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by
          push_cast
          rw [hl_eq, mul_comm]; exact hmul_inv
        have hmodeq : (ℓ'.val * i.val) ≡ 1 [MOD q] :=
          (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
        have ha_q : a ^ q = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
        have := pow_eq_pow_of_modEq hmodeq ha_q
        simpa using this
      -- Compute: (diag(a, a^ℓ'))^i = diag(a^i, a^(ℓ'*i)) = diag(a^i, a).
      have hpow_eq : (diagEmbed p (a, a ^ ℓ'.val)) ^ i.val = diagEmbed p (a ^ i.val, a) := by
        rw [← map_pow]
        congr 1
        show ((a, a ^ ℓ'.val) ^ i.val) = (a ^ i.val, a)
        rw [Prod.pow_def]
        refine Prod.mk.injEq .. |>.mpr ⟨rfl, ?_⟩
        rw [← pow_mul]; exact hpowa
      -- Now both subgroups equal because zpowers (g^i) = zpowers g when gcd(i, ord g) = 1.
      -- But more simply: we have diag(a^i, a) = (diag(a, a^ℓ'))^i, so it's in zpowers.
      -- For equality, use that diag(a, a^ℓ') is also in zpowers diag(a^i, a) — but this
      -- requires same argument. Simpler: use cardinality + one-direction containment.
      apply zpowers_eq_of_card_of_mem q
      · -- card of zpowers (diag(a^i, a)) = q via orderOf
        rw [Nat.card_zpowers, orderOf_diagEmbed]
        -- orderOf (a^i.val) = q (since q prime, q ∤ i.val).
        have hi_ne_nat : ¬ (q ∣ i.val) := by
          intro h
          have h1 : i.val < q := i.isLt
          exact hi (Nat.eq_zero_of_dvd_of_lt h h1)
        have hord_ai : orderOf (a ^ i.val) = q := by
          rw [orderOf_pow a, ha]
          have hgcd : Nat.gcd q i.val = 1 := hqf.out.coprime_iff_not_dvd.mpr hi_ne_nat
          rw [hgcd]; exact Nat.div_one _
        rw [hord_ai, ha, Nat.lcm_self]
      · -- card of zpowers (diag(a, a^ℓ')) = q
        have h := U_param_card p q hqf.out a ha (Sum.inl ℓ')
        change Nat.card (Subgroup.zpowers (diagEmbed p (a, a ^ ℓ'.val))) = q at h
        exact h
      · -- diag(a^i, a) ∈ zpowers (diag(a, a^ℓ'))
        rw [← hpow_eq]
        exact ⟨(i.val : ℤ), by simp [zpow_natCast]⟩
  · -- inr () case
    show (Subgroup.zpowers (diagEmbed p (1, a))).map (MulAut.conj (swapMat p)).toMonoidHom
      = U_param p q a (swapIdx q (Sum.inr ()))
    rw [zpowers_conj, swap_conj_diag]
    -- Goal: zpowers (diag(a, 1)) = U_param (inl ⟨0, _⟩) = zpowers (diag(a, a^0)) = zpowers (diag(a, 1)).
    show Subgroup.zpowers (diagEmbed p (a, 1)) =
         Subgroup.zpowers (diagEmbed p (a, a ^ (⟨0, hqf.out.pos⟩ : Fin q).val))
    simp

/-- Every order-`q` subgroup of `torusD p` equals some `U_param p q a ℓ`. -/
private lemma every_torusD_order_q_eq_Uparam (p q : ℕ) [Fact p.Prime] [hqf : Fact q.Prime]
    (a : (ZMod p)ˣ) (ha : orderOf a = q)
    {H : Subgroup (GLF p)} (hH : H ≤ torusD p) (hHcard : Nat.card H = q) :
    ∃ ℓ : Fin q ⊕ Unit, H = U_param p q a ℓ := by
  classical
  haveI : Finite (GLF p) := by
    haveI : Fintype (GLF p) := by unfold GLF; infer_instance
    infer_instance
  haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hHcard]; exact hqf.out.ne_zero)
  haveI : Fintype H := Fintype.ofFinite _
  -- Get a generator m of H with order q.
  obtain ⟨m₀, hm₀⟩ := exists_prime_orderOf_dvd_card (G := H) q
    (by rw [Fintype.card_eq_nat_card]; rw [hHcard])
  let m : GLF p := m₀
  have hm_order : orderOf m = q := by
    have := orderOf_injective H.subtype Subtype.val_injective m₀
    simp only [Subgroup.coe_subtype] at this
    rw [show (m : GLF p) = (m₀ : GLF p) from rfl, this]; exact hm₀
  -- H = zpowers m.
  have hm_in_H : m ∈ H := m₀.property
  have hH_eq : H = Subgroup.zpowers m := by
    have hm₀_ne : (m₀ : H) ≠ 1 := by
      intro h
      have h1 : orderOf (m₀ : H) = 1 := by rw [h]; exact orderOf_one
      rw [hm₀] at h1
      have := hqf.out.one_lt; omega
    have htop : Subgroup.zpowers (m₀ : H) = ⊤ :=
      zpowers_eq_top_of_prime_card hHcard hm₀_ne
    apply le_antisymm
    · intro x hx
      have hxH : (⟨x, hx⟩ : H) ∈ Subgroup.zpowers (m₀ : H) := by rw [htop]; trivial
      rcases Subgroup.mem_zpowers_iff.mp hxH with ⟨k, hk⟩
      have hk' : (m₀ : GLF p) ^ k = x := by
        have := congrArg (·.val) hk
        simp at this; exact this
      exact ⟨k, hk'⟩
    · rw [Subgroup.zpowers_le]; exact hm_in_H
  -- m ∈ torusD, so m = diagEmbed p (a^i, a^j) by orderOf_q_torusD_eq.
  have hmD : m ∈ torusD p := hH hm_in_H
  obtain ⟨i, j, hm_eq, hij⟩ := orderOf_q_torusD_eq p q hqf.out a ha m hmD hm_order
  -- Choose ℓ based on i, j.
  haveI : NeZero q := ⟨hqf.out.ne_zero⟩
  -- Case 1: q ∣ i. Then i.mod = 0, so by hij j is not divisible by q. Use inr ().
  -- We need H = zpowers (diag(a^i, a^j)). Show H = U_param p q a (inr ()) = zpowers (diag(1, a)).
  -- More precisely: We want to convert (a^i, a^j) to (1, a) up to ℓ in {inl ℓ, inr ()}.
  -- We have card H = q. Each U_param has card q.
  -- For surjection: if i ≡ 0 mod q, then a^i = 1, so m = diag(1, a^j). j not divisible.
  --   Then orderOf (a^j) = q. So a^j = a^k for some k coprime to q. We need diag(1, a^j) ∈ zpowers (diag(1, a))?
  --   No, we need zpowers diag(1, a^j) = zpowers diag(1, a). This holds because diag(1, a^j) generates
  --   same subgroup as diag(1, a^j) and both have order q.
  --   Idea: diag(1, a^j) ∈ zpowers diag(1, a) trivially: it's (diag(1, a))^j. And both have order q.
  -- For case i not divisible: use inl. Specifically: ℓ = ((a^j orderdvd... )
  by_cases hqi : q ∣ i
  · -- q ∣ i case. Then a^i = 1, m = diag(1, a^j), j not divisible by q.
    have hai : a ^ i = 1 := by
      rw [← ha] at hqi
      exact orderOf_dvd_iff_pow_eq_one.mp hqi
    have hqj : ¬ q ∣ j := fun h => hij ⟨hqi, h⟩
    -- choose ℓ = inr ()
    refine ⟨Sum.inr (), ?_⟩
    -- U_param p q a (inr ()) = zpowers (diag(1, a)) and H = zpowers (diag(1, a^j))
    change H = Subgroup.zpowers (diagEmbed p (1, a))
    rw [hH_eq]
    -- m = diag(a^i, a^j) = diag(1, a^j). Show zpowers (diag(1, a^j)) = zpowers (diag(1, a)).
    have hm_eq' : m = diagEmbed p (1, a ^ j) := by rw [hm_eq, hai]
    rw [hm_eq']
    -- Apply zpowers_eq_of_card_of_mem.
    apply zpowers_eq_of_card_of_mem q
    · rw [Nat.card_zpowers, orderOf_diagEmbed, orderOf_one]
      have hord_aj : orderOf (a ^ j) = q := by
        rw [orderOf_pow a, ha]
        have hgcd : Nat.gcd q j = 1 := hqf.out.coprime_iff_not_dvd.mpr hqj
        rw [hgcd]; exact Nat.div_one _
      rw [hord_aj]; simp
    · rw [Nat.card_zpowers, orderOf_diagEmbed, orderOf_one, ha]; simp
    · -- diag(1, a^j) ∈ zpowers (diag(1, a))
      refine ⟨(j : ℤ), ?_⟩
      simp only [zpow_natCast, ← map_pow]
      congr 1
      show ((1 : (ZMod p)ˣ), a) ^ j = (1, a ^ j)
      rw [Prod.pow_def]; simp
  · -- q ∤ i case. Use inl (a^j / a^i mod q), i.e., the index ℓ where a^j = (a^i)^ℓ.
    -- m = diag(a^i, a^j). Want zpowers m = zpowers (diag(a, a^ℓ)).
    -- Let i' = i mod q. Since q∤i, i' ≠ 0 and i' ∈ Fin q.
    -- Since orderOf (a^i) = q, a^i generates ⟨a⟩, so a^i = a^k for some k coprime to q.
    -- Then m^(k'with k*k'=1) = diag(a, a^(j*k')).
    -- Actually simpler: choose ℓ such that a^ℓ = a^(j*i⁻¹) where i⁻¹ is the inverse mod q.
    -- We need m = (diag(a, a^ℓ))^i (mod q). Let me just use ZMod q.
    have hi_ne : (i : ZMod q) ≠ 0 := by
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      exact hqi h
    set i' : (ZMod q)ˣ := Units.mk0 (i : ZMod q) hi_ne with hi'_def
    -- ℓ = (i'⁻¹ * j : ZMod q).val, taken mod q to get a Fin q.
    let ℓval : ℕ := ((((i'⁻¹ : (ZMod q)ˣ) : ZMod q) * (j : ZMod q)).val)
    have hℓval_lt : ℓval < q := ZMod.val_lt _
    refine ⟨Sum.inl ⟨ℓval, hℓval_lt⟩, ?_⟩
    change H = Subgroup.zpowers (diagEmbed p (a, a ^ (⟨ℓval, hℓval_lt⟩ : Fin q).val))
    rw [hH_eq, hm_eq]
    -- Now want: zpowers (diag(a^i, a^j)) = zpowers (diag(a, a^ℓval)).
    -- Key: (a^i, a^j) = (a, a^ℓval)^i ?  Then a^(ℓval * i) = a^j.
    -- We have ℓval ≡ i⁻¹ * j mod q, so ℓval * i ≡ j mod q, so a^(ℓval * i) = a^j.
    apply zpowers_eq_of_card_of_mem q
    · rw [Nat.card_zpowers, orderOf_diagEmbed]
      have hord_ai : orderOf (a ^ i) = q := by
        rw [orderOf_pow a, ha]
        have hgcd : Nat.gcd q i = 1 := hqf.out.coprime_iff_not_dvd.mpr hqi
        rw [hgcd]; exact Nat.div_one _
      have hord_aj_dvd : orderOf (a ^ j) ∣ q := ha ▸ orderOf_pow_dvd j
      rw [hord_ai]
      rcases (Nat.dvd_prime hqf.out).mp hord_aj_dvd with h1 | h1
      · rw [h1]; simp
      · rw [h1]; simp
    · -- Use U_param_card
      have h := U_param_card p q hqf.out a ha (Sum.inl ⟨ℓval, hℓval_lt⟩)
      change Nat.card (Subgroup.zpowers (diagEmbed p (a, a ^ (⟨ℓval, hℓval_lt⟩ : Fin q).val))) = q at h
      exact h
    · -- diag(a^i, a^j) ∈ zpowers (diag(a, a^ℓval)).
      -- We claim (diag(a, a^ℓval))^i = diag(a^i, a^(i * ℓval)) = diag(a^i, a^j).
      have hmodeq : (i * ℓval) ≡ j [MOD q] := by
        -- (i * ℓval : ZMod q) = i * (i'⁻¹ * j) = j (using i = i')
        have h_in_zmod : ((i * ℓval : ℕ) : ZMod q) = ((j : ℕ) : ZMod q) := by
          push_cast
          show (i : ZMod q) * (((((i'⁻¹ : (ZMod q)ˣ) : ZMod q) * (j : ZMod q))).val : ZMod q)
            = (j : ZMod q)
          rw [ZMod.natCast_val, ZMod.cast_id]
          -- Now (i) * (i'⁻¹ * j) = j since i = i'.
          have : (i : ZMod q) = (i' : ZMod q) := rfl
          rw [this]
          rw [← mul_assoc]
          rw [Units.mul_inv]
          ring
        exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h_in_zmod
      have hpow_a : a ^ (i * ℓval) = a ^ j := by
        have ha_q : a ^ q = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
        exact pow_eq_pow_of_modEq hmodeq ha_q
      refine ⟨(i : ℤ), ?_⟩
      simp only [zpow_natCast, ← map_pow]
      congr 1
      show ((a, a ^ (⟨ℓval, hℓval_lt⟩ : Fin q).val)) ^ i = (a ^ i, a ^ j)
      rw [Prod.pow_def]
      refine Prod.mk.injEq .. |>.mpr ⟨rfl, ?_⟩
      simp only
      rw [← pow_mul, mul_comm]
      exact hpow_a

/-- The equivalence relation on `Fin q ⊕ Unit` whose orbits correspond to
GLF-conjugacy classes of `U_param`. -/
private def swapOrbitSetoid (q : ℕ) [Fact q.Prime] : Setoid (Fin q ⊕ Unit) where
  r ℓ ℓ' := ℓ = ℓ' ∨ ℓ = swapIdx q ℓ'
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      intro ℓ ℓ' h
      rcases h with h | h
      · exact Or.inl h.symm
      · right
        have := congrArg (swapIdx q) h
        rw [swapIdx_involutive q ℓ'] at this
        exact this.symm
    trans := by
      intro a b c hab hbc
      rcases hab with hab | hab
      · rcases hbc with hbc | hbc
        · left; rw [hab, hbc]
        · right; rw [hab, hbc]
      · rcases hbc with hbc | hbc
        · right; rw [← hbc, hab]
        · left
          rw [hab, hbc, swapIdx_involutive q c]
  }

/-- `U_param a` is injective in `ℓ` when `a` has order `q`. -/
private lemma U_param_injective (p q : ℕ) [Fact p.Prime] [hqf : Fact q.Prime]
    (a : (ZMod p)ˣ) (ha : orderOf a = q)
    {ℓ ℓ' : Fin q ⊕ Unit} (h : U_param p q a ℓ = U_param p q a ℓ') :
    ℓ = ℓ' := by
  have hq1 := hqf.out.one_lt
  -- Helper: from H = zpowers x = zpowers y, x ∈ zpowers y, so y^k = x for some k.
  -- Apply diagEmbed_injective: (a, b)^k = (a', b').
  rcases ℓ with i | ⟨⟩ <;> rcases ℓ' with i' | ⟨⟩
  · -- inl i, inl i'. Need i = i'.
    change Subgroup.zpowers (diagEmbed p (a, a ^ i.val)) =
           Subgroup.zpowers (diagEmbed p (a, a ^ i'.val)) at h
    have hmem : diagEmbed p (a, a ^ i.val) ∈
                Subgroup.zpowers (diagEmbed p (a, a ^ i'.val)) := by
      rw [← h]; exact Subgroup.mem_zpowers _
    rcases hmem with ⟨k, hk⟩
    have hk' : ((a, a ^ i'.val) : (ZMod p)ˣ × (ZMod p)ˣ) ^ k = (a, a ^ i.val) := by
      apply diagEmbed_injective p; rw [map_zpow]; exact hk
    rw [Prod.pow_def] at hk'
    have hk_left : (a : (ZMod p)ˣ) ^ k = a := (Prod.mk.injEq ..).mp hk' |>.1
    have hk_right : (a ^ i'.val : (ZMod p)ˣ) ^ k = a ^ i.val := (Prod.mk.injEq ..).mp hk' |>.2
    -- From hk_left: a^(k-1) = 1, so q ∣ k - 1.
    have hk_minus_one : a ^ (k - 1) = 1 := by
      rw [show k - 1 = k + (-1) from rfl, zpow_add, zpow_neg_one, hk_left]; group
    have hq_dvd_km1 : (q : ℤ) ∣ (k - 1) := by
      have := orderOf_dvd_iff_zpow_eq_one.mpr hk_minus_one
      rw [ha] at this; exact_mod_cast this
    -- From hk_right: a^(i'*k - i) = 1, so q ∣ i' * k - i.
    have hk_right' : a ^ ((i'.val : ℤ) * k - i.val) = 1 := by
      rw [show (i'.val : ℤ) * k - i.val = (i'.val : ℤ) * k + (-(i.val : ℤ)) from by ring]
      rw [zpow_add, zpow_neg]
      have step : a ^ ((i'.val : ℤ) * k) = a ^ (i.val : ℤ) := by
        rw [zpow_mul]
        rw [show a ^ (i'.val : ℤ) = a ^ i'.val from by simp [zpow_natCast]]
        rw [hk_right]
        simp [zpow_natCast]
      rw [step, mul_inv_cancel]
    have hq_dvd_prod : (q : ℤ) ∣ ((i'.val : ℤ) * k - i.val) := by
      have := orderOf_dvd_iff_zpow_eq_one.mpr hk_right'
      rw [ha] at this; exact_mod_cast this
    -- (i' * k - i) = i' * (k - 1) + (i' - i). So q ∣ i' - i.
    have hq_dvd_diff : (q : ℤ) ∣ (i'.val : ℤ) - i.val := by
      have hdvd_im1 : (q : ℤ) ∣ (i'.val : ℤ) * (k - 1) := Dvd.dvd.mul_left hq_dvd_km1 _
      have : (i'.val : ℤ) * k - i.val = (i'.val : ℤ) * (k - 1) + ((i'.val : ℤ) - i.val) := by ring
      have h2 := dvd_sub hq_dvd_prod hdvd_im1
      rw [this] at h2
      simpa using h2
    -- Conclude i = i'.
    have hi_eq : i.val = i'.val := by
      have hi_lt : i.val < q := i.isLt
      have hi'_lt : i'.val < q := i'.isLt
      have habs : |((i'.val : ℤ) - i.val)| < q := by
        have h1 : ((i'.val : ℤ) - i.val) ≥ -(q : ℤ) := by
          have : (i.val : ℤ) ≤ (q : ℤ) - 1 := by omega
          linarith
        have h2 : ((i'.val : ℤ) - i.val) ≤ q - 1 := by
          have : (i'.val : ℤ) ≤ (q : ℤ) - 1 := by omega
          linarith
        rw [abs_lt]; omega
      have : (i'.val : ℤ) - i.val = 0 := by
        rcases hq_dvd_diff with ⟨c, hc⟩
        by_contra hne
        have hc_ne : c ≠ 0 := by
          rintro rfl; simp at hc; exact hne hc
        have habs_c : 1 ≤ |c| := by
          rcases Int.lt_or_lt_of_ne hc_ne with h | h
          · have : c ≤ -1 := by omega
            rw [abs_of_nonpos (by omega)]; omega
          · rw [abs_of_pos h]; omega
        have hq_pos : (0 : ℤ) < q := by exact_mod_cast hqf.out.pos
        have : (q : ℤ) ≤ |((i'.val : ℤ) - i.val)| := by
          rw [hc, abs_mul, abs_of_pos hq_pos]
          calc (q : ℤ) = q * 1 := by ring
            _ ≤ q * |c| := by nlinarith
        linarith
      have : (i'.val : ℤ) = i.val := by linarith
      omega
    congr 1
    apply Fin.ext; exact hi_eq
  · -- inl i, inr (). Contradicts: diag(a, ai) ∈ zpowers diag(1, a) gives 1 = a^k.
    exfalso
    change Subgroup.zpowers (diagEmbed p (a, a ^ i.val)) =
           Subgroup.zpowers (diagEmbed p (1, a)) at h
    have hmem : diagEmbed p (a, a ^ i.val) ∈ Subgroup.zpowers (diagEmbed p (1, a)) := by
      rw [← h]; exact Subgroup.mem_zpowers _
    rcases hmem with ⟨k, hk⟩
    have hk' : ((1 : (ZMod p)ˣ), a) ^ k = (a, a ^ i.val) := by
      apply diagEmbed_injective p; rw [map_zpow]; exact hk
    rw [Prod.pow_def] at hk'
    have hk_left : (1 : (ZMod p)ˣ) ^ k = a := (Prod.mk.injEq ..).mp hk' |>.1
    rw [one_zpow] at hk_left
    rw [← hk_left, orderOf_one] at ha
    omega
  · -- inr (), inl i'. Symmetric: diag(1, a) ∈ zpowers diag(a, a^i') gives a^k = 1, then a = 1 via second.
    exfalso
    change Subgroup.zpowers (diagEmbed p (1, a)) =
           Subgroup.zpowers (diagEmbed p (a, a ^ i'.val)) at h
    have hmem : diagEmbed p (1, a) ∈ Subgroup.zpowers (diagEmbed p (a, a ^ i'.val)) := by
      rw [← h]; exact Subgroup.mem_zpowers _
    rcases hmem with ⟨k, hk⟩
    have hk' : ((a, a ^ i'.val) : (ZMod p)ˣ × (ZMod p)ˣ) ^ k = (1, a) := by
      apply diagEmbed_injective p; rw [map_zpow]; exact hk
    rw [Prod.pow_def] at hk'
    have hk_left : (a : (ZMod p)ˣ) ^ k = 1 := (Prod.mk.injEq ..).mp hk' |>.1
    have hk_right : (a ^ i'.val : (ZMod p)ˣ) ^ k = a := (Prod.mk.injEq ..).mp hk' |>.2
    -- a^k = 1 → q ∣ k.
    have hq_dvd_k : (q : ℤ) ∣ k := by
      have := orderOf_dvd_iff_zpow_eq_one.mpr hk_left
      rw [ha] at this; exact_mod_cast this
    -- a^(i' * k) = a^1, so q ∣ i'*k - 1.
    have h_pow : a ^ ((i'.val : ℤ) * k - 1) = 1 := by
      rw [show (i'.val : ℤ) * k - 1 = (i'.val : ℤ) * k + (-1) from by ring]
      rw [zpow_add, zpow_neg_one]
      have h1 : a ^ ((i'.val : ℤ) * k) = a := by
        rw [zpow_mul]
        rw [show a ^ (i'.val : ℤ) = a ^ i'.val from by simp [zpow_natCast]]
        rw [hk_right]
      rw [h1, mul_inv_cancel]
    have hq_dvd_minus_one : (q : ℤ) ∣ ((i'.val : ℤ) * k - 1) := by
      have := orderOf_dvd_iff_zpow_eq_one.mpr h_pow
      rw [ha] at this; exact_mod_cast this
    -- q ∣ k → q ∣ i'*k. Combined: q ∣ 1.
    have hq_dvd_prod : (q : ℤ) ∣ (i'.val : ℤ) * k := Dvd.dvd.mul_left hq_dvd_k _
    have hq_dvd_one : (q : ℤ) ∣ 1 := by
      have := dvd_sub hq_dvd_prod hq_dvd_minus_one
      simpa using this
    have : (q : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) hq_dvd_one
    have : q ≤ 1 := by exact_mod_cast this
    omega
  · rfl

/-- Two `U_param a ℓ` and `U_param a ℓ'` are GLF-conjugate iff their indices
are related by the swap involution. -/
private lemma Uparam_conj_iff_swap (p q : ℕ) [Fact p.Prime] [hqf : Fact q.Prime]
    (hq2 : 2 < q) (hpq : p ≠ q) (hdvd : q ∣ (p - 1)) (a : (ZMod p)ˣ) (ha : orderOf a = q)
    (ℓ ℓ' : Fin q ⊕ Unit) :
    Subgroup.IsConjGp (U_param p q a ℓ) (U_param p q a ℓ') ↔
      (swapOrbitSetoid q).r ℓ ℓ' := by
  constructor
  · rintro ⟨g, hg⟩
    have hcard_ℓ := U_param_card p q hqf.out a ha ℓ
    have hcard_ℓ' := U_param_card p q hqf.out a ha ℓ'
    have hle_ℓ := U_param_le_torusD p q a ℓ
    have hle_ℓ' := U_param_le_torusD p q a ℓ'
    have hcase := conj_diag_subgroup_either_eq_or_swap p hqf.out hq2
      hle_ℓ hle_ℓ' hcard_ℓ hcard_ℓ' hg
    rcases hcase with heq | heq
    · -- U_param ℓ = U_param ℓ'.
      left; exact U_param_injective p q a ha heq
    · -- heq : U_param ℓ' = (U_param ℓ).map (conj σ).
      -- Rewrite RHS with U_param_conj_swap to get U_param (swapIdx ℓ).
      right
      rw [U_param_conj_swap p q hq2 hpq hdvd a ha ℓ] at heq
      -- heq : U_param ℓ' = U_param (swapIdx ℓ).
      have h_inj : ℓ' = swapIdx q ℓ := U_param_injective p q a ha heq
      rw [h_inj, swapIdx_involutive]
  · intro h
    rcases h with h | h
    · subst h; exact Subgroup.IsConjGp.refl _
    · refine ⟨swapMat p, ?_⟩
      rw [h, U_param_conj_swap p q hq2 hpq hdvd a ha (swapIdx q ℓ'), swapIdx_involutive]

/-- The number of GLF-conjugacy classes of order-q subgroups equals the number
of orbits of `swapIdx` on `Fin q ⊕ Unit`. -/
private lemma numConjClasses_eq_swapOrbits (p q : ℕ) [Fact p.Prime] [hqf : Fact q.Prime]
    (hq2 : 2 < q) (hpq : p ≠ q) (hdvd : q ∣ (p - 1)) :
    numConjClassesOfOrder (GLF p) q = Nat.card (Quotient (swapOrbitSetoid q)) := by
  classical
  haveI : Fact q.Prime := hqf
  unfold numConjClassesOfOrder
  -- Get a base unit a of order q.
  obtain ⟨a, ha⟩ := exists_unit_order_q p q hqf.out hpq hdvd
  -- Build the Equiv between Quotient swapOrbitSetoid and Quotient ((subgroupConjSetoid).comap _).
  set S := subgroupsOfOrder (GLF p) q
  -- Map: ℓ ↦ ⟨U_param a ℓ, _⟩ : S
  let toS : Fin q ⊕ Unit → S := fun ℓ => ⟨U_param p q a ℓ, U_param_card p q hqf.out a ha ℓ⟩
  -- Quotient map: S → Quotient ((conjSetoid).comap _)
  let proj : S → Quotient ((subgroupConjSetoid (GLF p)).comap (fun H : S => (H : Subgroup (GLF p)))) :=
    Quotient.mk _
  -- Composite: Fin q ⊕ Unit → Quotient.
  -- This composite respects swapOrbitSetoid.
  let f : Fin q ⊕ Unit → Quotient ((subgroupConjSetoid (GLF p)).comap
      (fun H : S => (H : Subgroup (GLF p)))) := proj ∘ toS
  have hresp : ∀ ℓ ℓ', (swapOrbitSetoid q).r ℓ ℓ' → f ℓ = f ℓ' := by
    intro ℓ ℓ' h
    -- Need: ⟦U_param ℓ⟧ = ⟦U_param ℓ'⟧. By Uparam_conj_iff_swap.
    apply Quotient.sound
    show Subgroup.IsConjGp (U_param p q a ℓ) (U_param p q a ℓ')
    exact (Uparam_conj_iff_swap p q hq2 hpq hdvd a ha ℓ ℓ').mpr h
  -- Lift f to Quotient swapOrbitSetoid.
  let fLift : Quotient (swapOrbitSetoid q) → Quotient ((subgroupConjSetoid (GLF p)).comap
      (fun H : S => (H : Subgroup (GLF p)))) :=
    Quotient.lift f hresp
  -- Show fLift is bijective.
  have hbij : Function.Bijective fLift := by
    refine ⟨?_, ?_⟩
    · -- Injective.
      intro x y hxy
      induction x using Quotient.ind with | _ ℓ =>
      induction y using Quotient.ind with | _ ℓ' =>
      apply Quotient.sound
      -- hxy : f ℓ = f ℓ'. Need swapOrbitSetoid.r ℓ ℓ'.
      have : Quotient.mk _ (toS ℓ) = Quotient.mk _ (toS ℓ') := hxy
      have hconj : Subgroup.IsConjGp (U_param p q a ℓ) (U_param p q a ℓ') := Quotient.exact this
      exact (Uparam_conj_iff_swap p q hq2 hpq hdvd a ha ℓ ℓ').mp hconj
    · -- Surjective: every order-q subgroup is conjugate to a U_param ℓ.
      intro x
      induction x using Quotient.ind with | _ H =>
      obtain ⟨H_sub, hH⟩ := H
      change Nat.card H_sub = q at hH
      -- Get g such that H.map (conj g) ≤ torusD.
      obtain ⟨g, hg⟩ := exists_conj_into_torusD p q hqf.out hq2 hpq hdvd hH
      -- Apply every_torusD_order_q_eq_Uparam.
      have hcard_map : Nat.card (H_sub.map (MulAut.conj g).toMonoidHom) = q := by
        have hequiv : H_sub ≃* H_sub.map (MulAut.conj g).toMonoidHom :=
          Subgroup.equivMapOfInjective H_sub _ (MulAut.conj g).injective
        have := Nat.card_eq_of_bijective hequiv hequiv.bijective
        omega
      obtain ⟨ℓ, hℓ⟩ := every_torusD_order_q_eq_Uparam p q a ha hg hcard_map
      -- ⟦U_param ℓ⟧ = ⟦H_sub⟧ in conj quotient (because H_sub is conjugate to its conj).
      refine ⟨Quotient.mk _ ℓ, ?_⟩
      change Quotient.mk _ (toS ℓ) = Quotient.mk _ ⟨H_sub, hH⟩
      apply Quotient.sound
      -- Need: IsConjGp (U_param ℓ) H_sub.
      show Subgroup.IsConjGp (U_param p q a ℓ) H_sub
      -- We have hℓ : H_sub.map (conj g) = U_param ℓ.
      -- So U_param ℓ = H_sub.map (conj g), i.e., H_sub is conjugate to U_param ℓ.
      -- We want IsConjGp (U_param ℓ) H_sub, i.e., H_sub = (U_param ℓ).map (conj h) for some h.
      -- Use conj g⁻¹: (U_param ℓ).map (conj g⁻¹) = H_sub.
      refine ⟨g⁻¹, ?_⟩
      rw [← hℓ]
      rw [Subgroup.map_map]
      have : ((MulAut.conj g⁻¹).toMonoidHom).comp ((MulAut.conj g).toMonoidHom) =
             MonoidHom.id _ := by
        ext x; simp [MulAut.conj_apply, mul_assoc]
      rw [this, Subgroup.map_id]
  -- Conclude via cardinality of equiv.
  have hequiv : Quotient (swapOrbitSetoid q) ≃
      Quotient ((subgroupConjSetoid (GLF p)).comap (fun H : S => (H : Subgroup (GLF p)))) :=
    Equiv.ofBijective fLift hbij
  exact (Nat.card_eq_of_bijective fLift hbij).symm

/-- For `q > 2` prime, fixed points of `swapIdx` on `Fin q ⊕ Unit` are exactly
`inl 1` and `inl (q-1)`. -/
private lemma swapIdx_fixedPoints (q : ℕ) [hqf : Fact q.Prime] (hq2 : 2 < q) :
    ∀ ℓ : Fin q ⊕ Unit, swapIdx q ℓ = ℓ ↔
      ℓ = Sum.inl ⟨1, by have := hqf.out.one_lt; omega⟩ ∨
      ℓ = Sum.inl ⟨q - 1, by have := hqf.out.one_lt; omega⟩ := by
  haveI : NeZero q := ⟨hqf.out.ne_zero⟩
  intro ℓ
  rcases ℓ with i | ⟨⟩
  · -- inl i case
    by_cases hi : i.val = 0
    · -- i.val = 0 → swapIdx (inl 0) = inr (). Never equal to inl _.
      simp only [Sum.inl.injEq]
      have h1 : swapIdx q (Sum.inl i) = Sum.inr () := by
        change (if i.val = 0 then Sum.inr () else _) = Sum.inr ()
        rw [if_pos hi]
      constructor
      · intro h; rw [h1] at h; exact absurd h (by simp)
      · intro h
        rcases h with h | h
        · -- i = ⟨1, _⟩. Then i.val = 1 ≠ 0.
          have hi1 : i.val = 1 := by rw [h]
          omega
        · -- i = ⟨q-1, _⟩. Then i.val = q - 1 ≠ 0 since q > 2.
          have hi1 : i.val = q - 1 := by rw [h]
          omega
    · -- i.val ≠ 0
      have hi_ne : (i.val : ZMod q) ≠ 0 := by
        intro h
        rw [ZMod.natCast_eq_zero_iff] at h
        have h1 : i.val < q := i.isLt
        exact hi (Nat.eq_zero_of_dvd_of_lt h h1)
      have h1 : swapIdx q (Sum.inl i) =
          Sum.inl ⟨((i.val : ZMod q)⁻¹).val, ZMod.val_lt _⟩ := by
        change (if i.val = 0 then Sum.inr () else _) = _
        rw [if_neg hi]
      rw [h1]
      -- swapIdx (inl i) = inl i iff ((i⁻¹).val) = i.val iff i⁻¹ = i iff i^2 = 1.
      -- For Fin q with q prime, units of ZMod q have order dividing q-1. i^2 = 1 → i = ±1.
      haveI : Fact q.Prime := hqf
      haveI : Fact (1 < q) := ⟨hqf.out.one_lt⟩
      -- Helper for `(-1 : ZMod q).val = q - 1`.
      have hneg_one_val : (-1 : ZMod q).val = q - 1 := by
        rw [ZMod.neg_val]
        simp [show (1 : ZMod q) ≠ 0 from one_ne_zero, ZMod.val_one]
      have hone_val : (1 : ZMod q).val = 1 := ZMod.val_one q
      constructor
      · intro heq
        have hval_eq : ((i.val : ZMod q)⁻¹).val = i.val := by
          have hsum := Sum.inl.inj heq
          exact (Fin.ext_iff.mp hsum)
        -- From hval_eq: ((i⁻¹).val : ZMod q) = i, so i⁻¹ = i.
        have hinv_eq : (i.val : ZMod q)⁻¹ = (i.val : ZMod q) := by
          have : (((((i.val : ZMod q)⁻¹).val : ℕ) : ZMod q)) = (i.val : ZMod q) := by
            rw [hval_eq]
          rw [ZMod.natCast_val, ZMod.cast_id] at this
          exact this
        -- i^2 = 1.
        have hsq : (i.val : ZMod q)^2 = 1 := by
          have h1 := ZMod.mul_inv_of_unit (i.val : ZMod q) (Ne.isUnit hi_ne)
          rw [hinv_eq] at h1
          rw [sq]; exact h1
        -- (i - 1)(i + 1) = 0 in ZMod q.
        have hfactor : ((i.val : ZMod q) - 1) * ((i.val : ZMod q) + 1) = 0 := by
          have : ((i.val : ZMod q) - 1) * ((i.val : ZMod q) + 1) =
                 (i.val : ZMod q)^2 - 1 := by ring
          rw [this, hsq]; ring
        rcases mul_eq_zero.mp hfactor with h | h
        · -- (i - 1) = 0 → i = 1.
          have hi_eq_one : (i.val : ZMod q) = 1 := by
            have : (i.val : ZMod q) - 1 + 1 = 0 + 1 := by rw [h]
            simpa using this
          have hcast : (i.val : ZMod q).val = (1 : ZMod q).val := by rw [hi_eq_one]
          rw [ZMod.val_natCast] at hcast
          rw [Nat.mod_eq_of_lt i.isLt, hone_val] at hcast
          left
          congr 1
          exact Fin.ext hcast
        · -- (i + 1) = 0 → i = -1.
          have hi_eq_neg_one : (i.val : ZMod q) = -1 := by
            have : (i.val : ZMod q) + 1 + (-1) = 0 + (-1) := by rw [h]
            simpa using this
          have hcast : (i.val : ZMod q).val = (-1 : ZMod q).val := by rw [hi_eq_neg_one]
          rw [ZMod.val_natCast] at hcast
          rw [Nat.mod_eq_of_lt i.isLt, hneg_one_val] at hcast
          right
          congr 1
          exact Fin.ext hcast
      · intro h
        rcases h with h | h
        · -- ℓ = inl 1, swapIdx ℓ = inl ((1 : ZMod q)⁻¹).val = inl 1.
          have hi1 : i.val = 1 := Fin.val_eq_of_eq (Sum.inl.inj h)
          have h_inv : ((i.val : ZMod q)⁻¹).val = i.val := by
            rw [hi1, Nat.cast_one, inv_one, hone_val]
          congr 1
          exact Fin.ext h_inv
        · -- ℓ = inl (q-1), swapIdx ℓ = inl ((q-1 : ZMod q)⁻¹).val = inl (q-1).
          have hi1 : i.val = q - 1 := Fin.val_eq_of_eq (Sum.inl.inj h)
          have hcast_neg : ((q - 1 : ℕ) : ZMod q) = -1 := by
            have hqpos : 1 ≤ q := hqf.out.one_lt.le
            have : ((q - 1 : ℕ) : ZMod q) = ((q : ℕ) : ZMod q) - ((1 : ℕ) : ZMod q) := by
              rw [Nat.cast_sub hqpos]
            rw [this, ZMod.natCast_self]
            simp
          have h_inv : ((i.val : ZMod q)⁻¹).val = i.val := by
            rw [hi1, hcast_neg]
            rw [show (-1 : ZMod q)⁻¹ = -1 from by simp]
            rw [hneg_one_val]
          congr 1
          exact Fin.ext h_inv
  · -- inr () case: swapIdx (inr ()) = inl 0 ≠ inr (). Also ℓ ≠ inl _.
    constructor
    · intro h
      change Sum.inl (⟨0, hqf.out.pos⟩ : Fin q) = Sum.inr () at h
      exact absurd h (by simp)
    · intro h
      rcases h with h | h <;> exact absurd h (by simp)

/-- For odd `q` (in particular prime > 2), the orbits of `swapIdx` on `Fin q ⊕ Unit`
have a specific structure useful for counting. -/
private lemma swapIdx_orbit_count (q : ℕ) [hqf : Fact q.Prime] (hq2 : 2 < q) :
    Nat.card (Quotient (swapOrbitSetoid q)) = (q + 3) / 2 := by
  classical
  -- q is odd since q > 2 is prime.
  have hq_odd : ¬ 2 ∣ q := by
    intro h2
    have hq_eq : 2 = q := (hqf.out.eq_one_or_self_of_dvd 2 h2).resolve_left (by norm_num)
    omega
  -- The setoid is decidable.
  haveI : DecidableEq (Fin q ⊕ Unit) := instDecidableEqSum
  haveI : DecidableRel (swapOrbitSetoid q).r :=
    fun a b => decidable_of_iff (a = b ∨ a = swapIdx q b) Iff.rfl
  haveI : Fintype (Quotient (swapOrbitSetoid q)) := Quotient.fintype _
  rw [Nat.card_eq_fintype_card]
  -- Build a function: every orbit is identified by its canonical representative.
  -- Use sum_card_fiberwise: |α| = Σ orbits (orbit size).
  -- Orbit sizes: 1 (fixed) or 2 (non-fixed). Fixed points = 2.
  set f : Fin q ⊕ Unit → Quotient (swapOrbitSetoid q) := Quotient.mk _ with hf_def
  -- |Fin q ⊕ Unit| = q + 1.
  have hcard_dom : Fintype.card (Fin q ⊕ Unit) = q + 1 := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  -- Σ orbits (fiber.card) = q + 1.
  have hsum : ∑ o : Quotient (swapOrbitSetoid q),
      (Finset.univ.filter (fun ℓ : Fin q ⊕ Unit => f ℓ = o)).card = q + 1 := by
    rw [← hcard_dom, ← Finset.card_univ]
    exact (Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ)
      (H := fun x _ => Finset.mem_univ _)).symm
  -- Each fiber has size 1 or 2: 1 if fixed (orbit rep is fixed), else 2.
  -- More precisely: the fiber over ⟦ℓ⟧ has size 1 if ℓ = swapIdx ℓ else 2.
  have hfib_size : ∀ ℓ : Fin q ⊕ Unit,
      (Finset.univ.filter (fun x : Fin q ⊕ Unit => f x = f ℓ)).card =
      if ℓ = swapIdx q ℓ then 1 else 2 := by
    intro ℓ
    by_cases hfix : ℓ = swapIdx q ℓ
    · -- fiber is {ℓ}
      rw [if_pos hfix]
      have : (Finset.univ.filter (fun x : Fin q ⊕ Unit => f x = f ℓ)) = {ℓ} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                   Finset.mem_singleton]
        constructor
        · intro h
          -- f x = f ℓ → x ~ ℓ → x = ℓ ∨ x = swapIdx ℓ → x = ℓ (using hfix).
          have hr : (swapOrbitSetoid q).r x ℓ := Quotient.exact h
          rcases hr with hr | hr
          · exact hr
          · rw [hr, ← hfix]
        · intro h; rw [h]
      rw [this, Finset.card_singleton]
    · -- fiber is {ℓ, swapIdx ℓ}
      rw [if_neg hfix]
      have hne : ℓ ≠ swapIdx q ℓ := hfix
      have : (Finset.univ.filter (fun x : Fin q ⊕ Unit => f x = f ℓ)) =
             {ℓ, swapIdx q ℓ} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                   Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro h
          have hr : (swapOrbitSetoid q).r x ℓ := Quotient.exact h
          rcases hr with hr | hr
          · left; exact hr
          · right; exact hr
        · rintro (rfl | rfl)
          · rfl
          · apply Quotient.sound
            right; rfl
      rw [this]
      rw [Finset.card_insert_of_notMem (by simp [hne])]
      simp
  -- Use this to rewrite hsum.
  -- The fiber over ⟦ℓ⟧ is the same as the fiber over ⟦ℓ'⟧ if ⟦ℓ⟧ = ⟦ℓ'⟧.
  -- So we can characterize fibers by their orbit reps.
  -- Σ orbits (1 if fixed orbit else 2) = q + 1.
  have hfix_card_orbit : ∀ o : Quotient (swapOrbitSetoid q),
      (Finset.univ.filter (fun ℓ : Fin q ⊕ Unit => f ℓ = o)).card =
      if (o.out = swapIdx q o.out) then 1 else 2 := by
    intro o
    have heq : f o.out = o := Quotient.out_eq o
    have h := hfib_size o.out
    rw [heq] at h
    exact h
  rw [Finset.sum_congr rfl (fun o _ => hfix_card_orbit o)] at hsum
  -- So: Σ orbits (1 if fixed else 2) = q + 1.
  -- The fixed orbits in `Quotient swapOrbitSetoid` ↔ fixed points of swapIdx.
  -- Specifically: bijection {ℓ : ℓ = swapIdx ℓ} ≃ {o : o.out = swapIdx o.out}.
  -- And we know fixed points are exactly inl 1 and inl (q-1), so 2 of them.
  have hcard_fixed_pts : Fintype.card { ℓ : Fin q ⊕ Unit // ℓ = swapIdx q ℓ } = 2 := by
    haveI : Fintype { ℓ : Fin q ⊕ Unit // ℓ = swapIdx q ℓ } := Subtype.fintype _
    have hone : (Sum.inl ⟨1, by have := hqf.out.one_lt; omega⟩ : Fin q ⊕ Unit) ≠
                (Sum.inl ⟨q - 1, by have := hqf.out.one_lt; omega⟩) := by
      intro h
      have : (1 : ℕ) = q - 1 := Fin.val_eq_of_eq (Sum.inl.inj h)
      omega
    -- The fixed points are exactly inl 1 and inl (q-1).
    rw [Fintype.card_subtype]
    have hfilter : (Finset.univ.filter (fun ℓ : Fin q ⊕ Unit => ℓ = swapIdx q ℓ)) =
        {Sum.inl ⟨1, by have := hqf.out.one_lt; omega⟩,
         Sum.inl ⟨q - 1, by have := hqf.out.one_lt; omega⟩} := by
      ext ℓ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                 Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro h
        have h' : swapIdx q ℓ = ℓ := h.symm
        exact (swapIdx_fixedPoints q hq2 ℓ).mp h'
      · rintro (h | h)
        · rw [h]
          exact ((swapIdx_fixedPoints q hq2 _).mpr (Or.inl rfl)).symm
        · rw [h]
          exact ((swapIdx_fixedPoints q hq2 _).mpr (Or.inr rfl)).symm
    rw [hfilter]
    rw [Finset.card_insert_of_notMem (by simp [hone])]
    simp
  -- Build the bijection {ℓ : ℓ = swapIdx ℓ} ≃ {o : Quotient // o.out = swapIdx o.out}.
  -- Since we used Quotient.out, this might be annoying. Let me just bound things.
  -- Actually let me skip the bijection and just observe:
  -- The set of orbits = (number of size-1 orbits) + (number of size-2 orbits).
  -- |α| = #(size-1 orbits) * 1 + #(size-2 orbits) * 2.
  -- Each size-1 orbit corresponds to exactly one fixed point.
  -- So #(size-1 orbits) = 2 (the fixed points).
  -- Thus q + 1 = 2 + 2*#(size-2 orbits), so #size-2 orbits = (q-1)/2.
  -- Total orbits = 2 + (q-1)/2 = (q+3)/2 (using q odd).
  -- Now we encode this.
  set fixOrbits := Finset.univ.filter (fun o : Quotient (swapOrbitSetoid q) =>
    o.out = swapIdx q o.out) with hfixOrbits_def
  set nonFixOrbits := Finset.univ.filter (fun o : Quotient (swapOrbitSetoid q) =>
    o.out ≠ swapIdx q o.out) with hnonFixOrbits_def
  have hsplit : (Finset.univ : Finset (Quotient (swapOrbitSetoid q))) =
                fixOrbits ∪ nonFixOrbits := by
    ext o
    simp [fixOrbits, nonFixOrbits]
    tauto
  have hdisj : Disjoint fixOrbits nonFixOrbits := by
    simp [Finset.disjoint_filter, fixOrbits, nonFixOrbits]
  have hcard_split : Fintype.card (Quotient (swapOrbitSetoid q)) =
                     fixOrbits.card + nonFixOrbits.card := by
    rw [← Finset.card_univ, hsplit, Finset.card_union_of_disjoint hdisj]
  -- Rewrite hsum using the split.
  have hsum_split : ∑ o : Quotient (swapOrbitSetoid q),
      (if (o.out = swapIdx q o.out) then (1 : ℕ) else 2) =
      fixOrbits.card * 1 + nonFixOrbits.card * 2 := by
    rw [show (Finset.univ : Finset (Quotient (swapOrbitSetoid q))) =
            fixOrbits ∪ nonFixOrbits from hsplit]
    rw [Finset.sum_union hdisj]
    congr 1
    · rw [Finset.sum_ite_of_true (fun o ho => by
        simp [fixOrbits] at ho; exact ho), Finset.sum_const, Nat.smul_one_eq_cast]
      simp
    · rw [Finset.sum_ite_of_false (fun o ho => by
        simp [nonFixOrbits] at ho; exact ho)]
      rw [Finset.sum_const]
      ring
  rw [hsum_split] at hsum
  -- |fix orbits| = 2.
  have hfix_orbits_card : fixOrbits.card = 2 := by
    -- Bijection between fixOrbits and {ℓ : ℓ = swapIdx ℓ}: send fixed orbit o to o.out.
    -- Inverse: send ℓ to ⟦ℓ⟧.
    have hequiv : fixOrbits ≃ { ℓ : Fin q ⊕ Unit // ℓ = swapIdx q ℓ } := by
      refine ⟨fun o => ⟨o.1.out, by
        have h2 : o.1 ∈ fixOrbits := o.2
        simp only [hfixOrbits_def, Finset.mem_filter, Finset.mem_univ, true_and] at h2
        exact h2⟩,
              fun ⟨ℓ, hℓ⟩ => ⟨Quotient.mk _ ℓ, ?_⟩, ?_, ?_⟩
      · simp [fixOrbits]
        -- ⟦ℓ⟧.out = swapIdx ⟦ℓ⟧.out.
        -- ⟦ℓ⟧.out ~ ℓ, so ⟦ℓ⟧.out = ℓ ∨ ⟦ℓ⟧.out = swapIdx ℓ.
        have hQ : Quotient.mk (swapOrbitSetoid q) (Quotient.out
          (Quotient.mk (swapOrbitSetoid q) ℓ)) =
          Quotient.mk (swapOrbitSetoid q) ℓ := Quotient.out_eq _
        have hr := Quotient.exact hQ
        rcases hr with hr | hr
        · rw [hr]; exact hℓ
        · rw [hr]; rw [swapIdx_involutive]; exact hℓ.symm
      · -- left inverse: applied to o gives o.
        intro o
        ext
        simp only
        exact Quotient.out_eq _
      · -- right inverse
        intro ⟨ℓ, hℓ⟩
        ext
        simp only
        -- Goal: ((⟦ℓ⟧.out : Fin q ⊕ Unit) = ℓ).
        -- ⟦ℓ⟧.out ~ ℓ, so out = ℓ ∨ out = swapIdx ℓ = ℓ (using hℓ).
        have hQ : Quotient.mk (swapOrbitSetoid q) (Quotient.out
          (Quotient.mk (swapOrbitSetoid q) ℓ)) =
          Quotient.mk (swapOrbitSetoid q) ℓ := Quotient.out_eq _
        have hr := Quotient.exact hQ
        rcases hr with hr | hr
        · exact hr
        · rw [hr]; exact hℓ.symm
    rw [show fixOrbits.card = Fintype.card fixOrbits from (Fintype.card_coe _).symm]
    rw [Fintype.card_congr hequiv]
    exact hcard_fixed_pts
  rw [hfix_orbits_card] at hsum
  -- hsum : 2 * 1 + nonFixOrbits.card * 2 = q + 1
  -- i.e., nonFixOrbits.card = (q - 1)/2.
  have hnonfix_card : nonFixOrbits.card * 2 = q - 1 := by omega
  -- Use that q is odd: q - 1 = 2k.
  -- (q + 3)/2 = (q - 1 + 4)/2 = (q-1)/2 + 2.
  rw [hcard_split, hfix_orbits_card]
  -- Goal: 2 + nonFixOrbits.card = (q + 3) / 2
  have hq_odd_nat : Odd q := hqf.out.odd_of_ne_two (by omega)
  obtain ⟨k, hk⟩ := hq_odd_nat
  -- q = 2k + 1.  Then nonFixOrbits.card = k, and (q+3)/2 = k+2.
  have hk_pos : k ≥ 1 := by omega
  have hnonfix_eq_k : nonFixOrbits.card = k := by omega
  have h_target : (q + 3) / 2 = k + 2 := by omega
  rw [hnonfix_eq_k, h_target]
  omega

/-- Case `q ∣ p-1`: there are exactly `(q+3)/2` conjugacy classes of
subgroups of order `q` in `GL_2(F_p)`. -/
lemma case_q_dvd_p_minus_one (p q : ℕ) [Fact p.Prime] (hq : q.Prime)
    (hq2 : 2 < q) (hpq : p ≠ q) (hdvd : q ∣ (p - 1)) :
    numConjClassesOfOrder (GLF p) q = (q + 3) / 2 := by
  haveI : Fact q.Prime := ⟨hq⟩
  rw [numConjClasses_eq_swapOrbits p q hq2 hpq hdvd]
  exact swapIdx_orbit_count q hq2

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
