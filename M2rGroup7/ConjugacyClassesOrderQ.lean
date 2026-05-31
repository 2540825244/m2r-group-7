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

/-- In a finite cyclic group, any two subgroups of the same order are equal. -/
private lemma unique_subgroup_of_card_in_cyclic
    {G : Type*} [Group G] [Finite G] [IsCyclic G] {n : ℕ} (hn : 0 < n)
    (H K : Subgroup G) (hH : Nat.card H = n) (hK : Nat.card K = n) : H = K := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype H := Fintype.ofFinite _
  haveI : Fintype K := Fintype.ofFinite _
  -- Both H and K consist of elements x with x^n = 1.
  set S : Finset G := (Finset.univ : Finset G).filter (fun x => x ^ n = 1) with hSdef
  have hcardS : S.card ≤ n := IsCyclic.card_pow_eq_one_le hn
  -- For x ∈ H: x^n = 1.
  have hcardH : Fintype.card H = n := by rw [← Nat.card_eq_fintype_card]; exact hH
  have hcardK : Fintype.card K = n := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hxn (H' : Subgroup G) (hH' : Nat.card H' = n) {x : G} (hx : x ∈ H') :
      x ^ n = 1 := by
    have hpow : (⟨x, hx⟩ : H') ^ n = 1 := by
      rw [← hH']
      exact pow_card_eq_one'
    have hpow2 : ((⟨x, hx⟩ : H')^ n : G) = ((1 : H') : G) := by
      exact_mod_cast hpow
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
    rw [Set.toFinset_card]
    convert hcardH using 1
  have hKcard : (K : Set G).toFinset.card = n := by
    rw [Set.toFinset_card]
    convert hcardK using 1
  -- Both have card n, both ⊆ S which has card ≤ n. So both = S.
  have hHeqS : (H : Set G).toFinset = S := by
    apply Finset.eq_of_subset_of_card_le hHsub
    rw [hHcard]; exact hcardS
  have hKeqS : (K : Set G).toFinset = S := by
    apply Finset.eq_of_subset_of_card_le hKsub
    rw [hKcard]; exact hcardS
  have hHK : (H : Set G).toFinset = (K : Set G).toFinset := hHeqS.trans hKeqS.symm
  ext x
  have : x ∈ (H : Set G).toFinset ↔ x ∈ (K : Set G).toFinset := by rw [hHK]
  simpa [Set.mem_toFinset] using this

/-- Two subgroups of `G` of the same order, both contained in a cyclic subgroup `S`,
are equal. -/
private lemma unique_subgroup_of_card_in_cyclic_le
    {G : Type*} [Group G] [Finite G] {S : Subgroup G} [IsCyclic S]
    {n : ℕ} (hn : 0 < n)
    {H K : Subgroup G} (hH : H ≤ S) (hK : K ≤ S)
    (hHcard : Nat.card H = n) (hKcard : Nat.card K = n) :
    H = K := by
  -- Move H, K into S as subgroups of S, then apply uniqueness within cyclic S.
  let H' : Subgroup S := H.subgroupOf S
  let K' : Subgroup S := K.subgroupOf S
  -- Cardinalities
  have hH'card : Nat.card H' = n := by
    have hHfin : Nat.card H = Nat.card H' := by
      apply Nat.card_eq_of_bijective
        (fun (x : H) => (⟨⟨x.1, hH x.2⟩, x.2⟩ : H'))
      refine ⟨fun x y hxy => Subtype.ext (by exact congrArg (·.1.1) hxy), ?_⟩
      rintro ⟨⟨y, hyS⟩, hy⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    rw [← hHfin]; exact hHcard
  have hK'card : Nat.card K' = n := by
    have hKfin : Nat.card K = Nat.card K' := by
      apply Nat.card_eq_of_bijective
        (fun (x : K) => (⟨⟨x.1, hK x.2⟩, x.2⟩ : K'))
      refine ⟨fun x y hxy => Subtype.ext (by exact congrArg (·.1.1) hxy), ?_⟩
      rintro ⟨⟨y, hyS⟩, hy⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    rw [← hKfin]; exact hKcard
  have hHK' : H' = K' :=
    unique_subgroup_of_card_in_cyclic hn H' K' hH'card hK'card
  -- Lift back
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

/-- Case `q ∣ p-1`: there are exactly `(q+3)/2` conjugacy classes of
subgroups of order `q` in `GL_2(F_p)`.

Proof outline (informal): pick `a ∈ (ZMod p)ˣ` of order `q`. The order-q
subgroups of `torusD p` are exactly the `q+1` cyclic groups
`U_ℓ = ⟨diag(a, a^ℓ)⟩` for `ℓ ∈ Fin q` and `U_∞ = ⟨diag(1, a)⟩`. By the
Sylow argument (analogous to `case_q_dvd_p_plus_one`), every order-q
subgroup of `GLF p` is conjugate to some `U_ℓ`. Using
`conj_diag_subgroup_either_eq_or_swap` plus `swap_conj_diag`, two
`U_ℓ`-subgroups are `GLF`-conjugate iff `σ`-conjugate, where `σ = swapMat`
acts as `inl 0 ↔ inr ()` and `inl ℓ ↔ inl (ℓ⁻¹ mod q)` for `ℓ ≠ 0`. The
involution has 3 fixed orbits (`inl 1`, `inl (q-1)`, the pair
`{inl 0, inr ()}`) and `(q-3)/2` size-2 orbits among `inl ℓ` with `ℓ ∉ {0, 1, -1}`,
totalling `3 + (q-3)/2 = (q+3)/2`.

This proof is left as a `sorry`; the helpers `U_param`, `U_param_card`,
`U_param_le_torusD`, `exists_natpow_of_orderDvd`, `orderOf_q_torusD_eq`,
and `exists_conj_into_torusD` provide partial scaffolding. -/
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
