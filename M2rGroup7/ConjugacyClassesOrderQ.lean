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
