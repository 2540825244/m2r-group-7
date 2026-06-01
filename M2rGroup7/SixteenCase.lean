import «M2rGroup7».SmallGroupsLibrary
import «M2rGroup7».PqCase
import Mathlib

namespace OrderSixteen.Prelim

/-- Center of a $p$-group is nontrivial: if $G$ is a nontrivial finite $p$-group
then $Z(G)$ is nontrivial. Direct wrapper around `IsPGroup.center_nontrivial`. -/
theorem pgroup_center_nontrivial {p : ℕ} [Fact p.Prime] {G : Type*}
    [Group G] [Finite G] [Nontrivial G] (hp : IsPGroup p G) :
    Nontrivial (Subgroup.center G) :=
  hp.center_nontrivial

/-- For a finite group $G$, $|Z(G)|$ divides $|G|$. Direct wrapper around
`Subgroup.card_subgroup_dvd_card` applied to the center. -/
theorem center_divides_card (G : Type*) [Group G] [Finite G] :
    Nat.card (Subgroup.center G) ∣ Nat.card G :=
  Subgroup.card_subgroup_dvd_card (Subgroup.center G)

/-- Divisors of $16 = 2^4$ are powers of $2$ with exponent at most $4$. -/
theorem two_power_divisors {d : ℕ} (h : d ∣ 16) :
    ∃ k ≤ 4, d = 2 ^ k := by
  rw [show (16 : ℕ) = 2 ^ 4 from by norm_num] at h
  exact (Nat.dvd_prime_pow Nat.prime_two).mp h

/-- If $|G| = 16$ then $G$ is a $2$-group. Direct wrapper around
`IsPGroup.of_card` with $16 = 2^4$. -/
theorem pgroup_of_card_sixteen {G : Type*} [Group G] (h : Nat.card G = 16) :
    IsPGroup 2 G :=
  IsPGroup.of_card (show Nat.card G = 2 ^ 4 from by rw [h]; norm_num)

/-- A group of prime cardinality is cyclic. Direct wrapper around
Mathlib's `isCyclic_of_prime_card`. -/
theorem cyclic_of_prime_card {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (h : Nat.card G = p) : IsCyclic G :=
  isCyclic_of_prime_card h

/-- If every element of $G$ satisfies $x^2 = 1$, then $G$ is abelian.
Wrapper around `Commute.of_orderOf_dvd_two`. -/
theorem order2_implies_abelian {G : Type*} [Group G]
    (h : ∀ x : G, x ^ 2 = 1) : ∀ a b : G, a * b = b * a := fun a b =>
  (Commute.of_orderOf_dvd_two (fun g => orderOf_dvd_iff_pow_eq_one.mpr (h g)) a b)

/-- Fundamental theorem of finite abelian groups: every finite abelian group
(written additively) is isomorphic to a direct sum of cyclic groups of
prime-power order. Wrapper around `AddCommGroup.equiv_directSum_zmod_of_finite`. -/
theorem fundamental_finite_abelian (G : Type*) [AddCommGroup G] [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℕ) (_ : ∀ i, Nat.Prime (p i)) (e : ι → ℕ),
      Nonempty (G ≃+ DirectSum ι (fun i => ZMod (p i ^ e i))) :=
  AddCommGroup.equiv_directSum_zmod_of_finite G

/-- A group $G$ is commutative iff $Z(G) = \top$. -/
theorem abelian_iff_center_top (G : Type*) [Group G] :
    (∀ a b : G, a * b = b * a) ↔ Subgroup.center G = ⊤ := by
  refine ⟨fun h => ?_, fun h a b => ?_⟩
  · rw [Subgroup.eq_top_iff']
    intro x
    rw [Subgroup.mem_center_iff]
    intro g
    exact h g x
  · have ha : a ∈ Subgroup.center G := by rw [h]; trivial
    exact (Subgroup.mem_center_iff.mp ha b).symm

/-- If $G/Z(G)$ is cyclic, then $G$ is commutative. Wrapper around
`commutative_of_cyclic_center_quotient` applied to the canonical surjection
$G \to G / Z(G)$. -/
theorem cyclic_center_quotient_abelian (G : Type*) [Group G]
    (h : IsCyclic (G ⧸ Subgroup.center G)) :
    ∀ a b : G, a * b = b * a :=
  commutative_of_cyclic_center_quotient (QuotientGroup.mk' (Subgroup.center G))
    (le_of_eq (QuotientGroup.ker_mk' _))

/-- If $G$ is a finite group then $|G/Z(G)| \cdot |Z(G)| = |G|$.
Wrapper around `Subgroup.index_mul_card` applied to the center, together with
the identification of $|G/Z(G)|$ with the index of $Z(G)$. -/
theorem quotient_by_center_card (G : Type*) [Group G] [Finite G] :
    Nat.card (G ⧸ Subgroup.center G) * Nat.card (Subgroup.center G) = Nat.card G := by
  rw [← Subgroup.index_eq_card]
  exact Subgroup.index_mul_card (Subgroup.center G)

/-- If $|G| = 16$ and $|Z(G)| = 4$, then $G/Z(G)$ is not cyclic. Otherwise, $G$
would be abelian, forcing $Z(G) = G$ and $|Z(G)| = 16$, contradicting
$|Z(G)| = 4$. -/
theorem order_four_quotient_not_cyclic {G : Type*} [Group G] [Finite G]
    (h_sixteen : Nat.card G = 16) (h_center : Nat.card (Subgroup.center G) = 4) :
    ¬ IsCyclic (G ⧸ Subgroup.center G) := by
  intro hcyc
  have h_comm : ∀ a b : G, a * b = b * a :=
    cyclic_center_quotient_abelian G hcyc
  have hcenter_top : Subgroup.center G = ⊤ :=
    (abelian_iff_center_top G).mp h_comm
  have h16 : Nat.card (Subgroup.center G) = 16 := by
    rw [hcenter_top, Nat.card_congr (Subgroup.topEquiv).toEquiv, h_sixteen]
  omega

/-- If $|G| = 16$ and $|Z(G)| = 2$, then $G/Z(G)$ is not cyclic. Otherwise, $G$
would be abelian, forcing $Z(G) = G$ and $|Z(G)| = 16$, contradicting
$|Z(G)| = 2$. -/
theorem order_eight_quotient_not_cyclic {G : Type*} [Group G] [Finite G]
    (h_sixteen : Nat.card G = 16) (h_center : Nat.card (Subgroup.center G) = 2) :
    ¬ IsCyclic (G ⧸ Subgroup.center G) := by
  intro hcyc
  have h_comm : ∀ a b : G, a * b = b * a :=
    cyclic_center_quotient_abelian G hcyc
  have hcenter_top : Subgroup.center G = ⊤ :=
    (abelian_iff_center_top G).mp h_comm
  have h16 : Nat.card (Subgroup.center G) = 16 := by
    rw [hcenter_top, Nat.card_congr (Subgroup.topEquiv).toEquiv, h_sixteen]
  omega

open scoped Pointwise in
/-- For finite subgroups $H$ and $K$ of a group $G$, the classical formula
$|H| \cdot |K| = |H \cap K| \cdot |HK|$. -/
theorem subgroup_product_card {G : Type*} [Group G] (H K : Subgroup G)
    [Finite H] [Finite K] :
    Nat.card (H : Set G) * Nat.card (K : Set G) =
      Nat.card (H ⊓ K : Subgroup G) * Nat.card ((H : Set G) * (K : Set G)) := by
  let f : H → G ⧸ K := fun h => QuotientGroup.mk h.val
  have hrange : Set.range f = QuotientGroup.mk '' (H : Set G) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨y.val, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩
  have hequiv : Nat.card (Quotient (Setoid.ker f)) =
      Nat.card (QuotientGroup.mk '' (H : Set G) : Set (G ⧸ K)) := by
    rw [← hrange]
    exact Nat.card_congr (Setoid.quotientKerEquivRange f)
  have hsetoid : Nat.card (Quotient (Setoid.ker f)) = Nat.card (H ⧸ K.subgroupOf H) := by
    refine Nat.card_congr (Quotient.congrRight ?_)
    intro a b
    simp only [Setoid.ker_def, f, QuotientGroup.eq]
    rw [QuotientGroup.leftRel_apply]
    rfl
  have hHK : Nat.card ((H : Set G) * (K : Set G)) =
      Nat.card K * Nat.card (QuotientGroup.mk '' (H : Set G) : Set (G ⧸ K)) :=
    Subgroup.card_mul_eq_card_subgroup_mul_card_quotient K (H : Set G)
  have hH : Nat.card H = Nat.card (H ⧸ K.subgroupOf H) * Nat.card (K.subgroupOf H) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hinter : Nat.card (K.subgroupOf H) = Nat.card (H ⊓ K : Subgroup G) := by
    have h1 : ((H ⊓ K).subgroupOf H) = K.subgroupOf H := by
      rw [show H ⊓ K = K ⊓ H from inf_comm _ _]
      exact Subgroup.inf_subgroupOf_right K H
    have h2 : Nat.card ((H ⊓ K).subgroupOf H) = Nat.card (H ⊓ K : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : (H ⊓ K) ≤ H)).toEquiv
    rw [← h1, h2]
  have hHsubtype : Nat.card (H : Set G) = Nat.card H := rfl
  have hKsubtype : Nat.card (K : Set G) = Nat.card K := rfl
  rw [hHsubtype, hKsubtype, hHK, ← hequiv, hsetoid]
  rw [hH, hinter]
  ring

/-- If $G/Z(G)$ is abelian, then the commutator $[g,h] = ghg^{-1}h^{-1}$ lies in
$Z(G)$ for all $g, h \in G$. -/
theorem commutator_in_center_when_quotient_abelian {G : Type*} [Group G]
    (h_abelian : ∀ a b : G ⧸ Subgroup.center G, a * b = b * a) (g h : G) :
    g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center G := by
  rw [← QuotientGroup.eq_one_iff]
  have heq : ((g * h * g⁻¹ * h⁻¹ : G) : G ⧸ Subgroup.center G) =
      (g : G ⧸ Subgroup.center G) * h * g⁻¹ * h⁻¹ := by
    simp
  rw [heq, h_abelian g h]
  simp [mul_assoc]

/-- If `|G| = 16`, `|Z(G)| = 4`, and `H ≤ G` is a subgroup of order 8
containing `Z(G)`, then `H` is abelian. -/
theorem gi_abelian_when_center_four {G : Type*} [Group G] [Finite G]
    (h_sixteen : Nat.card G = 16) (h_center : Nat.card (Subgroup.center G) = 4)
    (H : Subgroup G) (hH_card : Nat.card H = 8)
    (hH_contains : Subgroup.center G ≤ H) :
    ∀ a b : H, a * b = b * a := by
  -- View Z(G) as a subgroup of H.
  set Zin : Subgroup H := (Subgroup.center G).subgroupOf H with hZin
  -- Step 1: Zin ≤ Z(H).
  have hZin_le_center : Zin ≤ Subgroup.center H := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro h
    -- z.val ∈ Z(G), so it commutes with every element of G, in particular h.val.
    have hzG : (z : G) ∈ Subgroup.center G := hz
    have hcomm : (h : G) * (z : G) = (z : G) * (h : G) :=
      Subgroup.mem_center_iff.mp hzG (h : G)
    apply Subtype.ext
    change (h * z : H).val = (z * h : H).val
    push_cast
    exact hcomm
  -- Step 2: Nat.card Zin = 4.
  have hZin_card : Nat.card Zin = 4 := by
    have hequiv : Zin ≃* (Subgroup.center G) :=
      Subgroup.subgroupOfEquivOfLe hH_contains
    rw [Nat.card_congr hequiv.toEquiv, h_center]
  -- Step 3: Nat.card (H ⧸ Zin) = 2.
  have hQ_card : Nat.card (H ⧸ Zin) = 2 := by
    have h1 : Nat.card H = Nat.card (H ⧸ Zin) * Nat.card Zin :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup Zin
    rw [hH_card, hZin_card] at h1
    omega
  -- Step 4: H ⧸ Zin is cyclic (order 2 prime).
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hcyc : IsCyclic (H ⧸ Zin) := cyclic_of_prime_card hQ_card
  -- Step 5: Apply commutative_of_cyclic_center_quotient.
  exact commutative_of_cyclic_center_quotient (QuotientGroup.mk' Zin)
    (by rw [QuotientGroup.ker_mk']; exact hZin_le_center)

/-- If `a^2 ∈ Z(G)` and the commutator `[a,b] = a*b*a⁻¹*b⁻¹ ∈ Z(G)`, then
`[a,b]^2 = 1`. -/
theorem commutator_sq_eq_one_when_sq_central {G : Type*} [Group G] (a b : G)
    (h_sq_central : a ^ 2 ∈ Subgroup.center G)
    (h_comm_central : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center G) :
    (a * b * a⁻¹ * b⁻¹) ^ 2 = 1 := by
  -- Abbreviate the commutator. We use a local let-like definition that does NOT
  -- unfold under `rw`.
  let z : G := a * b * a⁻¹ * b⁻¹
  have hz_def : z = a * b * a⁻¹ * b⁻¹ := rfl
  -- Rewrite the goal in terms of z.
  change z ^ 2 = 1
  -- Extract centrality as "commutes with every element" statements.
  have hz : ∀ g : G, z * g = g * z := fun g =>
    (Subgroup.mem_center_iff.mp h_comm_central g).symm
  have ha2 : ∀ g : G, a ^ 2 * g = g * a ^ 2 := fun g =>
    (Subgroup.mem_center_iff.mp h_sq_central g).symm
  -- From the definition of z: a * b = z * (b * a).
  have hab : a * b = z * (b * a) := by
    rw [hz_def]; group
  -- Way 1: using a^2 central, a^2 * b = b * a^2.
  have way1 : a ^ 2 * b = b * a ^ 2 := ha2 b
  -- Way 2: expand using hab twice plus z central to get a^2 * b = z^2 * (b * a^2).
  have way2 : a ^ 2 * b = z ^ 2 * (b * a ^ 2) := by
    have e1 : a ^ 2 * b = a * (a * b) := by rw [sq, mul_assoc]
    have e2 : a * (a * b) = a * (z * (b * a)) := by rw [hab]
    have e3 : a * (z * (b * a)) = (a * z) * (b * a) := (mul_assoc a z (b * a)).symm
    have e4 : (a * z) * (b * a) = (z * a) * (b * a) := by rw [hz a]
    have e5 : (z * a) * (b * a) = z * (a * (b * a)) := mul_assoc z a (b * a)
    have e6 : a * (b * a) = (a * b) * a := (mul_assoc _ _ _).symm
    have e7 : z * (a * (b * a)) = z * ((a * b) * a) := by rw [e6]
    have e8 : z * ((a * b) * a) = z * ((z * (b * a)) * a) := by rw [hab]
    have e9 : z * ((z * (b * a)) * a) = z * (z * ((b * a) * a)) := by
      rw [mul_assoc z (b * a) a]
    have e10 : z * (z * ((b * a) * a)) = (z * z) * ((b * a) * a) := by
      rw [← mul_assoc]
    have e11 : (z * z) * ((b * a) * a) = z ^ 2 * (b * a ^ 2) := by
      rw [← sq, mul_assoc, ← sq]
    calc a ^ 2 * b
        = a * (a * b) := e1
      _ = a * (z * (b * a)) := e2
      _ = (a * z) * (b * a) := e3
      _ = (z * a) * (b * a) := e4
      _ = z * (a * (b * a)) := e5
      _ = z * ((a * b) * a) := e7
      _ = z * ((z * (b * a)) * a) := e8
      _ = z * (z * ((b * a) * a)) := e9
      _ = (z * z) * ((b * a) * a) := e10
      _ = z ^ 2 * (b * a ^ 2) := e11
  -- Combine way1 and way2: b * a^2 = z^2 * (b * a^2).
  have hcomb : b * a ^ 2 = z ^ 2 * (b * a ^ 2) := way1.symm.trans way2
  -- Therefore z^2 = 1 by cancellation.
  have hcancel : z ^ 2 * (b * a ^ 2) = 1 * (b * a ^ 2) := by
    rw [one_mul]; exact hcomb.symm
  exact mul_right_cancel hcancel

/-- When $|Z(G)| = 4$ and $|G| = 16$ and $g^2 \in Z(G)$, the commutator
$[g, h] = ghg^{-1}h^{-1}$ has order at most $2$, i.e. $(ghg^{-1}h^{-1})^2 = 1$.
Blueprint label `lem:commutator-has-order-two`. -/
theorem commutator_has_order_two {G : Type*} [Group G] [Finite G]
    (h_sixteen : Nat.card G = 16) (h_center : Nat.card (Subgroup.center G) = 4)
    (g h : G) (h_g_sq : g ^ 2 ∈ Subgroup.center G) :
    (g * h * g⁻¹ * h⁻¹) ^ 2 = 1 := by
  -- Step 1: |G/Z(G)| = 4.
  have hQ_card : Nat.card (G ⧸ Subgroup.center G) = 4 := by
    have h1 : Nat.card (G ⧸ Subgroup.center G) * Nat.card (Subgroup.center G) =
        Nat.card G := quotient_by_center_card G
    rw [h_sixteen, h_center] at h1
    omega
  -- Step 2: G/Z(G) is abelian, since it has cardinality 4 = 2^2 and 2 is prime.
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ_card_sq : Nat.card (G ⧸ Subgroup.center G) = 2 ^ 2 := by
    rw [hQ_card]; norm_num
  letI hQ_comm : CommGroup (G ⧸ Subgroup.center G) :=
    IsPGroup.commGroupOfCardEqPrimeSq hQ_card_sq
  have h_abelian : ∀ a b : G ⧸ Subgroup.center G, a * b = b * a :=
    fun a b => hQ_comm.mul_comm a b
  -- Step 3: The commutator [g,h] lies in Z(G).
  have h_comm_central : g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center G :=
    commutator_in_center_when_quotient_abelian h_abelian g h
  -- Step 4: Apply the existing lemma.
  exact commutator_sq_eq_one_when_sq_central g h h_g_sq h_comm_central

/-- Triple-product lemma in $C_2 \times C_2$: three non-identity elements multiply to $e$
iff they are pairwise distinct. Blueprint label `lem:abc-eq-e-in-klein`. -/
theorem abc_eq_e_in_klein {K : Type*} [Group K] [IsKleinFour K]
    (a b c : K) (ha : a ≠ 1) (hb : b ≠ 1) (hc : c ≠ 1) :
    a * b * c = 1 ↔ a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  classical
  -- Every element squares to 1.
  have hsq : ∀ x : K, x * x = 1 := fun x => by
    have := Monoid.pow_exponent_eq_one (G := K) x
    rw [IsKleinFour.exponent_two, pow_two] at this
    exact this
  -- So every element is its own inverse.
  have hinv : ∀ x : K, x⁻¹ = x := fun x =>
    (eq_inv_of_mul_eq_one_left (hsq x)).symm
  -- The group is commutative.
  have hcomm : ∀ x y : K, x * y = y * x :=
    fun x y => IsKleinFour.isMulCommutative.is_comm.comm x y
  constructor
  · intro habc
    refine ⟨?_, ?_, ?_⟩
    · intro hab
      rw [hab] at habc
      rw [show b * b * c = c from by rw [hsq b, one_mul]] at habc
      exact hc habc
    · intro hbc
      rw [hbc] at habc
      rw [show a * c * c = a from by rw [mul_assoc, hsq c, mul_one]] at habc
      exact ha habc
    · intro hac
      rw [hac] at habc
      rw [show c * b * c = b from by
        rw [hcomm c b, mul_assoc, hsq c, mul_one]] at habc
      exact hb habc
  · intro ⟨hab, hbc, hac⟩
    have hca : c ≠ a := fun h => hac h.symm
    have hcb : c ≠ b := fun h => hbc h.symm
    have hab_ne_one : a * b ≠ 1 := fun h => by
      have hbinv : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [hinv b] at hbinv
      exact hab hbinv
    have hab_ne_a : a * b ≠ a := fun h => by
      have hb_eq : b = 1 := by
        have heq : a * b = a * 1 := by rw [h, mul_one]
        exact mul_left_cancel heq
      exact hb hb_eq
    have hab_ne_b : a * b ≠ b := fun h => by
      have ha_eq : a = 1 := by
        have heq : a * b = 1 * b := by rw [h, one_mul]
        exact mul_right_cancel heq
      exact ha ha_eq
    -- Show c = a * b. Use that K has exactly 4 elements: {1, a, b, a*b}.
    have c_eq_ab : c = a * b := by
      have h_card : Nat.card K = 4 := IsKleinFour.card_four
      haveI : Finite K := IsKleinFour.instFinite
      haveI : Fintype K := Fintype.ofFinite K
      have h_fcard : Fintype.card K = 4 := by
        rw [← Nat.card_eq_fintype_card]; exact h_card
      -- Build the finset explicitly as Finset.insert.
      let S : Finset K :=
        insert 1 (insert a (insert b ({a * b} : Finset K)))
      have hb_notin : b ∉ ({a * b} : Finset K) := by
        simp only [Finset.mem_singleton]
        exact fun h => hab_ne_b h.symm
      have ha_notin : a ∉ (insert b ({a * b} : Finset K)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hab, fun h => hab_ne_a h.symm⟩
      have h1_notin : (1 : K) ∉ (insert a (insert b ({a * b} : Finset K))) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm ha, Ne.symm hb, Ne.symm hab_ne_one⟩
      have hS_card : S.card = 4 := by
        change (insert 1 (insert a (insert b ({a * b} : Finset K)))).card = 4
        rw [Finset.card_insert_of_notMem h1_notin,
            Finset.card_insert_of_notMem ha_notin,
            Finset.card_insert_of_notMem hb_notin,
            Finset.card_singleton]
      have hS_univ : S = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [hS_card, h_fcard]
      have hc_mem : c ∈ S := by rw [hS_univ]; exact Finset.mem_univ c
      change c ∈ insert (1 : K) (insert a (insert b ({a * b} : Finset K))) at hc_mem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc_mem
      rcases hc_mem with h1 | h2 | h3 | h4
      · exact absurd h1 hc
      · exact absurd h2 hca
      · exact absurd h3 hcb
      · exact h4
    -- Now compute: a * b * c = a * b * (a * b) = 1.
    rw [c_eq_ab]
    exact hsq (a * b)

/-- Internal direct product: if $H, K \le G$ with $K \le Z(G)$, $H \cap K = \{e\}$,
and $|H| \cdot |K| = |G|$, then $G \cong H \times K$.
Blueprint label `lem:internal-direct-product`. -/
theorem internal_direct_product {G : Type*} [Group G] [Finite G]
    (H K : Subgroup G) (hK_center : K ≤ Subgroup.center G)
    (h_disjoint : H ⊓ K = ⊥)
    (h_card : Nat.card H * Nat.card K = Nat.card G) :
    Nonempty (G ≃* (H × K)) := by
  -- Build φ : H × K →* G with φ (h, k) = h.val * k.val.
  let φ : H × K →* G := MonoidHom.mk' (fun p => p.1.val * p.2.val) (by
    rintro ⟨h₁, k₁⟩ ⟨h₂, k₂⟩
    -- Need: (h₁*h₂).val * (k₁*k₂).val = (h₁.val * k₁.val) * (h₂.val * k₂.val)
    -- Use centrality of k₁: k₁ * h₂ = h₂ * k₁.
    have hcomm : (k₁ : G) * (h₂ : G) = (h₂ : G) * (k₁ : G) :=
      ((Subgroup.mem_center_iff.mp (hK_center k₁.prop)) (h₂ : G)).symm
    change ((h₁ * h₂ : H) : G) * ((k₁ * k₂ : K) : G) =
      ((h₁ : G) * (k₁ : G)) * ((h₂ : G) * (k₂ : G))
    push_cast
    rw [mul_assoc, mul_assoc, ← mul_assoc (k₁ : G), hcomm,
        mul_assoc (h₂ : G), ← mul_assoc])
  -- Injectivity: if h₁*k₁ = h₂*k₂, then h₂⁻¹*h₁ = k₂*k₁⁻¹ ∈ H ∩ K = ⊥.
  have h_inj : Function.Injective φ := by
    rintro ⟨h₁, k₁⟩ ⟨h₂, k₂⟩ heq
    change (h₁ : G) * (k₁ : G) = (h₂ : G) * (k₂ : G) at heq
    -- Then h₂⁻¹ * h₁ = k₂ * k₁⁻¹.
    have hkey : (h₂ : G)⁻¹ * (h₁ : G) = (k₂ : G) * (k₁ : G)⁻¹ := by
      have hstep : (h₂ : G)⁻¹ * ((h₁ : G) * (k₁ : G)) =
          (h₂ : G)⁻¹ * ((h₂ : G) * (k₂ : G)) := by rw [heq]
      rw [← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul] at hstep
      -- hstep : h₂⁻¹ * h₁ * k₁ = k₂
      have := congrArg (· * (k₁ : G)⁻¹) hstep
      simp only at this
      rw [mul_assoc, mul_inv_cancel, mul_one] at this
      exact this
    -- This element lies in H (as h₂⁻¹ * h₁) and in K (as k₂ * k₁⁻¹).
    set x : G := (h₂ : G)⁻¹ * (h₁ : G) with hx_def
    have hxH : x ∈ H := H.mul_mem (H.inv_mem h₂.prop) h₁.prop
    have hxK : x ∈ K := by
      rw [hkey]
      exact K.mul_mem k₂.prop (K.inv_mem k₁.prop)
    have hxInter : x ∈ H ⊓ K := Subgroup.mem_inf.mpr ⟨hxH, hxK⟩
    rw [h_disjoint] at hxInter
    have hx_eq_one : x = 1 := hxInter
    -- From x = 1, we get h₁ = h₂.
    have hh : (h₁ : G) = (h₂ : G) := by
      have h1 : (h₂ : G)⁻¹ * (h₁ : G) = 1 := hx_eq_one
      have h2 := congrArg ((h₂ : G) * ·) h1
      simp only at h2
      rw [← mul_assoc, mul_inv_cancel, one_mul, mul_one] at h2
      exact h2
    have hk : (k₁ : G) = (k₂ : G) := by
      rw [hh] at heq
      exact mul_left_cancel heq
    have hh' : h₁ = h₂ := Subtype.ext hh
    have hk' : k₁ = k₂ := Subtype.ext hk
    rw [hh', hk']
  -- Cardinality of H × K equals G.
  have h_card_HK : Nat.card (H × K) = Nat.card G := by
    rw [Nat.card_prod]; exact h_card
  -- Injectivity + same finite card ⇒ bijectivity.
  have h_bij : Function.Bijective φ :=
    h_inj.bijective_of_nat_card_le (le_of_eq h_card_HK.symm)
  exact ⟨(MulEquiv.ofBijective φ h_bij).symm⟩

open scoped Pointwise in
/-- Two distinct abelian order-$8$ subgroups of a group of order $16$ force the
center to have order at least $4$. Blueprint label `lem:two-abelian-subgroups-force-center-four`. -/
theorem two_abelian_subgroups_force_center_four {G : Type*} [Group G] [Finite G]
    (h_sixteen : Nat.card G = 16) (H₁ H₂ : Subgroup G)
    (h₁_card : Nat.card H₁ = 8) (h₂_card : Nat.card H₂ = 8)
    (h_distinct : H₁ ≠ H₂)
    (h₁_abelian : ∀ a b : H₁, a * b = b * a)
    (h₂_abelian : ∀ a b : H₂, a * b = b * a) :
    4 ≤ Nat.card (Subgroup.center G) := by
  -- Step 1: |H₁ ⊓ H₂| = 4.
  -- 1a: |H₁ ⊓ H₂| ≤ 8 (since H₁ ⊓ H₂ ≤ H₁).
  have h_card_H₁_eq : Nat.card ((H₁ : Set G)) = 8 := h₁_card
  have h_card_H₂_eq : Nat.card ((H₂ : Set G)) = 8 := h₂_card
  -- subgroup_product_card gives the key cardinality identity.
  have h_prod := subgroup_product_card H₁ H₂
  rw [h_card_H₁_eq, h_card_H₂_eq] at h_prod
  -- |HK| ≤ |G| = 16.
  have h_HK_le_card : Nat.card ((H₁ : Set G) * (H₂ : Set G)) ≤ 16 := by
    rw [← h_sixteen]
    rw [Nat.card_coe_set_eq]
    exact Set.ncard_le_card _
  -- |H₁ ⊓ H₂| ≤ |H₁| = 8 since (H₁ ⊓ H₂) ≤ H₁.
  haveI : Finite H₁ := Nat.finite_of_card_ne_zero (by rw [h₁_card]; norm_num)
  haveI : Finite H₂ := Nat.finite_of_card_ne_zero (by rw [h₂_card]; norm_num)
  have h_inter_le_H₁ : Nat.card (H₁ ⊓ H₂ : Subgroup G) ≤ 8 := by
    rw [← h₁_card]
    exact Subgroup.card_le_of_le (inf_le_left)
  -- From h_prod (64 = inter * HK) and h_HK_le_card (HK ≤ 16): inter ≥ 4.
  set a := Nat.card (H₁ ⊓ H₂ : Subgroup G) with ha_def
  set b := Nat.card ((H₁ : Set G) * (H₂ : Set G)) with hb_def
  have hab : 8 * 8 = a * b := h_prod
  have h_a_pos : 0 < a := Nat.card_pos
  have h_a_ge_4 : 4 ≤ a := by
    -- a * b = 64, b ≤ 16, so a ≥ 4.
    by_contra h_lt
    -- a ≤ 3, so a * b ≤ 3 * 16 = 48 < 64.
    have h_a_le : a ≤ 3 := by omega
    have : a * b ≤ 3 * 16 := Nat.mul_le_mul h_a_le h_HK_le_card
    omega
  -- |H₁ ⊓ H₂| ≠ 8 because H₁ ≠ H₂.
  have h_a_ne_8 : a ≠ 8 := by
    intro h_eq
    apply h_distinct
    -- If a = 8 = |H₁|, then H₁ ⊓ H₂ = H₁ since (H₁ ⊓ H₂) ≤ H₁ and same card.
    have h_inter_eq_H₁ : H₁ ⊓ H₂ = H₁ := by
      apply Subgroup.eq_of_le_of_card_ge (inf_le_left)
      rw [← ha_def, h_eq, h₁_card]
    -- Then H₁ ≤ H₂.
    have h₁_le_h₂ : H₁ ≤ H₂ := h_inter_eq_H₁ ▸ inf_le_right
    -- And by card equality, H₁ = H₂.
    exact Subgroup.eq_of_le_of_card_ge h₁_le_h₂ (by rw [h₁_card, h₂_card])
  -- So a = 4.
  have h_a_eq_4 : a = 4 := by
    have h_a_dvd : a ∣ 64 := ⟨b, hab⟩
    interval_cases a
    all_goals first | rfl | omega
  -- And then b = 16.
  have h_b_eq_16 : b = 16 := by
    have : 8 * 8 = 4 * b := h_a_eq_4 ▸ hab
    omega
  -- Step 2: Show (H₁ : Set G) * (H₂ : Set G) = Set.univ.
  have h_HK_univ : (H₁ : Set G) * (H₂ : Set G) = Set.univ := by
    rw [Set.eq_univ_iff_ncard]
    rw [← Nat.card_coe_set_eq, ← hb_def, h_b_eq_16, h_sixteen]
  -- Step 3: Show H₁ ⊓ H₂ ≤ Subgroup.center G.
  have h_inter_in_center : (H₁ ⊓ H₂ : Subgroup G) ≤ Subgroup.center G := by
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_center_iff]
    intro g
    -- g ∈ G = H₁ * H₂, so g = h₁ * h₂ with h₁ ∈ H₁, h₂ ∈ H₂.
    have hg_mem : g ∈ (H₁ : Set G) * (H₂ : Set G) := by
      rw [h_HK_univ]; trivial
    rw [Set.mem_mul] at hg_mem
    obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := hg_mem
    -- x commutes with h₁ (both in H₁ abelian).
    have hxh₁ : x * h₁ = h₁ * x := by
      have h := h₁_abelian ⟨x, hx₁⟩ ⟨h₁, hh₁⟩
      exact congrArg Subtype.val h
    -- x commutes with h₂ (both in H₂ abelian).
    have hxh₂ : x * h₂ = h₂ * x := by
      have h := h₂_abelian ⟨x, hx₂⟩ ⟨h₂, hh₂⟩
      exact congrArg Subtype.val h
    -- Now compute: h₁ * h₂ * x = h₁ * (h₂ * x) = h₁ * (x * h₂) = (h₁ * x) * h₂
    --            = (x * h₁) * h₂ = x * (h₁ * h₂).
    calc h₁ * h₂ * x = h₁ * (h₂ * x) := mul_assoc _ _ _
      _ = h₁ * (x * h₂) := by rw [hxh₂]
      _ = (h₁ * x) * h₂ := (mul_assoc _ _ _).symm
      _ = (x * h₁) * h₂ := by rw [hxh₁]
      _ = x * (h₁ * h₂) := mul_assoc _ _ _
  -- Step 4: |H₁ ⊓ H₂| ≤ |Z(G)|.
  have : 4 ≤ Nat.card (Subgroup.center G) := by
    rw [← h_a_eq_4, ha_def]
    exact Subgroup.card_le_of_le h_inter_in_center
  exact this

/-- If a subgroup `H` of `G` contains `Z(G)` and `H/Z(G)` is cyclic, then `H`
is abelian. The argument is: `Z(G) ∩ H` (i.e. `(Subgroup.center G).subgroupOf H`)
is contained in `Z(H)` because anything central in `G` is central in `H`; then
`H/Z(H)` is a quotient of `H/(Z(G).subgroupOf H)` hence cyclic, and
`cyclic_center_quotient_abelian` applied to `H` gives commutativity. -/
theorem subgroup_abelian_of_cyclic_quot_center {G : Type*} [Group G]
    (H : Subgroup G)
    (hcyc : IsCyclic (H ⧸ (Subgroup.center G).subgroupOf H)) :
    ∀ a b : H, a * b = b * a := by
  -- Step 1: Z(G).subgroupOf H ≤ Z(H).
  have hz_le_zH : (Subgroup.center G).subgroupOf H ≤ Subgroup.center H := by
    intro a ha
    rw [Subgroup.mem_subgroupOf] at ha
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : G) * (a : G) = (a : G) * (g : G)
    exact (Subgroup.mem_center_iff.mp ha) (g : G)
  -- Step 2: (Z(G).subgroupOf H) is Normal in H (its elements are central in G).
  haveI hnorm : ((Subgroup.center G).subgroupOf H).Normal := by
    constructor
    intro n hn h
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hconj : ((h * n * h⁻¹ : H) : G) = ((n : H) : G) := by
      show (h : G) * (n : G) * (h : G)⁻¹ = (n : G)
      rw [(Subgroup.mem_center_iff.mp hn) (h : G), mul_assoc, mul_inv_cancel, mul_one]
    rw [hconj]
    exact hn
  -- Step 3: H/(Z(G).subgroupOf H) →* H/Z(H) is surjective, so H/Z(H) is cyclic.
  haveI : IsCyclic (H ⧸ Subgroup.center H) := by
    have hsurj : Function.Surjective
        (QuotientGroup.map ((Subgroup.center G).subgroupOf H) (Subgroup.center H)
          (MonoidHom.id H) hz_le_zH) := by
      apply QuotientGroup.map_surjective_of_surjective
      · -- QuotientGroup.mk ∘ id is surjective.
        intro x
        refine Quotient.inductionOn' x ?_
        intro a
        exact ⟨a, rfl⟩
    exact isCyclic_of_surjective _ hsurj
  exact cyclic_center_quotient_abelian H ‹IsCyclic _›

/-- Classification of groups of order $8$. Every group of order $8$ is
isomorphic to one of $C_8$, $C_4 \times C_2$, $C_2 \times C_2 \times C_2$,
$D_4$ (`DihedralGroup 4`), or $Q_8$ (`QuaternionGroup 2`).
Blueprint label `lem:order-eight-classification`. Assumed as an external
project-level dependency. -/
theorem order_eight_classification {G : Type*} [Group G] (h : Nat.card G = 8) :
    Nonempty (G ≃* CyclicGroup 8) ∨
    Nonempty (G ≃* CyclicGroup 4 × CyclicGroup 2) ∨
    Nonempty (G ≃* CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) ∨
    Nonempty (G ≃* DihedralGroup 4) ∨
    Nonempty (G ≃* QuaternionGroup 2) := by
  sorry

/-- There is no group $G$ of order $16$ with $|Z(G)| = 2$ and
$G/Z(G) \cong C_2 \times C_2 \times C_2$.
Blueprint label `thm:no-Z2cubed-quotient`. -/
theorem no_Z2cubed_quotient {G : Type*} [Group G] [Finite G]
    (h_sixteen : Nat.card G = 16) (h_center : Nat.card (Subgroup.center G) = 2) :
    ¬ Nonempty ((G ⧸ Subgroup.center G) ≃*
      CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2) := by
  sorry

/-- With `|G| = 16`, `|Z(G)| = 2`, and `G/Z(G) ≅ D_4`, there exists an element
`x ∈ G` of order 8. This corresponds to a generator of the cyclic-of-order-8
preimage `G_1` of the unique cyclic order-4 subgroup of `D_4`.
Blueprint label `lem:one-Gi-cyclic-order-eight`. -/
theorem one_Gi_cyclic_order_eight {G : Type*} [Group G] [Finite G]
    (h_sixteen : Nat.card G = 16) (h_center : Nat.card (Subgroup.center G) = 2)
    (_hquot : Nonempty ((G ⧸ Subgroup.center G) ≃* DihedralGroup 4)) :
    ∃ x : G, orderOf x = 8 := by
  -- Step 1: extract the iso φ : G/Z(G) ≃* D_4.
  obtain ⟨φ⟩ := _hquot
  -- Step 2: take g₁ = φ⁻¹(r 1) ∈ G/Z(G), an element of order 4.
  set qmap : G →* G ⧸ Subgroup.center G := QuotientGroup.mk' (Subgroup.center G)
    with hqmap_def
  let r1 : DihedralGroup 4 := DihedralGroup.r 1
  let g₁ : G ⧸ Subgroup.center G := φ.symm r1
  let M : Subgroup (G ⧸ Subgroup.center G) := Subgroup.zpowers g₁
  -- |M| = 4 since orderOf g₁ = orderOf r1 = 4.
  have hr1_order : orderOf r1 = 4 := by
    change orderOf (DihedralGroup.r 1) = 4
    rw [DihedralGroup.orderOf_r_one]
  have hg₁_order : orderOf g₁ = 4 := by
    change orderOf (φ.symm r1) = 4
    rw [show (φ.symm r1 : G ⧸ Subgroup.center G) = φ.symm.toMonoidHom r1 from rfl,
      orderOf_injective φ.symm.toMonoidHom φ.symm.injective, hr1_order]
  have hM_card : Nat.card M = 4 := by
    change Nat.card (Subgroup.zpowers g₁) = 4
    rw [Nat.card_zpowers, hg₁_order]
  have hM_cyc : IsCyclic M := by
    change IsCyclic (Subgroup.zpowers g₁); infer_instance
  -- Step 3: K = M.comap qmap is the preimage in G; |K| = 8.
  let K : Subgroup G := M.comap qmap
  have qmap_surj : Function.Surjective qmap :=
    QuotientGroup.mk'_surjective (Subgroup.center G)
  have hM_idx : M.index = 2 := by
    have hi : M.index * Nat.card M = Nat.card (G ⧸ Subgroup.center G) :=
      Subgroup.index_mul_card M
    have hQ : Nat.card (G ⧸ Subgroup.center G) = 8 := by
      have hmul := OrderSixteen.Prelim.quotient_by_center_card G
      rw [h_center, h_sixteen] at hmul; omega
    rw [hM_card, hQ] at hi; omega
  have hK_idx : K.index = 2 := by
    change (M.comap qmap).index = 2
    rw [Subgroup.index_comap]
    have hrange : qmap.range = ⊤ := MonoidHom.range_eq_top.mpr qmap_surj
    rw [hrange, Subgroup.relIndex_top_right]; exact hM_idx
  have hK_card : Nat.card K = 8 := by
    have hk : K.index * Nat.card K = Nat.card G := Subgroup.index_mul_card K
    rw [hK_idx, h_sixteen] at hk; omega
  -- Step 4: K is abelian via subgroup_abelian_of_cyclic_quot_center.
  -- We build the iso K / (Z.subgroupOf K) ≃* f.range = M, which is cyclic.
  let f : K →* (G ⧸ Subgroup.center G) := qmap.comp K.subtype
  have hf_range : f.range = M := by
    ext y
    simp only [MonoidHom.mem_range, MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.coe_subtype, f]
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨x, hxK⟩, rfl⟩; exact hxK
    · intro hyM
      obtain ⟨x, rfl⟩ := qmap_surj y
      exact ⟨⟨x, hyM⟩, rfl⟩
  have hf_ker : f.ker = (Subgroup.center G).subgroupOf K := by
    ext x
    refine ⟨?_, ?_⟩
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      rw [Subgroup.mem_subgroupOf]
      exact (QuotientGroup.eq_one_iff (x : G)).mp hx
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff (x : G)).mpr hx
  haveI : IsCyclic f.range := by
    rw [hf_range]; exact hM_cyc
  haveI hker_normal : ((Subgroup.center G).subgroupOf K).Normal := by
    rw [show (Subgroup.center G).subgroupOf K = f.ker from hf_ker.symm]
    infer_instance
  have iso_quot : K ⧸ (Subgroup.center G).subgroupOf K ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq hf_ker.symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  haveI hKqcyc : IsCyclic (K ⧸ (Subgroup.center G).subgroupOf K) :=
    isCyclic_of_surjective iso_quot.symm iso_quot.symm.surjective
  have hK_abelian : ∀ a b : K, a * b = b * a :=
    OrderSixteen.Prelim.subgroup_abelian_of_cyclic_quot_center K hKqcyc
  -- Step 5: classify K. Five cases.
  rcases OrderSixteen.Prelim.order_eight_classification hK_card with
    hC8 | hC4C2 | hC2cube | hD4 | hQ8
  · -- Case C_8: K is cyclic of order 8, so it has an element of order 8.
    obtain ⟨ψ⟩ := hC8
    haveI hKcyc : IsCyclic K :=
      isCyclic_of_surjective ψ.symm ψ.symm.surjective
    haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK_card]; norm_num)
    obtain ⟨k, hk⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := K)
    refine ⟨(k : G), ?_⟩
    have hsub : orderOf (K.subtype k) = orderOf k :=
      orderOf_injective K.subtype K.subtype_injective k
    have : orderOf (k : G) = orderOf k := hsub
    rw [this, hk, hK_card]
  · -- Case C_4 × C_2: deeper commutator argument from the blueprint.
    -- This is the [G, G] ∩ G_1 contradiction left as a known sub-stub.
    sorry
  · -- Case C_2^3: every element has order dividing 2, but g₁ ∈ M has order 4
    -- and there's a preimage of g₁ in K — contradiction.
    exfalso
    obtain ⟨ψ⟩ := hC2cube
    -- Every element y of (C_2)^3 satisfies y^2 = 1 (decidable check).
    have hsq_cube : ∀ y : CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2, y ^ 2 = 1 := by
      decide
    -- Transport this to K via ψ.
    have hsq : ∀ x : K, x ^ 2 = 1 := by
      intro x
      have hψx_sq : (ψ x) ^ 2 = 1 := hsq_cube (ψ x)
      have : ψ (x ^ 2) = 1 := by rw [map_pow]; exact hψx_sq
      have hinj := ψ.injective
      have heq1 : ψ (x ^ 2) = ψ 1 := by rw [this]; exact (map_one ψ).symm
      exact hinj heq1
    -- Now lift g₁ to K. Since qmap is surjective and g₁ ∈ M, there's x ∈ G with
    -- qmap x = g₁; that x is in K = M.comap qmap.
    obtain ⟨x0, hx0⟩ := qmap_surj g₁
    have hx0K : x0 ∈ K := by
      change x0 ∈ M.comap qmap
      rw [Subgroup.mem_comap, hx0]
      exact Subgroup.mem_zpowers g₁
    set xK : K := ⟨x0, hx0K⟩
    -- xK^2 = 1 in K.
    have hxK2 : xK ^ 2 = 1 := hsq xK
    -- Apply f: f(xK^2) = f(xK)^2 = g₁^2.
    have hfxK : f xK = g₁ := by
      change qmap (xK : G) = g₁
      change qmap x0 = g₁
      exact hx0
    have hg1_sq : g₁ ^ 2 = 1 := by
      have := congrArg f hxK2
      rw [map_pow, map_one, hfxK] at this
      exact this
    have : orderOf g₁ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hg1_sq
    rw [hg₁_order] at this
    omega
  · -- Case D_4: K ≅ D_4 is non-abelian, contradicting K abelian.
    exfalso
    obtain ⟨ψ⟩ := hD4
    -- DihedralGroup 4 is non-abelian: r 1 and sr 0 do not commute.
    have hne : (DihedralGroup.r (1 : ZMod 4)) * (DihedralGroup.sr 0)
        ≠ (DihedralGroup.sr 0) * (DihedralGroup.r 1) := by decide
    have habK := hK_abelian (ψ.symm (DihedralGroup.r 1)) (ψ.symm (DihedralGroup.sr 0))
    have := congrArg ψ habK
    rw [map_mul, map_mul, ψ.apply_symm_apply, ψ.apply_symm_apply] at this
    exact hne this
  · -- Case Q_8: K ≅ Q_8 is non-abelian, contradicting K abelian.
    exfalso
    obtain ⟨ψ⟩ := hQ8
    have hne : (QuaternionGroup.a (1 : ZMod (2 * 2))) * (QuaternionGroup.xa 0)
        ≠ (QuaternionGroup.xa 0) * (QuaternionGroup.a 1) := by decide
    have habK := hK_abelian (ψ.symm (QuaternionGroup.a 1)) (ψ.symm (QuaternionGroup.xa 0))
    have := congrArg ψ habK
    rw [map_mul, map_mul, ψ.apply_symm_apply, ψ.apply_symm_apply] at this
    exact hne this

end OrderSixteen.Prelim

namespace OrderSixteen

variable (G : Type*) [h_group : Group G] [Finite G] {h_sixteen : Nat.card G = 16}

/-- Dependent reindexing of a Pi-type product as a `MulEquiv`.
Given `e : ι ≃ ι'`, transport `(∀ i : ι, P i)` to `(∀ j : ι', P (e.symm j))`. -/
def piCongrLeftMul {ι ι' : Type*} (P : ι → Type*) [∀ i, Mul (P i)] (e : ι ≃ ι') :
    ((i : ι) → P i) ≃* ((j : ι') → P (e.symm j)) :=
  { Equiv.piCongrLeft' P e with
    map_mul' := fun _ _ => by funext j; rfl }

/-- Split a Pi-type over `Fin (n + 1)` into a binary product of the head and the tail. -/
def piFinSuccMul {n : ℕ} (P : Fin (n + 1) → Type*) [∀ i, Mul (P i)] :
    ((i : Fin (n + 1)) → P i) ≃* P 0 × ((i : Fin n) → P i.succ) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [Fin.cons_zero]
    · intro j
      simp [Fin.cons_succ]
  right_inv := fun ⟨a, b⟩ => by
    simp [Fin.cons_zero, Fin.cons_succ]
  map_mul' := fun x y => by
    refine Prod.ext rfl ?_
    funext i
    rfl

include h_sixteen in
theorem center_order_sixteen (h : Nat.card (Subgroup.center G) = 16)
  : Nonempty (G ≃* CyclicGroup 16) ∨
    Nonempty (G ≃* CyclicGroup 8 × CyclicGroup 2) ∨
    Nonempty (G ≃* CyclicGroup 4 × CyclicGroup 4) ∨
    Nonempty (G ≃* CyclicGroup 4 × CyclicGroup 2 × CyclicGroup 2) ∨
    Nonempty (G ≃* CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2)
  := by
  -- Step 1: Z(G) = ⊤ (Z and G are both subgroups of cardinality 16).
  have hcenter_top : Subgroup.center G = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [h, h_sixteen]
  -- Step 2: G is commutative.
  have h_comm : ∀ a b : G, a * b = b * a :=
    (OrderSixteen.Prelim.abelian_iff_center_top G).mpr hcenter_top
  -- Step 3: Promote `Group G` to `CommGroup G`.
  letI hG_comm : CommGroup G := { h_group with mul_comm := h_comm }
  -- Step 4: Apply the multiplicative structure theorem for finite abelian groups.
  obtain ⟨ι, instFin, n, hn_gt, ⟨φ⟩⟩ :=
    CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  -- Step 5: Cardinality of each factor is `n i`, and the product is 16.
  haveI : Fintype ι := instFin
  haveI : ∀ i, NeZero (n i) :=
    fun i => ⟨Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one (hn_gt i).le)⟩
  have hn_card : ∀ i, Nat.card (Multiplicative (ZMod (n i))) = n i := by
    intro i
    rw [Nat.card_congr (Multiplicative.toAdd)]
    exact Nat.card_zmod _
  have hprod : ∏ i, n i = 16 := by
    have hG : Nat.card ((i : ι) → Multiplicative (ZMod (n i))) = 16 := by
      have heq : Nat.card G = Nat.card ((i : ι) → Multiplicative (ZMod (n i))) :=
        Nat.card_eq_of_bijective φ φ.bijective
      rw [← heq, h_sixteen]
    rw [Nat.card_pi] at hG
    simp_rw [hn_card] at hG
    exact hG
  -- Step 6: |ι| ≤ 4, since 2^|ι| ≤ ∏ n i = 16.
  have hcard_le : Fintype.card ι ≤ 4 := by
    by_contra hlt
    push Not at hlt
    have h2pow : 2 ^ Fintype.card ι ≤ ∏ i, n i := by
      have hconst : ∏ _i ∈ (Finset.univ : Finset ι), (2 : ℕ) = 2 ^ Fintype.card ι := by
        rw [Finset.prod_const]
        rfl
      rw [← hconst]
      apply Finset.prod_le_prod
      · intros; positivity
      · intros; exact hn_gt _
    rw [hprod] at h2pow
    have hp : (2 : ℕ) ^ 5 ≤ 2 ^ Fintype.card ι :=
      Nat.pow_le_pow_right (by norm_num) hlt
    omega
  -- Step 7: Show 0 < Fintype.card ι.
  have hk_pos : 0 < Fintype.card ι := by
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with hk | hk
    · -- k = 0 means ι is empty, so ∏ = 1, contradicting ∏ = 16
      have hempty : IsEmpty ι := Fintype.card_eq_zero_iff.mp hk
      have h1 : ∏ i, n i = 1 := by
        rw [@Finset.univ_eq_empty ι _ hempty, Finset.prod_empty]
      rw [hprod] at h1; omega
    · exact hk
  -- Step 8: Case split on `k = Fintype.card ι`. Generalize before the case split.
  obtain ⟨k, hk_eq⟩ : ∃ k, Fintype.card ι = k := ⟨_, rfl⟩
  rw [hk_eq] at hcard_le hk_pos
  -- Set up reindexing using equivalence to Fin k.
  interval_cases k
  · -- k = 1: a single factor of order 16, so G ≃* CyclicGroup 16.
    left
    -- Reindex ι to Fin 1, and use MulEquiv.piUnique.
    let e : ι ≃ Fin 1 := (Fintype.equivFin ι).trans (finCongr hk_eq)
    -- The product over Fin 1 has only one factor, n(e.symm 0).
    have hn0 : n (e.symm 0) = 16 := by
      have heq : ∏ i : Fin 1, n (e.symm i) = ∏ i : ι, n i := by
        apply Finset.prod_equiv e.symm
        · simp
        · intros; rfl
      have : ∏ i : Fin 1, n (e.symm i) = 16 := heq.trans hprod
      simpa using this
    -- Use MulEquiv.piUnique to collapse Fin 1 → α to α default = α 0.
    have ψ : G ≃* Multiplicative (ZMod (n (e.symm 0))) :=
      (φ.trans (piCongrLeftMul (fun i => Multiplicative (ZMod (n i))) e)).trans
        (MulEquiv.piUnique (fun (i : Fin 1) => Multiplicative (ZMod (n (e.symm i)))))
    -- CyclicGroup 16 is defeq to Multiplicative (ZMod 16).
    refine ⟨?_⟩
    change G ≃* Multiplicative (ZMod 16)
    rw [← hn0]
    exact ψ
  · -- k = 2: two factors n₀ * n₁ = 16, each ≥ 2.
    -- Possible (n₀, n₁): (2,8), (4,4), (8,2). Map to second or third disjunct.
    let e : ι ≃ Fin 2 := (Fintype.equivFin ι).trans (finCongr hk_eq)
    have hprod2 : n (e.symm 0) * n (e.symm 1) = 16 := by
      have heq : ∏ i : Fin 2, n (e.symm i) = ∏ i : ι, n i := by
        apply Finset.prod_equiv e.symm
        · simp
        · intros; rfl
      have hp : ∏ i : Fin 2, n (e.symm i) = 16 := heq.trans hprod
      simpa [Fin.prod_univ_succ, Fin.prod_univ_zero] using hp
    have hge0 : 2 ≤ n (e.symm 0) := hn_gt _
    have hge1 : 2 ≤ n (e.symm 1) := hn_gt _
    have hle0 : n (e.symm 0) ≤ 16 := by nlinarith
    have hle1 : n (e.symm 1) ≤ 16 := by nlinarith
    -- The iso template, parametrized by what we know about n (e.symm 0), n (e.symm 1).
    -- We need to produce a final iso depending on the case.
    have key : ∀ a b : ℕ, a = n (e.symm 0) → b = n (e.symm 1) →
        Nonempty (G ≃* Multiplicative (ZMod a) × Multiplicative (ZMod b)) := by
      intro a b ha hb
      refine ⟨?_⟩
      subst ha; subst hb
      exact (φ.trans (piCongrLeftMul (fun i => Multiplicative (ZMod (n i))) e)).trans
        ((piFinSuccMul (fun i : Fin 2 => Multiplicative (ZMod (n (e.symm i))))).trans
          (MulEquiv.prodCongr (MulEquiv.refl _)
            (MulEquiv.piUnique (fun i : Fin 1 =>
              Multiplicative (ZMod (n (e.symm i.succ)))))))
    -- Now case split.
    have hcases : (n (e.symm 0) = 2 ∧ n (e.symm 1) = 8) ∨
                  (n (e.symm 0) = 4 ∧ n (e.symm 1) = 4) ∨
                  (n (e.symm 0) = 8 ∧ n (e.symm 1) = 2) := by
      interval_cases (n (e.symm 0)) <;> interval_cases (n (e.symm 1)) <;> omega
    rcases hcases with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
    · -- (2, 8) → G ≃* CyclicGroup 8 × CyclicGroup 2 via prodComm.
      right; left
      obtain ⟨ψ⟩ := key 2 8 h0.symm h1.symm
      refine ⟨ψ.trans (MulEquiv.prodComm)⟩
    · -- (4, 4) → G ≃* CyclicGroup 4 × CyclicGroup 4.
      right; right; left
      exact key 4 4 h0.symm h1.symm
    · -- (8, 2) → G ≃* CyclicGroup 8 × CyclicGroup 2.
      right; left
      exact key 8 2 h0.symm h1.symm
  · -- k = 3: three factors with product 16, each ≥ 2.
    -- Possible: (2,2,4), (2,4,2), (4,2,2). All map to disjunct 4: C4 × C2 × C2.
    right; right; right; left
    let e : ι ≃ Fin 3 := (Fintype.equivFin ι).trans (finCongr hk_eq)
    have hprod3 : n (e.symm 0) * (n (e.symm 1) * n (e.symm 2)) = 16 := by
      have heq : ∏ i : Fin 3, n (e.symm i) = ∏ i : ι, n i := by
        apply Finset.prod_equiv e.symm
        · simp
        · intros; rfl
      have hp : ∏ i : Fin 3, n (e.symm i) = 16 := heq.trans hprod
      simpa [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_assoc] using hp
    have hge0 : 2 ≤ n (e.symm 0) := hn_gt _
    have hge1 : 2 ≤ n (e.symm 1) := hn_gt _
    have hge2 : 2 ≤ n (e.symm 2) := hn_gt _
    have hle0 : n (e.symm 0) ≤ 4 := by
      have : n (e.symm 0) * 4 ≤ 16 := by
        calc n (e.symm 0) * 4 ≤ n (e.symm 0) * (n (e.symm 1) * n (e.symm 2)) := by
              apply Nat.mul_le_mul_left; nlinarith
          _ = 16 := hprod3
      omega
    have hle1 : n (e.symm 1) ≤ 4 := by
      have h_aux : 4 * n (e.symm 1) ≤ n (e.symm 0) * (n (e.symm 1) * n (e.symm 2)) := by
        have h1 : (2 * 2) * n (e.symm 1) ≤ n (e.symm 0) * n (e.symm 2) * n (e.symm 1) := by
          apply Nat.mul_le_mul_right
          exact Nat.mul_le_mul hge0 hge2
        calc 4 * n (e.symm 1) = (2 * 2) * n (e.symm 1) := by ring
          _ ≤ n (e.symm 0) * n (e.symm 2) * n (e.symm 1) := h1
          _ = n (e.symm 0) * (n (e.symm 1) * n (e.symm 2)) := by ring
      rw [hprod3] at h_aux; omega
    have hle2 : n (e.symm 2) ≤ 4 := by
      have h_aux : 4 * n (e.symm 2) ≤ n (e.symm 0) * (n (e.symm 1) * n (e.symm 2)) := by
        calc 4 * n (e.symm 2) = 2 * 2 * n (e.symm 2) := by ring
          _ ≤ n (e.symm 0) * n (e.symm 1) * n (e.symm 2) := by
              apply Nat.mul_le_mul_right
              exact Nat.mul_le_mul hge0 hge1
          _ = n (e.symm 0) * (n (e.symm 1) * n (e.symm 2)) := by ring
      rw [hprod3] at h_aux; omega
    -- The iso template, parametrized by the three values.
    have key : ∀ a b c : ℕ, a = n (e.symm 0) → b = n (e.symm 1) → c = n (e.symm 2) →
        Nonempty (G ≃* Multiplicative (ZMod a) ×
          Multiplicative (ZMod b) × Multiplicative (ZMod c)) := by
      intro a b c ha hb hc
      refine ⟨?_⟩
      subst ha; subst hb; subst hc
      refine (φ.trans (piCongrLeftMul (fun i => Multiplicative (ZMod (n i))) e)).trans ?_
      refine (piFinSuccMul (fun i : Fin 3 => Multiplicative (ZMod (n (e.symm i))))).trans ?_
      refine MulEquiv.prodCongr (MulEquiv.refl _) ?_
      refine (piFinSuccMul (fun i : Fin 2 => Multiplicative (ZMod (n (e.symm i.succ))))).trans ?_
      refine MulEquiv.prodCongr (MulEquiv.refl _) ?_
      exact MulEquiv.piUnique _
    -- Case split.
    have hcases : (n (e.symm 0) = 2 ∧ n (e.symm 1) = 2 ∧ n (e.symm 2) = 4) ∨
                  (n (e.symm 0) = 2 ∧ n (e.symm 1) = 4 ∧ n (e.symm 2) = 2) ∨
                  (n (e.symm 0) = 4 ∧ n (e.symm 1) = 2 ∧ n (e.symm 2) = 2) := by
      interval_cases (n (e.symm 0)) <;> interval_cases (n (e.symm 1)) <;>
        interval_cases (n (e.symm 2)) <;> omega
    rcases hcases with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    · -- (2, 2, 4) → swap first and last to get (4, 2, 2).
      obtain ⟨ψ⟩ := key 2 2 4 h0.symm h1.symm h2.symm
      -- We have ψ : G ≃* Z2 × Z2 × Z4. Need G ≃* Z4 × Z2 × Z2.
      -- Z2 × Z2 × Z4 ≃ Z2 × (Z4 × Z2) [prodComm on inner] ≃ (Z4 × Z2) × Z2 [prodAssoc?]
      -- Easier: Z2 × Z2 × Z4 ≃ Z4 × (Z2 × Z2) via permutation. Let me use prodComm + assoc.
      refine ⟨ψ.trans ?_⟩
      -- Z2 × (Z2 × Z4) ≃* (Z4 × Z2) × Z2 ≃* Z4 × Z2 × Z2.
      refine (MulEquiv.refl _).trans ?_
      -- Use MulEquiv.prodComm and prodAssoc.
      change Multiplicative (ZMod 2) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 4))
           ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)
      -- (Z2 × (Z2 × Z4)) ≃ ((Z2 × Z2) × Z4) ≃ ((Z2 × Z4) × Z2) ≃ ... too complicated.
      -- Simpler: Z2 × (Z2 × Z4) ≃ Z2 × (Z4 × Z2) ≃ (Z4 × Z2) × Z2 ≃ Z4 × (Z2 × Z2).
      refine (MulEquiv.prodCongr (MulEquiv.refl _) MulEquiv.prodComm).trans ?_
      refine (MulEquiv.prodAssoc).symm.trans ?_
      exact MulEquiv.prodCongr (MulEquiv.prodComm) (MulEquiv.refl _) |>.trans MulEquiv.prodAssoc
    · -- (2, 4, 2) → need (4, 2, 2). Swap first two.
      obtain ⟨ψ⟩ := key 2 4 2 h0.symm h1.symm h2.symm
      refine ⟨ψ.trans ?_⟩
      change Multiplicative (ZMod 2) × (Multiplicative (ZMod 4) × Multiplicative (ZMod 2))
           ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)
      -- (Z2 × (Z4 × Z2)) ≃ ((Z2 × Z4) × Z2) ≃ ((Z4 × Z2) × Z2) ≃ (Z4 × (Z2 × Z2)).
      refine MulEquiv.prodAssoc.symm.trans ?_
      exact MulEquiv.prodCongr MulEquiv.prodComm (MulEquiv.refl _) |>.trans MulEquiv.prodAssoc
    · -- (4, 2, 2): direct match.
      exact key 4 2 2 h0.symm h1.symm h2.symm
  · -- k = 4: four factors each ≥ 2 with product 16, so all factors equal 2.
    right; right; right; right
    let e : ι ≃ Fin 4 := (Fintype.equivFin ι).trans (finCongr hk_eq)
    have hprod4 : ∏ i : Fin 4, n (e.symm i) = 16 := by
      have heq : ∏ i : Fin 4, n (e.symm i) = ∏ i : ι, n i := by
        apply Finset.prod_equiv e.symm
        · simp
        · intros; rfl
      exact heq.trans hprod
    have hn4 : ∀ i : Fin 4, n (e.symm i) = 2 := by
      intro i
      have hge : ∀ j : Fin 4, 2 ≤ n (e.symm j) := fun j => hn_gt _
      -- All four factors ≥ 2 and product = 16. If any > 2, product > 16.
      by_contra hne
      have hgt : 2 < n (e.symm i) := lt_of_le_of_ne (hge i) (Ne.symm hne)
      have : 16 < ∏ j : Fin 4, n (e.symm j) := by
        have hsplit : ∏ j : Fin 4, n (e.symm j) =
            n (e.symm i) * ∏ j ∈ Finset.univ.erase i, n (e.symm j) :=
          (Finset.mul_prod_erase Finset.univ (fun j => n (e.symm j)) (Finset.mem_univ i)).symm
        have hprod3 : 8 ≤ ∏ j ∈ Finset.univ.erase i, n (e.symm j) := by
          have hcard : (Finset.univ.erase i : Finset (Fin 4)).card = 3 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
            simp
          calc 8 = 2 ^ 3 := by norm_num
            _ = ∏ _j ∈ (Finset.univ.erase i : Finset (Fin 4)), (2 : ℕ) := by
                rw [Finset.prod_const, hcard]
            _ ≤ ∏ j ∈ Finset.univ.erase i, n (e.symm j) := by
                apply Finset.prod_le_prod
                · intros; positivity
                · intros j _; exact hge j
        calc 16 < n (e.symm i) * 8 := by omega
          _ ≤ n (e.symm i) * ∏ j ∈ Finset.univ.erase i, n (e.symm j) := by
              apply Nat.mul_le_mul_left _ hprod3
          _ = ∏ j : Fin 4, n (e.symm j) := hsplit.symm
      omega
    -- Build the iso. Start from φ and reindex.
    refine ⟨?_⟩
    let φ' : G ≃* ((i : Fin 4) → Multiplicative (ZMod (n (e.symm i)))) :=
      φ.trans (piCongrLeftMul (fun i => Multiplicative (ZMod (n i))) e)
    -- Each factor is Multiplicative (ZMod 2). Use piCongrRight to rewrite.
    let cast0 : Multiplicative (ZMod (n (e.symm 0))) ≃* Multiplicative (ZMod 2) := by
      rw [hn4 0]
    let cast1 : Multiplicative (ZMod (n (e.symm 1))) ≃* Multiplicative (ZMod 2) := by
      rw [hn4 1]
    let cast2 : Multiplicative (ZMod (n (e.symm 2))) ≃* Multiplicative (ZMod 2) := by
      rw [hn4 2]
    let cast3 : Multiplicative (ZMod (n (e.symm 3))) ≃* Multiplicative (ZMod 2) := by
      rw [hn4 3]
    -- Unfold the Pi-type into a 4-fold product.
    have split : ((i : Fin 4) → Multiplicative (ZMod (n (e.symm i)))) ≃*
        Multiplicative (ZMod (n (e.symm 0))) ×
        Multiplicative (ZMod (n (e.symm 1))) ×
        Multiplicative (ZMod (n (e.symm 2))) ×
        Multiplicative (ZMod (n (e.symm 3))) := by
      refine (piFinSuccMul _).trans ?_
      refine MulEquiv.prodCongr (MulEquiv.refl _) ?_
      refine (piFinSuccMul _).trans ?_
      refine MulEquiv.prodCongr (MulEquiv.refl _) ?_
      refine (piFinSuccMul _).trans ?_
      refine MulEquiv.prodCongr (MulEquiv.refl _) ?_
      exact MulEquiv.piUnique _
    -- Now compose: G ≃* (... × ... × ... × ...) and cast each factor.
    exact φ'.trans (split.trans
      ((cast0.prodCongr (cast1.prodCongr (cast2.prodCongr cast3)))))

include h_sixteen in
theorem center_order_eight (h : Nat.card (Subgroup.center G) = 8)
  : False
  := by
  -- Step 1: |G/Z(G)| = 2 (from |Z(G)| = 8 and |G| = 16).
  have hQ : Nat.card (G ⧸ Subgroup.center G) = 2 := by
    have hmul := OrderSixteen.Prelim.quotient_by_center_card G
    rw [h, h_sixteen] at hmul
    omega
  -- Step 2: G/Z(G) is cyclic since 2 is prime.
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hcyc : IsCyclic (G ⧸ Subgroup.center G) :=
    OrderSixteen.Prelim.cyclic_of_prime_card hQ
  -- Step 3: G is commutative.
  have h_comm : ∀ a b : G, a * b = b * a :=
    OrderSixteen.Prelim.cyclic_center_quotient_abelian G hcyc
  -- Step 4: Z(G) = ⊤.
  have hcenter_top : Subgroup.center G = ⊤ :=
    (OrderSixteen.Prelim.abelian_iff_center_top G).mp h_comm
  -- Step 5: derive a contradiction from |Z(G)| = 8 and Z(G) = ⊤.
  have h16 : Nat.card (Subgroup.center G) = 16 := by
    rw [hcenter_top, Nat.card_congr (Subgroup.topEquiv).toEquiv, h_sixteen]
  omega

include h_sixteen in
/-- Sub-theorem: when `|Z(G)| = 4` and `Z(G)` is cyclic (so `Z(G) ≅ C_4`),
`G` is isomorphic to the modular group `M_16` or to the Pauli group. -/
theorem center_four_cyclic (h : Nat.card (Subgroup.center G) = 4)
    (hcyc : IsCyclic (Subgroup.center G))
  : Nonempty (G ≃* (CyclicGroup 4 × CyclicGroup 2) ⋊[c2OnK8Psi6] CyclicGroup 2) ∨
    Nonempty (G ≃* CyclicGroup 8 ⋊[c2OnC8Pow5] CyclicGroup 2)
  := by
  sorry

include h_sixteen in
/-- Sub-theorem: when `|Z(G)| = 4` and `Z(G)` is not cyclic
(so `Z(G) ≅ C_2 × C_2`), `G` is isomorphic to one of `D_4 × C_2`,
`(C_2 × C_2) ⋊ C_4`, `Q_8 × C_2`, or `C_4 ⋊ C_4`. -/
theorem center_four_klein (h : Nat.card (Subgroup.center G) = 4)
    (hncyc : ¬ IsCyclic (Subgroup.center G))
  : Nonempty (G ≃* CyclicGroup 2 × DihedralGroup 4) ∨
    Nonempty (G ≃* (CyclicGroup 2 × CyclicGroup 2) ⋊[c4OnC2sqSwap] CyclicGroup 4) ∨
    Nonempty (G ≃* CyclicGroup 2 × QuaternionGroup 2) ∨
    Nonempty (G ≃* CyclicGroup 4 ⋊[c4OnC4Inv] CyclicGroup 4)
  := by
  sorry

include h_sixteen in
theorem center_order_four (h : Nat.card (Subgroup.center G) = 4)
  : Nonempty (G ≃* (CyclicGroup 2 × CyclicGroup 2) ⋊[c4OnC2sqSwap] CyclicGroup 4) ∨
    Nonempty (G ≃* CyclicGroup 4 ⋊[c4OnC4Inv] CyclicGroup 4) ∨
    Nonempty (G ≃* CyclicGroup 8 ⋊[c2OnC8Pow5] CyclicGroup 2) ∨
    Nonempty (G ≃* CyclicGroup 2 × DihedralGroup 4) ∨
    Nonempty (G ≃* CyclicGroup 2 × QuaternionGroup 2) ∨
    Nonempty (G ≃* (CyclicGroup 4 × CyclicGroup 2) ⋊[c2OnK8Psi6] CyclicGroup 2)
  := by
  -- Split on whether Z(G) is cyclic. Z(G) is finite, so this is decidable
  -- classically; we use classical choice.
  by_cases hcyc : IsCyclic (Subgroup.center G)
  · -- Z(G) cyclic ⇒ Z(G) ≅ C_4 ⇒ G is M_16 or Pauli.
    obtain (hpauli | hmod) := center_four_cyclic (h_sixteen := h_sixteen) G h hcyc
    · -- Pauli case → disjunct 6.
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hpauli))))
    · -- Modular case → disjunct 3.
      exact Or.inr (Or.inr (Or.inl hmod))
  · -- Z(G) not cyclic ⇒ Z(G) ≅ C_2 × C_2 ⇒ G is D4×C2, K4⋊C4, Q8×C2 or C4⋊C4.
    obtain (hd4 | hk4 | hq8 | hc4) :=
      center_four_klein (h_sixteen := h_sixteen) G h hcyc
    · -- D4 × C2 case → disjunct 4.
      exact Or.inr (Or.inr (Or.inr (Or.inl hd4)))
    · -- K4 ⋊ C4 case → disjunct 1.
      exact Or.inl hk4
    · -- Q8 × C2 case → disjunct 5.
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hq8))))
    · -- C4 ⋊ C4 case → disjunct 2.
      exact Or.inr (Or.inl hc4)

include h_sixteen in
/-- Sub-theorem (leaf case): when `|G| = 16`, `|Z(G)| = 2`, and `G` contains
a witness pair `(x, y)` with `orderOf x = 8`, `orderOf y = 2`,
`y ∉ ⟨x⟩`, and the dihedral relation `y * x * y = x⁻¹`, then `G ≅ DihedralGroup 8`.
Blueprint label `thm:case-dihedral-eight`. -/
theorem center_two_dihedral
    (x : G) (hx_order : orderOf x = 8)
    (y : G) (hy_order : orderOf y = 2)
    (hy_notin : y ∉ Subgroup.zpowers x)
    (h_rel : y * x * y = x⁻¹) :
    Nonempty (G ≃* DihedralGroup 8) := by
  -- y has order 2, so y² = 1 and y = y⁻¹.
  have hy_sq : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rw [hy_order, sq] at this; exact this
  have hy_inv : y⁻¹ = y :=
    (eq_inv_of_mul_eq_one_left hy_sq).symm
  -- Powers of x are well-defined mod 8.
  have hx_pow_eq : ∀ a b : ℕ, a ≡ b [MOD 8] → x ^ a = x ^ b := by
    intro a b hab
    rw [pow_eq_pow_iff_modEq, hx_order]; exact hab
  -- x^(ZMod 8 value) is consistent with ZMod addition.
  have hx_val_add : ∀ i j : ZMod 8, x ^ (i + j).val = x ^ i.val * x ^ j.val := by
    intro i j
    rw [← pow_add]
    apply hx_pow_eq
    rw [Nat.ModEq, ZMod.val_add]
    omega
  -- y * x^k * y = x⁻¹^k (using hy_inv and conj_pow).
  have hyxky : ∀ k : ℕ, y * x ^ k * y = x⁻¹ ^ k := by
    intro k
    have h_conj : (y * x * y⁻¹) ^ k = y * x ^ k * y⁻¹ := conj_pow
    have h_yxy : y * x * y⁻¹ = x⁻¹ := by rw [hy_inv]; exact h_rel
    rw [h_yxy, hy_inv] at h_conj
    exact h_conj.symm
  -- Key fact: for any k1, k2 : ZMod 8,
  -- ((-(k1 : ZMod 8)).val + k2.val) ≡ (k2 - k1).val [MOD 8].
  have h_neg_add_val : ∀ k1 k2 : ZMod 8,
      ((-k1).val + k2.val) ≡ (k2 - k1).val [MOD 8] := by
    intro k1 k2
    have hcast : ((((-k1).val + k2.val) : ℕ) : ZMod 8)
        = (((k2 - k1).val : ℕ) : ZMod 8) := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      ring
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  -- Express x⁻¹ ^ k as x ^ ((-k : ZMod 8).val) for k : ℕ.
  have hx_inv_pow : ∀ k : ℕ, x⁻¹ ^ k = x ^ ((-(k : ZMod 8)).val) := by
    intro k
    rw [inv_pow]
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_add]
    rw [show (1 : G) = x ^ 0 from (pow_zero x).symm]
    apply hx_pow_eq
    have hsum_cast : (((-(k : ZMod 8)).val + k : ℕ) : ZMod 8) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val]
      ring
    have h := (ZMod.natCast_eq_zero_iff _ _).mp hsum_cast
    unfold Nat.ModEq
    omega
  -- Key helper: x^k * y = y * x ^ ((-(k : ZMod 8)).val).
  have hxy_swap : ∀ k : ℕ, x ^ k * y = y * x ^ ((-(k : ZMod 8)).val) := by
    intro k
    have h1 : y * x ^ k * y = x⁻¹ ^ k := hyxky k
    have h2 : y * (y * x ^ k * y) = y * x⁻¹ ^ k := by rw [h1]
    have h3 : y * (y * x ^ k * y) = x ^ k * y := by
      rw [show y * (y * x ^ k * y) = (y * y) * x ^ k * y from by group, hy_sq, one_mul]
    rw [h3, hx_inv_pow] at h2
    exact h2
  -- Define the forward map DihedralGroup 8 → G.
  let f_fun : DihedralGroup 8 → G := fun d => match d with
    | DihedralGroup.r i => x ^ i.val
    | DihedralGroup.sr i => y * x ^ i.val
  have hf_one : f_fun 1 = 1 := by
    change x ^ (0 : ZMod 8).val = 1
    simp
  have hf_mul : ∀ a b : DihedralGroup 8, f_fun (a * b) = f_fun a * f_fun b := by
    rintro (i | i) (j | j)
    · change x ^ (i + j).val = x ^ i.val * x ^ j.val
      exact hx_val_add i j
    · change y * x ^ (j - i).val = x ^ i.val * (y * x ^ j.val)
      have step1 : x ^ i.val * (y * x ^ j.val) = (x ^ i.val * y) * x ^ j.val := by
        rw [mul_assoc]
      rw [step1, hxy_swap i.val, mul_assoc, ← pow_add]
      congr 1
      apply hx_pow_eq
      have hcong : (-(i.val : ZMod 8)) = -i := by rw [ZMod.natCast_zmod_val]
      rw [hcong]
      exact (h_neg_add_val i j).symm
    · change y * x ^ (i + j).val = y * x ^ i.val * x ^ j.val
      rw [hx_val_add i j, mul_assoc]
    · change x ^ (j - i).val = (y * x ^ i.val) * (y * x ^ j.val)
      have step1 : (y * x ^ i.val) * (y * x ^ j.val) = y * ((x ^ i.val * y) * x ^ j.val) := by
        rw [mul_assoc, mul_assoc]
      rw [step1, hxy_swap i.val]
      have step2 : y * ((y * x ^ ((-(i.val : ZMod 8)).val)) * x ^ j.val)
          = (y * y) * (x ^ ((-(i.val : ZMod 8)).val) * x ^ j.val) := by
        simp only [← mul_assoc]
      rw [step2, hy_sq, one_mul, ← pow_add]
      apply hx_pow_eq
      have hcong : (-(i.val : ZMod 8)) = -i := by rw [ZMod.natCast_zmod_val]
      rw [hcong]
      exact (h_neg_add_val i j).symm
  let F : DihedralGroup 8 →* G :=
    { toFun := f_fun
      map_one' := hf_one
      map_mul' := hf_mul }
  have hf_inj : Function.Injective f_fun := by
    rintro (i | i) (j | j) h
    · change x ^ i.val = x ^ j.val at h
      have hmod : i.val ≡ j.val [MOD 8] := by
        have hpow := (pow_eq_pow_iff_modEq).mp h
        rw [hx_order] at hpow; exact hpow
      have hi : ((i.val : ℕ) : ZMod 8) = i := ZMod.natCast_zmod_val i
      have hj : ((j.val : ℕ) : ZMod 8) = j := ZMod.natCast_zmod_val j
      have heq : ((i.val : ℕ) : ZMod 8) = ((j.val : ℕ) : ZMod 8) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
      rw [hi, hj] at heq
      rw [heq]
    · exfalso
      change x ^ i.val = y * x ^ j.val at h
      have hy_eq : y = x ^ i.val * (x ^ j.val)⁻¹ := by
        have : x ^ i.val * (x ^ j.val)⁻¹ = y * x ^ j.val * (x ^ j.val)⁻¹ := by rw [h]
        rw [mul_inv_cancel_right] at this
        exact this.symm
      apply hy_notin
      rw [hy_eq]
      exact Subgroup.mul_mem _ (Subgroup.npow_mem_zpowers x i.val)
        (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers x j.val))
    · exfalso
      change y * x ^ i.val = x ^ j.val at h
      have hy_eq : y = x ^ j.val * (x ^ i.val)⁻¹ := by
        have : x ^ j.val * (x ^ i.val)⁻¹ = (y * x ^ i.val) * (x ^ i.val)⁻¹ := by rw [h]
        rw [mul_inv_cancel_right] at this
        exact this.symm
      apply hy_notin
      rw [hy_eq]
      exact Subgroup.mul_mem _ (Subgroup.npow_mem_zpowers x j.val)
        (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers x i.val))
    · change y * x ^ i.val = y * x ^ j.val at h
      have h' : x ^ i.val = x ^ j.val := mul_left_cancel h
      have hmod : i.val ≡ j.val [MOD 8] := by
        have hpow := (pow_eq_pow_iff_modEq).mp h'
        rw [hx_order] at hpow; exact hpow
      have hi : ((i.val : ℕ) : ZMod 8) = i := ZMod.natCast_zmod_val i
      have hj : ((j.val : ℕ) : ZMod 8) = j := ZMod.natCast_zmod_val j
      have heq : ((i.val : ℕ) : ZMod 8) = ((j.val : ℕ) : ZMod 8) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
      rw [hi, hj] at heq
      rw [heq]
  have hD_card : Nat.card (DihedralGroup 8) = 16 := by
    rw [DihedralGroup.nat_card]
  have hf_bij : Function.Bijective f_fun := by
    apply hf_inj.bijective_of_nat_card_le
    rw [hD_card, h_sixteen]
  exact ⟨(MulEquiv.ofBijective F hf_bij).symm⟩

include h_sixteen in
/-- Sub-theorem (leaf case): when `|G| = 16`, `|Z(G)| = 2`, and `G` contains
a witness pair `(x, y)` with `orderOf x = 8`, `orderOf y = 2`,
`y ∉ ⟨x⟩`, and the semidihedral relation `y * x * y = x^3`, then `G` is
isomorphic to the semidihedral group of order 16.
Blueprint label `thm:case-semidihedral`. -/
theorem center_two_semidihedral
    (x : G) (hx_order : orderOf x = 8)
    (y : G) (hy_order : orderOf y = 2)
    (hy_notin : y ∉ Subgroup.zpowers x)
    (h_rel : y * x * y = x ^ 3) :
    Nonempty (G ≃* CyclicGroup 8 ⋊[c2OnC8Pow3] CyclicGroup 2) := by
  -- y has order 2, so y² = 1 and y = y⁻¹.
  have hy_sq : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rw [hy_order, sq] at this; exact this
  have hy_inv : y⁻¹ = y :=
    (eq_inv_of_mul_eq_one_left hy_sq).symm
  -- Powers of x are well-defined mod 8.
  have hx_pow_eq : ∀ a b : ℕ, a ≡ b [MOD 8] → x ^ a = x ^ b := by
    intro a b hab
    rw [pow_eq_pow_iff_modEq, hx_order]; exact hab
  -- x^(ZMod 8 value) is consistent with ZMod addition.
  have hx_val_add : ∀ i j : ZMod 8, x ^ (i + j).val = x ^ i.val * x ^ j.val := by
    intro i j
    rw [← pow_add]
    apply hx_pow_eq
    rw [Nat.ModEq, ZMod.val_add]
    omega
  -- y * x^k * y = x^(3k) (via conj_pow on the relation y * x * y = x^3).
  have hyxky : ∀ k : ℕ, y * x ^ k * y = x ^ (3 * k) := by
    intro k
    have h_conj : (y * x * y⁻¹) ^ k = y * x ^ k * y⁻¹ := conj_pow
    have h_yxy : y * x * y⁻¹ = x ^ 3 := by rw [hy_inv]; exact h_rel
    rw [h_yxy, hy_inv] at h_conj
    rw [← h_conj, ← pow_mul]
  -- Key fact: for any k1, k2 : ZMod 8, 3 * k1.val + k2.val ≡ ((3 : ZMod 8) * k1 + k2).val [MOD 8].
  have h_three_mul_val : ∀ k1 k2 : ZMod 8,
      3 * k1.val + k2.val ≡ ((3 : ZMod 8) * k1 + k2).val [MOD 8] := by
    intro k1 k2
    have hcast : (((3 * k1.val + k2.val : ℕ) : ZMod 8))
        = ((((3 : ZMod 8) * k1 + k2).val : ℕ) : ZMod 8) := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  -- Key helper: x^k * y = y * x^((3k : ZMod 8).val) (since y * y = 1, multiply hyxky on left by y).
  have hxy_swap : ∀ k : ℕ, x ^ k * y = y * x ^ ((3 * (k : ZMod 8)).val) := by
    intro k
    have h1 : y * x ^ k * y = x ^ (3 * k) := hyxky k
    have h2 : y * (y * x ^ k * y) = y * x ^ (3 * k) := by rw [h1]
    have h3 : y * (y * x ^ k * y) = x ^ k * y := by
      rw [show y * (y * x ^ k * y) = (y * y) * x ^ k * y from by group, hy_sq, one_mul]
    rw [h3] at h2
    rw [h2]
    congr 1
    apply hx_pow_eq
    -- need 3 * k ≡ (3 * (k : ZMod 8)).val [MOD 8]
    have hcast : ((3 * k : ℕ) : ZMod 8) = (((3 * (k : ZMod 8)).val : ℕ) : ZMod 8) := by
      push_cast
      rw [ZMod.natCast_zmod_val]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  -- Case split lemma on CyclicGroup 2: each element has toAdd ∈ {0, 1}.
  have hc2_cases : ∀ g : CyclicGroup 2, (Multiplicative.toAdd g).val = 0 ∨
                   (Multiplicative.toAdd g).val = 1 := by
    intro g
    have h : (Multiplicative.toAdd g).val < 2 := ZMod.val_lt _
    omega
  -- c2OnC8Pow3 at the identity is identity.
  have hphi_one : ∀ n : CyclicGroup 8, c2OnC8Pow3 1 n = n := by
    intro n
    rw [map_one]
    rfl
  -- c2OnC8Pow3 at the non-trivial element sends n to n^3.
  have hphi_nontriv : ∀ n : CyclicGroup 8,
      c2OnC8Pow3 (Multiplicative.ofAdd (1 : ZMod 2)) n = n ^ 3 := by
    intro n
    rfl
  -- For y^k where k = 0 or 1 (since y has order 2). Convert (toAdd g).val for g : CyclicGroup 2.
  -- We'll need to relate x^((toAdd n).val) for n : CyclicGroup 8.
  -- Multiplicativity of `n ↦ x^(toAdd n).val`:
  have hx_toAdd_mul : ∀ n₁ n₂ : CyclicGroup 8,
      x ^ (Multiplicative.toAdd (n₁ * n₂)).val
        = x ^ (Multiplicative.toAdd n₁).val * x ^ (Multiplicative.toAdd n₂).val := by
    intro n₁ n₂
    -- toAdd (n₁ * n₂) = toAdd n₁ + toAdd n₂.
    change x ^ ((Multiplicative.toAdd n₁ + Multiplicative.toAdd n₂)).val
      = x ^ (Multiplicative.toAdd n₁).val * x ^ (Multiplicative.toAdd n₂).val
    exact hx_val_add _ _
  -- x ^ ((Multiplicative.toAdd (n^3)).val) = (x ^ (Multiplicative.toAdd n).val)^3 mod 8.
  have hx_toAdd_pow3 : ∀ n : CyclicGroup 8,
      x ^ (Multiplicative.toAdd (n ^ 3)).val
        = x ^ (3 * (Multiplicative.toAdd n).val) := by
    intro n
    apply hx_pow_eq
    -- toAdd (n^3) = 3 • toAdd n = 3 * toAdd n (in ZMod 8).
    have h : Multiplicative.toAdd (n ^ 3) = 3 * Multiplicative.toAdd n := by
      change (3 : ℕ) • Multiplicative.toAdd n = 3 * Multiplicative.toAdd n
      simp [nsmul_eq_mul]
    rw [h]
    -- Need (3 * toAdd n).val ≡ 3 * (toAdd n).val [MOD 8].
    have hcast : (((3 * Multiplicative.toAdd n).val : ℕ) : ZMod 8)
        = ((3 * (Multiplicative.toAdd n).val : ℕ) : ZMod 8) := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  -- Define the forward map.
  let f_fun : CyclicGroup 8 ⋊[c2OnC8Pow3] CyclicGroup 2 → G := fun a =>
    x ^ (Multiplicative.toAdd a.left).val * y ^ (Multiplicative.toAdd a.right).val
  have hf_one : f_fun 1 = 1 := by
    change x ^ (Multiplicative.toAdd (1 : CyclicGroup 8)).val
       * y ^ (Multiplicative.toAdd (1 : CyclicGroup 2)).val = 1
    have h1 : (Multiplicative.toAdd (1 : CyclicGroup 8)).val = 0 := by
      change (0 : ZMod 8).val = 0
      simp
    have h2 : (Multiplicative.toAdd (1 : CyclicGroup 2)).val = 0 := by
      change (0 : ZMod 2).val = 0
      simp
    rw [h1, h2]; simp
  have hf_mul : ∀ a b : CyclicGroup 8 ⋊[c2OnC8Pow3] CyclicGroup 2,
      f_fun (a * b) = f_fun a * f_fun b := by
    intro a b
    change x ^ (Multiplicative.toAdd (a * b).left).val
         * y ^ (Multiplicative.toAdd (a * b).right).val
       = (x ^ (Multiplicative.toAdd a.left).val * y ^ (Multiplicative.toAdd a.right).val)
       * (x ^ (Multiplicative.toAdd b.left).val * y ^ (Multiplicative.toAdd b.right).val)
    -- (a * b).left = a.left * c2OnC8Pow3 a.right b.left.
    -- (a * b).right = a.right * b.right.
    rw [SemidirectProduct.mul_left, SemidirectProduct.mul_right]
    -- Case split on a.right (the CyclicGroup 2 element).
    -- Derived swap: x^(3k) * y = y * x^k (from y * x^k = x^(3k) * y, derived from hyxky).
    have hxy_swap_inv : ∀ k : ℕ, x ^ (3 * k) * y = y * x ^ k := by
      intro k
      have h1 : y * x ^ k * y = x ^ (3 * k) := hyxky k
      -- Multiply both sides on the right by y:
      -- (y * x^k * y) * y = x^(3k) * y
      -- y * x^k = x^(3k) * y
      have h2 : y * x ^ k * y * y = x ^ (3 * k) * y := by rw [h1]
      rw [mul_assoc (y * x ^ k) y y, hy_sq, mul_one] at h2
      -- h2 : y * x^k = x^(3k) * y
      exact h2.symm
    -- (Multiplicative.toAdd g₁ + Multiplicative.toAdd g₂).val handling for CyclicGroup 2:
    -- For g₁ = ofAdd 1 and g₂ = ofAdd 1: 1 + 1 = 2 ≡ 0 in ZMod 2, so toAdd (g₁ * g₂) = 0.
    rcases hc2_cases a.right with ha | ha
    · -- a.right = 1, so c2OnC8Pow3 a.right = id, y^0 = 1.
      have ha_eq : a.right = 1 := by
        apply Multiplicative.toAdd.injective
        rw [show (Multiplicative.toAdd (1 : CyclicGroup 2)) = (0 : ZMod 2) from rfl]
        rw [ZMod.val_eq_zero] at ha
        exact ha
      rw [ha_eq, hphi_one]
      have hay0 : y ^ (Multiplicative.toAdd (1 : CyclicGroup 2)).val = 1 := by
        rw [show (Multiplicative.toAdd (1 : CyclicGroup 2)) = (0 : ZMod 2) from rfl]
        simp
      rw [hay0]
      simp only [mul_one]
      -- Goal: x^(toAdd (a.left * b.left)).val * y^(toAdd (1 * b.right)).val
      --     = x^(toAdd a.left).val * (x^(toAdd b.left).val * y^(toAdd b.right).val)
      rw [hx_toAdd_mul, one_mul, mul_assoc]
    · -- a.right ≠ 1, so a.right = Multiplicative.ofAdd 1, hence c2OnC8Pow3 a.right = (·^3).
      have ha_eq : a.right = Multiplicative.ofAdd (1 : ZMod 2) := by
        apply Multiplicative.toAdd.injective
        rw [show Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2)) = (1 : ZMod 2) from rfl]
        have h1 : (Multiplicative.toAdd a.right).val = 1 := ha
        have hcast : (((Multiplicative.toAdd a.right).val : ℕ) : ZMod 2)
            = ((1 : ℕ) : ZMod 2) := by rw [h1]
        rw [ZMod.natCast_zmod_val] at hcast
        rw [hcast]; rfl
      rw [ha_eq, hphi_nontriv]
      have hay1 : y ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))).val = y := by
        rw [show (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))) = (1 : ZMod 2) from rfl]
        rw [show ((1 : ZMod 2)).val = 1 from rfl]
        simp
      rw [hay1]
      -- Goal: x^(toAdd (a.left * b.left^3)).val * y^(toAdd (ofAdd 1 * b.right)).val
      --     = x^(toAdd a.left).val * y * (x^(toAdd b.left).val * y^(toAdd b.right).val)
      rw [hx_toAdd_mul]
      -- Massage b.left^3 by replacing with explicit equivalent (b.left*b.left*b.left).
      have hpow3_eq : (b.left ^ (3 : ℕ) : CyclicGroup 8) = b.left * b.left * b.left := by
        rw [pow_succ, pow_succ, pow_one]
      rw [show (b.left ^ 3 : CyclicGroup 8) = b.left * b.left * b.left from hpow3_eq]
      rw [hx_toAdd_mul, hx_toAdd_mul]
      -- Now LHS has x^(toAdd a.left).val * (x^(toAdd b.left).val * x^(toAdd b.left).val
      --     * x^(toAdd b.left).val) * y^(toAdd (ofAdd 1 * b.right)).val
      -- Combine the three x^k via pow_add: x^k * x^k * x^k = x^(3k).
      rw [← pow_add, ← pow_add]
      -- Now: x^(toAdd a.left).val * x^((toAdd b.left).val + (toAdd b.left).val
      --     + (toAdd b.left).val) * y^...
      have h3k : (Multiplicative.toAdd b.left).val + (Multiplicative.toAdd b.left).val
          + (Multiplicative.toAdd b.left).val = 3 * (Multiplicative.toAdd b.left).val := by ring
      rw [h3k]
      -- LHS: x^(toAdd a.left).val * x^(3*(toAdd b.left).val) * y^(toAdd (ofAdd 1 * b.right)).val
      -- RHS: x^(toAdd a.left).val * y * (x^(toAdd b.left).val * y^(toAdd b.right).val)
      -- Apply mul_assoc to LHS and RHS explicitly.
      rw [mul_assoc (x ^ (Multiplicative.toAdd a.left).val) (x ^ (3 * (Multiplicative.toAdd b.left).val)) _]
      rw [mul_assoc (x ^ (Multiplicative.toAdd a.left).val) y _]
      congr 1
      -- Now goal: x^(3*b.left.val) * y^(toAdd (ofAdd 1 * b.right)).val
      --        = y * (x^b.left.val * y^b.right.val)
      rcases hc2_cases b.right with hb | hb
      · -- b.right = 1: y^(toAdd b.right).val = 1, y^(toAdd (ofAdd 1 * 1)).val = y.
        have hbr_eq : b.right = 1 := by
          apply Multiplicative.toAdd.injective
          rw [show (Multiplicative.toAdd (1 : CyclicGroup 2)) = (0 : ZMod 2) from rfl]
          rw [ZMod.val_eq_zero] at hb
          exact hb
        rw [hbr_eq, mul_one]
        rw [hay1]
        have hy_pow_0 : y ^ (Multiplicative.toAdd (1 : CyclicGroup 2)).val = 1 := by
          rw [show (Multiplicative.toAdd (1 : CyclicGroup 2)) = (0 : ZMod 2) from rfl]
          simp
        rw [hy_pow_0, mul_one]
        -- Goal: x^(3*(toAdd b.left).val) * y = y * x^(toAdd b.left).val
        exact hxy_swap_inv _
      · -- b.right = ofAdd 1: y^(toAdd b.right).val = y, y^(toAdd (ofAdd 1 * ofAdd 1)).val = y^0 = 1.
        have hbr_eq : b.right = Multiplicative.ofAdd (1 : ZMod 2) := by
          apply Multiplicative.toAdd.injective
          rw [show Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2)) = (1 : ZMod 2) from rfl]
          have h1 : (Multiplicative.toAdd b.right).val = 1 := hb
          have hcast : (((Multiplicative.toAdd b.right).val : ℕ) : ZMod 2)
              = ((1 : ℕ) : ZMod 2) := by rw [h1]
          rw [ZMod.natCast_zmod_val] at hcast
          rw [hcast]; rfl
        rw [hbr_eq]
        -- Goal after rw: x^(3*(toAdd b.left).val) * y^(toAdd (ofAdd 1 * ofAdd 1)).val
        --             = y * (x^(toAdd b.left).val * y^(toAdd ofAdd 1).val)
        -- Note (toAdd (ofAdd 1 * ofAdd 1)).val = 0 and (toAdd ofAdd 1).val = 1 by decide.
        -- Use simp to unfold things.
        -- Compute the y exponents directly.
        have h_y_zero : y ^ (Multiplicative.toAdd
            (Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2))).val
            = (1 : G) := by
          have htadd : Multiplicative.toAdd
              (Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2))
              = ((1 : ZMod 2) + 1) := rfl
          rw [htadd]
          rw [show ((1 : ZMod 2) + 1) = 0 from by decide]
          show y ^ ((0 : ZMod 2)).val = (1 : G)
          simp
        have h_y_one : y ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))).val = y := by
          show y ^ ((1 : ZMod 2)).val = y
          simp [show ((1 : ZMod 2)).val = 1 from rfl]
        suffices h : x ^ (3 * (Multiplicative.toAdd b.left).val) * (1 : G)
            = y * (x ^ (Multiplicative.toAdd b.left).val * y) by
          calc x ^ (3 * (Multiplicative.toAdd b.left).val) *
                  y ^ (Multiplicative.toAdd
                    (Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2))).val
              = x ^ (3 * (Multiplicative.toAdd b.left).val) * 1 := by rw [h_y_zero]
            _ = y * (x ^ (Multiplicative.toAdd b.left).val * y) := h
            _ = y * (x ^ (Multiplicative.toAdd b.left).val *
                y ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))).val) := by rw [h_y_one]
        rw [mul_one]
        -- Goal: x^(3*(toAdd b.left).val) = y * (x^(toAdd b.left).val * y)
        rw [← mul_assoc, ← hyxky]
  -- Build the MonoidHom.
  let F : (CyclicGroup 8 ⋊[c2OnC8Pow3] CyclicGroup 2) →* G :=
    { toFun := f_fun
      map_one' := hf_one
      map_mul' := hf_mul }
  -- Injectivity.
  have hf_inj : Function.Injective f_fun := by
    intro a b hab
    change x ^ (Multiplicative.toAdd a.left).val * y ^ (Multiplicative.toAdd a.right).val
       = x ^ (Multiplicative.toAdd b.left).val * y ^ (Multiplicative.toAdd b.right).val at hab
    rcases hc2_cases a.right with ha | ha
    · rcases hc2_cases b.right with hb | hb
      · -- Both a.right = 1 and b.right = 1.
        rw [ha, hb] at hab
        simp only [pow_zero, mul_one] at hab
        have hmod : (Multiplicative.toAdd a.left).val ≡ (Multiplicative.toAdd b.left).val [MOD 8] := by
          have hpow := (pow_eq_pow_iff_modEq).mp hab
          rw [hx_order] at hpow; exact hpow
        have ha_eq : a.right = b.right := by
          apply Multiplicative.toAdd.injective
          have := ha.trans hb.symm
          have h1 : ((Multiplicative.toAdd a.right).val : ZMod 2)
              = ((Multiplicative.toAdd b.right).val : ZMod 2) := by
            rw [ha, hb]
          rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h1
          exact h1
        have hl_eq : a.left = b.left := by
          apply Multiplicative.toAdd.injective
          have hi : ((((Multiplicative.toAdd a.left).val) : ℕ) : ZMod 8)
              = Multiplicative.toAdd a.left := ZMod.natCast_zmod_val _
          have hj : ((((Multiplicative.toAdd b.left).val) : ℕ) : ZMod 8)
              = Multiplicative.toAdd b.left := ZMod.natCast_zmod_val _
          have heq : ((((Multiplicative.toAdd a.left).val) : ℕ) : ZMod 8)
              = ((((Multiplicative.toAdd b.left).val) : ℕ) : ZMod 8) :=
            (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
          rw [hi, hj] at heq
          exact heq
        exact SemidirectProduct.ext hl_eq ha_eq
      · -- a.right = 1, b.right = ofAdd 1: contradiction.
        exfalso
        rw [ha, hb] at hab
        simp only [pow_zero, mul_one, pow_one] at hab
        -- hab: x^(toAdd a.left).val = x^(toAdd b.left).val * y
        have hy_eq : y = (x ^ (Multiplicative.toAdd b.left).val)⁻¹
                       * x ^ (Multiplicative.toAdd a.left).val := by
          have : (x ^ (Multiplicative.toAdd b.left).val)⁻¹ * x ^ (Multiplicative.toAdd a.left).val
              = (x ^ (Multiplicative.toAdd b.left).val)⁻¹ *
                  (x ^ (Multiplicative.toAdd b.left).val * y) := by rw [hab]
          rw [← mul_assoc, inv_mul_cancel, one_mul] at this
          exact this.symm
        apply hy_notin
        rw [hy_eq]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers x _))
          (Subgroup.npow_mem_zpowers x _)
    · rcases hc2_cases b.right with hb | hb
      · -- a.right = ofAdd 1, b.right = 1: contradiction.
        exfalso
        rw [ha, hb] at hab
        simp only [pow_one, pow_zero, mul_one] at hab
        -- hab: x^(toAdd a.left).val * y = x^(toAdd b.left).val
        have hy_eq : y = (x ^ (Multiplicative.toAdd a.left).val)⁻¹
                       * x ^ (Multiplicative.toAdd b.left).val := by
          have : (x ^ (Multiplicative.toAdd a.left).val)⁻¹ *
                 (x ^ (Multiplicative.toAdd a.left).val * y)
              = (x ^ (Multiplicative.toAdd a.left).val)⁻¹ * x ^ (Multiplicative.toAdd b.left).val
              := by rw [hab]
          rw [← mul_assoc, inv_mul_cancel, one_mul] at this
          exact this
        apply hy_notin
        rw [hy_eq]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers x _))
          (Subgroup.npow_mem_zpowers x _)
      · -- Both a.right = ofAdd 1 and b.right = ofAdd 1.
        rw [ha, hb] at hab
        simp only [pow_one] at hab
        -- hab: x^(toAdd a.left).val * y = x^(toAdd b.left).val * y
        have hab' : x ^ (Multiplicative.toAdd a.left).val = x ^ (Multiplicative.toAdd b.left).val :=
          mul_right_cancel hab
        have hmod : (Multiplicative.toAdd a.left).val ≡ (Multiplicative.toAdd b.left).val [MOD 8] := by
          have hpow := (pow_eq_pow_iff_modEq).mp hab'
          rw [hx_order] at hpow; exact hpow
        have ha_eq : a.right = b.right := by
          apply Multiplicative.toAdd.injective
          have h1 : ((Multiplicative.toAdd a.right).val : ZMod 2)
              = ((Multiplicative.toAdd b.right).val : ZMod 2) := by rw [ha, hb]
          rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h1
          exact h1
        have hl_eq : a.left = b.left := by
          apply Multiplicative.toAdd.injective
          have hi : ((((Multiplicative.toAdd a.left).val) : ℕ) : ZMod 8)
              = Multiplicative.toAdd a.left := ZMod.natCast_zmod_val _
          have hj : ((((Multiplicative.toAdd b.left).val) : ℕ) : ZMod 8)
              = Multiplicative.toAdd b.left := ZMod.natCast_zmod_val _
          have heq : ((((Multiplicative.toAdd a.left).val) : ℕ) : ZMod 8)
              = ((((Multiplicative.toAdd b.left).val) : ℕ) : ZMod 8) :=
            (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
          rw [hi, hj] at heq
          exact heq
        exact SemidirectProduct.ext hl_eq ha_eq
  -- Cardinality.
  have hSD_card : Nat.card (CyclicGroup 8 ⋊[c2OnC8Pow3] CyclicGroup 2) = 16 := by
    rw [SemidirectProduct.card, card_cyclicGroup, card_cyclicGroup]
  have hf_bij : Function.Bijective f_fun := by
    apply hf_inj.bijective_of_nat_card_le
    rw [hSD_card, h_sixteen]
  exact ⟨(MulEquiv.ofBijective F hf_bij).symm⟩

include h_sixteen in
/-- Sub-theorem (leaf case): when `|G| = 16`, `|Z(G)| = 2`, and `G` contains
a witness pair `(x, y)` with `orderOf x = 8`, `y^2 = x^4`, `y ∉ ⟨x⟩`, and the
quaternion relation `y * x * y⁻¹ = x⁻¹`, then `G ≅ QuaternionGroup 4`
(the generalized quaternion group of order 16). Blueprint label
`thm:case-quaternion-sixteen`. -/
theorem center_two_quaternion
    (x : G) (hx_order : orderOf x = 8)
    (y : G) (hy_sq : y ^ 2 = x ^ 4)
    (hy_notin : y ∉ Subgroup.zpowers x)
    (h_rel : y * x * y⁻¹ = x⁻¹) :
    Nonempty (G ≃* QuaternionGroup 4) := by
  -- y² = x⁴, used to convert the xa-xa case.
  have hy_sq' : y * y = x ^ 4 := by rw [← sq]; exact hy_sq
  -- Powers of x are well-defined mod 8.
  have hx_pow_eq : ∀ a b : ℕ, a ≡ b [MOD 8] → x ^ a = x ^ b := by
    intro a b hab
    rw [pow_eq_pow_iff_modEq, hx_order]; exact hab
  -- x^(ZMod 8 value) is consistent with ZMod addition.
  have hx_val_add : ∀ i j : ZMod 8, x ^ (i + j).val = x ^ i.val * x ^ j.val := by
    intro i j
    rw [← pow_add]
    apply hx_pow_eq
    rw [Nat.ModEq, ZMod.val_add]
    omega
  -- y * x^k * y⁻¹ = x⁻¹^k (via conj_pow on the relation y * x * y⁻¹ = x⁻¹).
  have hyxky : ∀ k : ℕ, y * x ^ k * y⁻¹ = x⁻¹ ^ k := by
    intro k
    have h_conj : (y * x * y⁻¹) ^ k = y * x ^ k * y⁻¹ := conj_pow
    rw [h_rel] at h_conj
    exact h_conj.symm
  -- Key fact: for any k1, k2 : ZMod 8,
  -- ((-k1).val + k2.val) ≡ (k2 - k1).val [MOD 8].
  have h_neg_add_val : ∀ k1 k2 : ZMod 8,
      ((-k1).val + k2.val) ≡ (k2 - k1).val [MOD 8] := by
    intro k1 k2
    have hcast : ((((-k1).val + k2.val) : ℕ) : ZMod 8)
        = (((k2 - k1).val : ℕ) : ZMod 8) := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      ring
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  -- Express x⁻¹ ^ k as x ^ ((-k : ZMod 8).val) for k : ℕ.
  have hx_inv_pow : ∀ k : ℕ, x⁻¹ ^ k = x ^ ((-(k : ZMod 8)).val) := by
    intro k
    rw [inv_pow]
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_add]
    rw [show (1 : G) = x ^ 0 from (pow_zero x).symm]
    apply hx_pow_eq
    have hsum_cast : (((-(k : ZMod 8)).val + k : ℕ) : ZMod 8) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val]
      ring
    have h := (ZMod.natCast_eq_zero_iff _ _).mp hsum_cast
    unfold Nat.ModEq
    omega
  -- Key helper: x^k * y = y * x ^ ((-(k : ZMod 8)).val).
  -- Multiply hyxky on the right by y: y * x^k = x⁻¹^k * y.
  -- Then multiply on the left by y⁻¹ flipped: x^k * y = y * x⁻¹^k from rearrangement.
  -- Actually simpler: from hyxky, y * x^k = x⁻¹^k * y, so x^k * y = y * x^... after
  -- conjugating both sides by y appropriately. Let me derive it directly.
  have hxy_swap : ∀ k : ℕ, x ^ k * y = y * x ^ ((-(k : ZMod 8)).val) := by
    -- From y * x^k * y⁻¹ = x⁻¹^k, get y * x^k = x⁻¹^k * y (for all k).
    have h1 : ∀ k : ℕ, y * x ^ k = x⁻¹ ^ k * y := by
      intro k
      have hk := hyxky k
      have h2 : (y * x ^ k * y⁻¹) * y = x⁻¹ ^ k * y := by rw [hk]
      rw [inv_mul_cancel_right] at h2
      exact h2
    intro k
    -- We want: x^k * y = y * x^((-k).val).
    -- From h1 applied to (-k).val: y * x^((-k).val) = x⁻¹^((-k).val) * y.
    -- And x⁻¹^((-k).val) = x^k (mod 8).
    have h3 : y * x ^ ((-(k : ZMod 8)).val) = x⁻¹ ^ ((-(k : ZMod 8)).val) * y :=
      h1 ((-(k : ZMod 8)).val)
    have hx_inv_pow_neg : x⁻¹ ^ ((-(k : ZMod 8)).val) = x ^ k := by
      rw [hx_inv_pow]
      apply hx_pow_eq
      have hcast : (((-((-(k : ZMod 8)).val : ZMod 8)).val : ℕ) : ZMod 8) = ((k : ℕ) : ZMod 8) := by
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
        ring
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
    rw [hx_inv_pow_neg] at h3
    exact h3.symm
  -- Define the forward map QuaternionGroup 4 → G.
  let f_fun : QuaternionGroup 4 → G := fun d => match d with
    | QuaternionGroup.a i => x ^ i.val
    | QuaternionGroup.xa i => y * x ^ i.val
  have hf_one : f_fun 1 = 1 := by
    change x ^ (0 : ZMod 8).val = 1
    simp
  have hf_mul : ∀ a b : QuaternionGroup 4, f_fun (a * b) = f_fun a * f_fun b := by
    rintro (i | i) (j | j)
    · change x ^ (i + j).val = x ^ i.val * x ^ j.val
      exact hx_val_add i j
    · change y * x ^ (j - i).val = x ^ i.val * (y * x ^ j.val)
      have step1 : x ^ i.val * (y * x ^ j.val) = (x ^ i.val * y) * x ^ j.val := by
        rw [mul_assoc]
      rw [step1, hxy_swap i.val, mul_assoc, ← pow_add]
      congr 1
      apply hx_pow_eq
      have hcong : (-(i.val : ZMod 8)) = -i := by rw [ZMod.natCast_zmod_val]
      rw [hcong]
      exact (h_neg_add_val i j).symm
    · change y * x ^ (i + j).val = y * x ^ i.val * x ^ j.val
      rw [hx_val_add i j, mul_assoc]
    · -- xa i * xa j = a (↑n + j - i) with n = 4 (QuaternionGroup 4).
      -- Goal: x ^ (↑4 + j - i).val = (y * x ^ i.val) * (y * x ^ j.val)
      change x ^ (((4 : ℕ) : ZMod 8) + j - i).val
        = (y * x ^ i.val) * (y * x ^ j.val)
      have step1 : (y * x ^ i.val) * (y * x ^ j.val)
          = y * ((x ^ i.val * y) * x ^ j.val) := by
        rw [mul_assoc, mul_assoc]
      rw [step1, hxy_swap i.val]
      -- Now: y * ((y * x^((-i).val)) * x^j.val)
      -- = (y * y) * (x^((-i).val) * x^j.val)
      -- = x^4 * x^((-i).val + j.val)
      -- = x^(4 + (-i).val + j.val)
      have step2 : y * ((y * x ^ ((-(i.val : ZMod 8)).val)) * x ^ j.val)
          = (y * y) * (x ^ ((-(i.val : ZMod 8)).val) * x ^ j.val) := by
        simp only [← mul_assoc]
      rw [step2, hy_sq', ← pow_add, ← pow_add]
      -- Goal: x ^ (((4 : ℕ) : ZMod 8) + j - i).val
      --     = x ^ (4 + ((-(i.val : ZMod 8)).val + j.val))
      apply hx_pow_eq
      -- We need (((4 : ℕ) : ZMod 8) + j - i).val ≡ 4 + (-i).val + j.val [MOD 8].
      have hcong_i : (-(i.val : ZMod 8)) = -i := by rw [ZMod.natCast_zmod_val]
      have hneg_add : ((-(i.val : ZMod 8)).val + j.val) ≡ (j - i).val [MOD 8] := by
        rw [hcong_i]
        exact h_neg_add_val i j
      -- Now reduce: (((4:ℕ):ZMod 8) + j - i).val ≡ 4 + ((-i).val + j.val) mod 8
      -- Step a: 4 + ((-i).val + j.val) ≡ 4 + (j - i).val mod 8
      -- Step b: (((4:ℕ):ZMod 8) + j - i).val ≡ 4 + (j - i).val mod 8
      have h_step_a : 4 + ((-(i.val : ZMod 8)).val + j.val) ≡ 4 + (j - i).val [MOD 8] := by
        have := hneg_add
        unfold Nat.ModEq at this ⊢
        omega
      have h_step_b : (((4 : ℕ) : ZMod 8) + j - i).val ≡ 4 + (j - i).val [MOD 8] := by
        -- ((4:ℕ):ZMod 8) + j - i = ((4:ℕ):ZMod 8) + (j - i)
        have hrewrite : ((4 : ℕ) : ZMod 8) + j - i = ((4 : ℕ) : ZMod 8) + (j - i) := by
          ring
        rw [hrewrite]
        -- Now we need ((↑4 + (j - i)) : ZMod 8).val ≡ 4 + (j - i).val [MOD 8]
        have hval_add := ZMod.val_add (((4 : ℕ) : ZMod 8)) (j - i)
        have hval_4 : (((4 : ℕ) : ZMod 8) : ZMod 8).val = 4 := by decide
        rw [hval_4] at hval_add
        unfold Nat.ModEq
        omega
      -- Combine using symmetry/transitivity.
      exact h_step_b.trans h_step_a.symm
  let F : QuaternionGroup 4 →* G :=
    { toFun := f_fun
      map_one' := hf_one
      map_mul' := hf_mul }
  have hf_inj : Function.Injective f_fun := by
    rintro (i | i) (j | j) h
    · change x ^ i.val = x ^ j.val at h
      have hmod : i.val ≡ j.val [MOD 8] := by
        have hpow := (pow_eq_pow_iff_modEq).mp h
        rw [hx_order] at hpow; exact hpow
      have hi : ((i.val : ℕ) : ZMod 8) = i := ZMod.natCast_zmod_val i
      have hj : ((j.val : ℕ) : ZMod 8) = j := ZMod.natCast_zmod_val j
      have heq : ((i.val : ℕ) : ZMod 8) = ((j.val : ℕ) : ZMod 8) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
      rw [hi, hj] at heq
      rw [heq]
    · exfalso
      change x ^ i.val = y * x ^ j.val at h
      have hy_eq : y = x ^ i.val * (x ^ j.val)⁻¹ := by
        have : x ^ i.val * (x ^ j.val)⁻¹ = y * x ^ j.val * (x ^ j.val)⁻¹ := by rw [h]
        rw [mul_inv_cancel_right] at this
        exact this.symm
      apply hy_notin
      rw [hy_eq]
      exact Subgroup.mul_mem _ (Subgroup.npow_mem_zpowers x i.val)
        (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers x j.val))
    · exfalso
      change y * x ^ i.val = x ^ j.val at h
      have hy_eq : y = x ^ j.val * (x ^ i.val)⁻¹ := by
        have : x ^ j.val * (x ^ i.val)⁻¹ = (y * x ^ i.val) * (x ^ i.val)⁻¹ := by rw [h]
        rw [mul_inv_cancel_right] at this
        exact this.symm
      apply hy_notin
      rw [hy_eq]
      exact Subgroup.mul_mem _ (Subgroup.npow_mem_zpowers x j.val)
        (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers x i.val))
    · change y * x ^ i.val = y * x ^ j.val at h
      have h' : x ^ i.val = x ^ j.val := mul_left_cancel h
      have hmod : i.val ≡ j.val [MOD 8] := by
        have hpow := (pow_eq_pow_iff_modEq).mp h'
        rw [hx_order] at hpow; exact hpow
      have hi : ((i.val : ℕ) : ZMod 8) = i := ZMod.natCast_zmod_val i
      have hj : ((j.val : ℕ) : ZMod 8) = j := ZMod.natCast_zmod_val j
      have heq : ((i.val : ℕ) : ZMod 8) = ((j.val : ℕ) : ZMod 8) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
      rw [hi, hj] at heq
      rw [heq]
  have hQ_card : Nat.card (QuaternionGroup 4) = 16 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hf_bij : Function.Bijective f_fun := by
    apply hf_inj.bijective_of_nat_card_le
    rw [hQ_card, h_sixteen]
  exact ⟨(MulEquiv.ofBijective F hf_bij).symm⟩

include h_sixteen in
/-- Sub-stub: when `|G| = 16` and `|Z(G)| = 2`, the quotient `G/Z(G)` is
isomorphic to the dihedral group `D_4` of order 8. This is the structural
reduction of `thm:center-two`: cyclic and abelian-quotient cases are ruled out
via `cyclic_center_quotient_abelian` and
`two_abelian_subgroups_force_center_four`, and the elementary-abelian quotient
is ruled out by `thm:no-Z2cubed-quotient` (not yet formalized). -/
theorem center_two_quotient_dihedral (h : Nat.card (Subgroup.center G) = 2) :
    Nonempty ((G ⧸ Subgroup.center G) ≃* DihedralGroup 4) := by
  -- Step 1: |G/Z(G)| = 8.
  have hQ : Nat.card (G ⧸ Subgroup.center G) = 8 := by
    have hmul := OrderSixteen.Prelim.quotient_by_center_card G
    rw [h, h_sixteen] at hmul
    omega
  -- A reusable helper. Given two distinct cyclic order-4 subgroups M₁, M₂ ≤ G/Z,
  -- the pullbacks K₁, K₂ ≤ G are distinct, abelian, of order 8.
  have helper : ∀ (M₁ M₂ : Subgroup (G ⧸ Subgroup.center G)),
      M₁ ≠ M₂ → Nat.card M₁ = 4 → Nat.card M₂ = 4 →
      IsCyclic M₁ → IsCyclic M₂ → False := by
    intro M₁ M₂ hne hM₁card hM₂card hM₁cyc hM₂cyc
    set qmap : G →* G ⧸ Subgroup.center G := QuotientGroup.mk' (Subgroup.center G)
      with hqmap_def
    set K₁ : Subgroup G := M₁.comap qmap with hK₁_def
    set K₂ : Subgroup G := M₂.comap qmap with hK₂_def
    -- Z ≤ K_i.
    have hZ_le_K : ∀ M : Subgroup (G ⧸ Subgroup.center G),
        Subgroup.center G ≤ M.comap qmap := by
      intro M z hz
      simp only [Subgroup.mem_comap]
      rw [show qmap z = 1 from (QuotientGroup.eq_one_iff z).mpr hz]
      exact M.one_mem
    have hZK₁ : Subgroup.center G ≤ K₁ := hZ_le_K M₁
    have hZK₂ : Subgroup.center G ≤ K₂ := hZ_le_K M₂
    -- Cardinality: |K_i| = 8.
    have qmap_surj : Function.Surjective qmap :=
      QuotientGroup.mk'_surjective (Subgroup.center G)
    have card_K : ∀ (M : Subgroup (G ⧸ Subgroup.center G)), Nat.card M = 4 →
        Nat.card (M.comap qmap) = 8 := by
      intro M hM
      have hidx_comap : (M.comap qmap).index = M.index := by
        rw [Subgroup.index_comap]
        have hrange : qmap.range = ⊤ := MonoidHom.range_eq_top.mpr qmap_surj
        rw [hrange, Subgroup.relIndex_top_right]
      have hM_idx : M.index * Nat.card M = Nat.card (G ⧸ Subgroup.center G) :=
        Subgroup.index_mul_card M
      have hM_idx2 : M.index = 2 := by rw [hM, hQ] at hM_idx; omega
      have hK_idx : (M.comap qmap).index * Nat.card (M.comap qmap) = Nat.card G :=
        Subgroup.index_mul_card _
      rw [hidx_comap, hM_idx2, h_sixteen] at hK_idx
      omega
    have hK₁card : Nat.card K₁ = 8 := card_K M₁ hM₁card
    have hK₂card : Nat.card K₂ = 8 := card_K M₂ hM₂card
    -- K_i is abelian.
    have K_abelian : ∀ (M : Subgroup (G ⧸ Subgroup.center G)) (_ : IsCyclic M),
        ∀ a b : (M.comap qmap), a * b = b * a := by
      intro M hMcyc
      apply OrderSixteen.Prelim.subgroup_abelian_of_cyclic_quot_center
      set K := M.comap qmap with hK_def
      let f : K →* (G ⧸ Subgroup.center G) := qmap.comp K.subtype
      have hf_range : f.range = M := by
        ext y
        simp only [MonoidHom.mem_range, MonoidHom.coe_comp, Function.comp_apply,
          Subgroup.coe_subtype, f]
        constructor
        · rintro ⟨⟨x, hxK⟩, rfl⟩
          exact hxK
        · intro hyM
          obtain ⟨x, rfl⟩ := qmap_surj y
          exact ⟨⟨x, hyM⟩, rfl⟩
      have hf_ker : f.ker = (Subgroup.center G).subgroupOf K := by
        ext x
        constructor
        · intro hx
          rw [MonoidHom.mem_ker] at hx
          rw [Subgroup.mem_subgroupOf]
          exact (QuotientGroup.eq_one_iff (x : G)).mp hx
        · intro hx
          rw [Subgroup.mem_subgroupOf] at hx
          rw [MonoidHom.mem_ker]
          exact (QuotientGroup.eq_one_iff (x : G)).mpr hx
      haveI : IsCyclic f.range := by
        rw [show f.range = M from hf_range]
        exact hMcyc
      have hf_ker' : (Subgroup.center G).subgroupOf K = f.ker := hf_ker.symm
      haveI hker_normal : ((Subgroup.center G).subgroupOf K).Normal := by
        rw [hf_ker']
        infer_instance
      have iso : K ⧸ (Subgroup.center G).subgroupOf K ≃* f.range := by
        refine (QuotientGroup.quotientMulEquivOfEq hf_ker.symm).trans ?_
        exact QuotientGroup.quotientKerEquivRange f
      exact isCyclic_of_surjective iso.symm iso.symm.surjective
    have hK₁ab := K_abelian M₁ hM₁cyc
    have hK₂ab := K_abelian M₂ hM₂cyc
    -- K₁ ≠ K₂ via the correspondence theorem.
    have hK_ne : K₁ ≠ K₂ := by
      intro hKeq
      apply hne
      have hiso : (QuotientGroup.comapMk'OrderIso (Subgroup.center G)) M₁
          = (QuotientGroup.comapMk'OrderIso (Subgroup.center G)) M₂ := by
        apply Subtype.ext
        exact hKeq
      exact (QuotientGroup.comapMk'OrderIso (Subgroup.center G)).injective hiso
    -- Apply two_abelian_subgroups_force_center_four.
    have h_center_ge_4 : 4 ≤ Nat.card (Subgroup.center G) :=
      OrderSixteen.Prelim.two_abelian_subgroups_force_center_four h_sixteen
        K₁ K₂ hK₁card hK₂card hK_ne hK₁ab hK₂ab
    omega
  -- Step 2: Apply the order-8 classification to G/Z(G).
  rcases OrderSixteen.Prelim.order_eight_classification hQ with
    h1 | h2 | h3 | h4 | h5
  · -- Case 1: G/Z(G) ≅ C_8, contradicting `order_eight_quotient_not_cyclic`.
    exfalso
    obtain ⟨φ⟩ := h1
    have hcyc : IsCyclic (G ⧸ Subgroup.center G) :=
      isCyclic_of_surjective φ.symm φ.symm.surjective
    exact OrderSixteen.Prelim.order_eight_quotient_not_cyclic h_sixteen h hcyc
  · -- Case 2: G/Z(G) ≅ C_4 × C_2 — produce two distinct cyclic order-4 subgroups.
    exfalso
    obtain ⟨φ⟩ := h2
    let e₁ : CyclicGroup 4 × CyclicGroup 2 :=
      (Multiplicative.ofAdd (1 : ZMod 4), 1)
    let e₂ : CyclicGroup 4 × CyclicGroup 2 :=
      (Multiplicative.ofAdd (1 : ZMod 4), Multiplicative.ofAdd (1 : ZMod 2))
    let g₁ : G ⧸ Subgroup.center G := φ.symm e₁
    let g₂ : G ⧸ Subgroup.center G := φ.symm e₂
    let M₁ : Subgroup (G ⧸ Subgroup.center G) := Subgroup.zpowers g₁
    let M₂ : Subgroup (G ⧸ Subgroup.center G) := Subgroup.zpowers g₂
    have he₁_order : orderOf e₁ = 4 := by
      change orderOf ((Multiplicative.ofAdd (1 : ZMod 4)),
        (1 : CyclicGroup 2)) = 4
      rw [Prod.orderOf, orderOf_one, orderOf_ofAdd_eq_addOrderOf,
        ZMod.addOrderOf_one]
      decide
    have he₂_order : orderOf e₂ = 4 := by
      change orderOf ((Multiplicative.ofAdd (1 : ZMod 4)),
        (Multiplicative.ofAdd (1 : ZMod 2))) = 4
      rw [Prod.orderOf, orderOf_ofAdd_eq_addOrderOf,
        orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one,
        ZMod.addOrderOf_one]
      decide
    have hg₁_order : orderOf g₁ = 4 := by
      change orderOf (φ.symm e₁) = 4
      rw [show (φ.symm e₁ : G ⧸ Subgroup.center G) = φ.symm.toMonoidHom e₁ from rfl,
        orderOf_injective φ.symm.toMonoidHom φ.symm.injective, he₁_order]
    have hg₂_order : orderOf g₂ = 4 := by
      change orderOf (φ.symm e₂) = 4
      rw [show (φ.symm e₂ : G ⧸ Subgroup.center G) = φ.symm.toMonoidHom e₂ from rfl,
        orderOf_injective φ.symm.toMonoidHom φ.symm.injective, he₂_order]
    have hM₁_card : Nat.card M₁ = 4 := by
      change Nat.card (Subgroup.zpowers g₁) = 4
      rw [Nat.card_zpowers, hg₁_order]
    have hM₂_card : Nat.card M₂ = 4 := by
      change Nat.card (Subgroup.zpowers g₂) = 4
      rw [Nat.card_zpowers, hg₂_order]
    have hM₁_cyc : IsCyclic M₁ := by
      change IsCyclic (Subgroup.zpowers g₁)
      infer_instance
    have hM₂_cyc : IsCyclic M₂ := by
      change IsCyclic (Subgroup.zpowers g₂)
      infer_instance
    have hM_ne : M₁ ≠ M₂ := by
      intro hMeq
      have : (Subgroup.zpowers e₁ : Subgroup (CyclicGroup 4 × CyclicGroup 2))
          = Subgroup.zpowers e₂ := by
        have hmap_lemma : ∀ x : G ⧸ Subgroup.center G,
            Subgroup.map φ.toMonoidHom (Subgroup.zpowers x) =
              Subgroup.zpowers (φ x) := by
          intro x
          exact (MonoidHom.map_zpowers φ.toMonoidHom x).symm ▸ rfl
        have := congr_arg (Subgroup.map φ.toMonoidHom) hMeq
        rw [hmap_lemma, hmap_lemma, show φ g₁ = e₁ from φ.apply_symm_apply e₁,
          show φ g₂ = e₂ from φ.apply_symm_apply e₂] at this
        exact this
      have he₂_mem : e₂ ∈ Subgroup.zpowers e₁ := by
        rw [this]; exact Subgroup.mem_zpowers e₂
      obtain ⟨k, hk⟩ := he₂_mem
      have h_snd : (e₁ ^ k).2 = (1 : CyclicGroup 2) := by
        rw [Prod.pow_snd]
        change (1 : CyclicGroup 2) ^ k = 1
        exact one_zpow k
      have h_e2_snd : e₂.2 = Multiplicative.ofAdd (1 : ZMod 2) := rfl
      have hofadd : (Multiplicative.ofAdd (1 : ZMod 2) : CyclicGroup 2) = 1 := by
        rw [← h_e2_snd, ← hk]
        exact h_snd
      have hzmod : (1 : ZMod 2) = 0 :=
        Multiplicative.ofAdd.injective hofadd
      exact absurd hzmod (by decide)
    exact helper M₁ M₂ hM_ne hM₁_card hM₂_card hM₁_cyc hM₂_cyc
  · -- Case 3: G/Z(G) ≅ C_2 × C_2 × C_2, ruled out by `no_Z2cubed_quotient`.
    exact absurd h3 (OrderSixteen.Prelim.no_Z2cubed_quotient h_sixteen h)
  · -- Case 4: G/Z(G) ≅ D_4. This is the goal.
    exact h4
  · -- Case 5: G/Z(G) ≅ Q_8 — produce two distinct cyclic order-4 subgroups.
    exfalso
    obtain ⟨φ⟩ := h5
    let e₁ : QuaternionGroup 2 := QuaternionGroup.a 1
    let e₂ : QuaternionGroup 2 := QuaternionGroup.xa 0
    let g₁ : G ⧸ Subgroup.center G := φ.symm e₁
    let g₂ : G ⧸ Subgroup.center G := φ.symm e₂
    let M₁ : Subgroup (G ⧸ Subgroup.center G) := Subgroup.zpowers g₁
    let M₂ : Subgroup (G ⧸ Subgroup.center G) := Subgroup.zpowers g₂
    have he₁_order : orderOf e₁ = 4 := by
      change orderOf (QuaternionGroup.a (1 : ZMod (2 * 2))) = 4
      rw [QuaternionGroup.orderOf_a]
      decide
    have he₂_order : orderOf e₂ = 4 := by
      change orderOf (QuaternionGroup.xa (0 : ZMod (2 * 2))) = 4
      exact QuaternionGroup.orderOf_xa _
    have hg₁_order : orderOf g₁ = 4 := by
      change orderOf (φ.symm e₁) = 4
      rw [show (φ.symm e₁ : G ⧸ Subgroup.center G) = φ.symm.toMonoidHom e₁ from rfl,
        orderOf_injective φ.symm.toMonoidHom φ.symm.injective, he₁_order]
    have hg₂_order : orderOf g₂ = 4 := by
      change orderOf (φ.symm e₂) = 4
      rw [show (φ.symm e₂ : G ⧸ Subgroup.center G) = φ.symm.toMonoidHom e₂ from rfl,
        orderOf_injective φ.symm.toMonoidHom φ.symm.injective, he₂_order]
    have hM₁_card : Nat.card M₁ = 4 := by
      change Nat.card (Subgroup.zpowers g₁) = 4
      rw [Nat.card_zpowers, hg₁_order]
    have hM₂_card : Nat.card M₂ = 4 := by
      change Nat.card (Subgroup.zpowers g₂) = 4
      rw [Nat.card_zpowers, hg₂_order]
    have hM₁_cyc : IsCyclic M₁ := by
      change IsCyclic (Subgroup.zpowers g₁)
      infer_instance
    have hM₂_cyc : IsCyclic M₂ := by
      change IsCyclic (Subgroup.zpowers g₂)
      infer_instance
    have hM_ne : M₁ ≠ M₂ := by
      intro hMeq
      have hmap_lemma : ∀ x : G ⧸ Subgroup.center G,
          Subgroup.map φ.toMonoidHom (Subgroup.zpowers x) =
            Subgroup.zpowers (φ x) := by
        intro x
        exact (MonoidHom.map_zpowers φ.toMonoidHom x).symm ▸ rfl
      have hT_eq : (Subgroup.zpowers e₁ : Subgroup (QuaternionGroup 2))
          = Subgroup.zpowers e₂ := by
        have := congr_arg (Subgroup.map φ.toMonoidHom) hMeq
        rw [hmap_lemma, hmap_lemma, show φ g₁ = e₁ from φ.apply_symm_apply e₁,
          show φ g₂ = e₂ from φ.apply_symm_apply e₂] at this
        exact this
      have he₂_mem : e₂ ∈ Subgroup.zpowers e₁ := by
        rw [hT_eq]; exact Subgroup.mem_zpowers e₂
      have he₁_fin : IsOfFinOrder e₁ := by
        rw [← orderOf_pos_iff, he₁_order]; norm_num
      rw [← he₁_fin.mem_powers_iff_mem_zpowers] at he₂_mem
      obtain ⟨k, hk⟩ := he₂_mem
      have ha_pow : (QuaternionGroup.a (1 : ZMod (2 * 2))) ^ k =
          QuaternionGroup.a (k : ZMod (2 * 2)) :=
        QuaternionGroup.a_one_pow k
      have heq : (QuaternionGroup.a (k : ZMod (2 * 2)) : QuaternionGroup 2) =
          QuaternionGroup.xa (0 : ZMod (2 * 2)) := ha_pow.symm.trans hk
      cases heq
    exact helper M₁ M₂ hM_ne hM₁_card hM₂_card hM₁_cyc hM₂_cyc

/-- Helper: in DihedralGroup 4, every element raised to the 4th power is 1. -/
private lemma D4_pow4_eq_one (g : DihedralGroup 4) : g ^ 4 = 1 := by
  match g with
  | DihedralGroup.r i =>
    rw [DihedralGroup.r_pow]
    have h4 : ((4 : ℕ) : ZMod 4) = 0 := by decide
    rw [show (i * (4 : ℕ) : ZMod 4) = 0 from by rw [h4, mul_zero]]
    rfl
  | DihedralGroup.sr i =>
    have h2 : DihedralGroup.sr i ^ 2 = 1 := by
      rw [sq]; exact DihedralGroup.sr_mul_self i
    calc (DihedralGroup.sr i) ^ 4
        = (DihedralGroup.sr i ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 ^ 2 := by rw [h2]
      _ = 1 := one_pow 2

include h_sixteen in
/-- Sub-stub: given `|G| = 16`, `|Z(G)| = 2`, and `G/Z(G) ≅ D_4`, exactly one
of the three structural witness pairs exists in `G`, matching the dihedral,
semidihedral, or quaternion leaf case. This is the witness-extraction step of
`thm:center-two`, using `lem:one-Gi-cyclic-order-eight` to obtain a cyclic
order-8 subgroup of `G` and the order-8 classification on the two non-abelian
order-8 subgroups to identify the conjugation rule. -/
theorem center_two_witness (h : Nat.card (Subgroup.center G) = 2)
    (_hquot : Nonempty ((G ⧸ Subgroup.center G) ≃* DihedralGroup 4)) :
    (∃ x y : G, orderOf x = 8 ∧ orderOf y = 2 ∧
        y ∉ Subgroup.zpowers x ∧ y * x * y = x⁻¹) ∨
    (∃ x y : G, orderOf x = 8 ∧ orderOf y = 2 ∧
        y ∉ Subgroup.zpowers x ∧ y * x * y = x ^ 3) ∨
    (∃ x y : G, orderOf x = 8 ∧ y ^ 2 = x ^ 4 ∧
        y ∉ Subgroup.zpowers x ∧ y * x * y⁻¹ = x⁻¹) := by
  -- Step 1: get x with orderOf x = 8.
  obtain ⟨x, hx⟩ := Prelim.one_Gi_cyclic_order_eight h_sixteen h _hquot
  -- Useful: x^8 = 1.
  have hx8 : x ^ 8 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  -- Step 2: the cyclic subgroup ⟨x⟩ has cardinality 8 and is normal of index 2.
  have hX_card : Nat.card (Subgroup.zpowers x) = 8 := by
    rw [Nat.card_zpowers, hx]
  have hX_index : (Subgroup.zpowers x).index = 2 := by
    have h_index_mul := Subgroup.index_mul_card (Subgroup.zpowers x)
    rw [hX_card, h_sixteen] at h_index_mul
    omega
  haveI hX_normal : (Subgroup.zpowers x).Normal :=
    Subgroup.normal_of_index_eq_two hX_index
  -- Step 3: pick y ∉ ⟨x⟩.
  have hX_ne_top : Subgroup.zpowers x ≠ ⊤ := by
    intro h_eq
    have : Nat.card (Subgroup.zpowers x) = Nat.card G := by
      rw [h_eq, Nat.card_congr Subgroup.topEquiv.toEquiv]
    rw [hX_card, h_sixteen] at this
    omega
  obtain ⟨y, hy_notmem⟩ : ∃ y : G, y ∉ Subgroup.zpowers x := by
    by_contra h_all
    push_neg at h_all
    apply hX_ne_top
    rw [Subgroup.eq_top_iff']
    exact h_all
  -- Set up the iso.
  obtain ⟨φ⟩ := _hquot
  set a : DihedralGroup 4 := φ ((x : G ⧸ Subgroup.center G)) with ha_def
  set b : DihedralGroup 4 := φ ((y : G ⧸ Subgroup.center G)) with hb_def
  -- Step 4: x^4 ∈ Z(G).
  have hx4_center : x ^ 4 ∈ Subgroup.center G := by
    have h_a4 : a ^ 4 = 1 := D4_pow4_eq_one a
    have h_xpow_eq_one : ((x : G ⧸ Subgroup.center G)) ^ 4 = 1 := by
      apply φ.injective
      rw [map_pow, ← ha_def, h_a4, map_one]
    have h_x4_quot : ((x ^ 4 : G) : G ⧸ Subgroup.center G) = 1 := by
      rw [← h_xpow_eq_one]; rfl
    exact (QuotientGroup.eq_one_iff _).mp h_x4_quot
  -- x^4 has order 2 in G.
  have hx4_order : orderOf (x ^ 4) = 2 := by
    rw [orderOf_pow' x (by norm_num : (4 : ℕ) ≠ 0), hx]
    decide
  have hx4_ne_one : x ^ 4 ≠ 1 := by
    intro h_eq
    have : orderOf (x ^ 4) = 1 := by rw [h_eq]; exact orderOf_one
    rw [hx4_order] at this
    omega
  -- Z(G) = {1, x^4}.
  have hcenter_mem_iff : ∀ z : G, z ∈ Subgroup.center G → z = 1 ∨ z = x ^ 4 := by
    intro z hz
    have hcenter_card : Nat.card (Subgroup.center G) = 2 := h
    rw [Nat.card_eq_two_iff' (1 : Subgroup.center G)] at hcenter_card
    obtain ⟨w, _, hw_unique⟩ := hcenter_card
    by_cases hz_eq : z = 1
    · exact Or.inl hz_eq
    right
    have h1 : (⟨z, hz⟩ : Subgroup.center G) ≠ 1 := by
      intro heq
      apply hz_eq
      have := congrArg Subtype.val heq
      simpa using this
    have h2 : (⟨x ^ 4, hx4_center⟩ : Subgroup.center G) ≠ 1 := by
      intro heq
      apply hx4_ne_one
      have := congrArg Subtype.val heq
      simpa using this
    have h3 : (⟨z, hz⟩ : Subgroup.center G) = (⟨x ^ 4, hx4_center⟩ : Subgroup.center G) := by
      rw [hw_unique _ h1, hw_unique _ h2]
    have := congrArg Subtype.val h3
    simpa using this
  -- Z(G) ⊆ ⟨x⟩.
  have h_Z_sub : ∀ z ∈ Subgroup.center G, z ∈ Subgroup.zpowers x := by
    intro z hz
    rcases hcenter_mem_iff z hz with rfl | rfl
    · exact one_mem _
    · exact pow_mem (Subgroup.mem_zpowers x) 4
  -- Step 5: x^2 ∉ Z(G).
  have hx2_notin_Z : x ^ 2 ∉ Subgroup.center G := by
    intro h_in
    rcases hcenter_mem_iff _ h_in with h_eq | h_eq
    · -- x^2 = 1 contradicts orderOf x = 8.
      have : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h_eq
      rw [hx] at this; omega
    · -- x^2 = x^4 means x^2 = 1, again contradiction.
      have h2 : x ^ 2 = 1 := by
        have hself : (1 : G) = x ^ 2 := by
          calc (1 : G) = x ^ 2 * x⁻¹ ^ 2 := by group
            _ = x ^ 4 * x⁻¹ ^ 2 := by rw [h_eq]
            _ = x ^ 2 := by group
        exact hself.symm
      have : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h2
      rw [hx] at this; omega
  -- Step 6: a has order 4 in D_4.
  have ha_pow2_ne_one : a ^ 2 ≠ 1 := by
    intro heq
    apply hx2_notin_Z
    have h_x2_quot : ((x ^ 2 : G) : G ⧸ Subgroup.center G) = 1 := by
      have h_a_pow_inj : ((x : G ⧸ Subgroup.center G)) ^ 2 = 1 := by
        apply φ.injective
        rw [map_pow, ← ha_def, heq, map_one]
      rw [← h_a_pow_inj]; rfl
    exact (QuotientGroup.eq_one_iff _).mp h_x2_quot
  have ha_pow4_eq_one : a ^ 4 = 1 := D4_pow4_eq_one a
  have ha_order : orderOf a = 4 := by
    have h_dvd_4 : orderOf a ∣ 4 := orderOf_dvd_of_pow_eq_one ha_pow4_eq_one
    have h_not_dvd_2 : ¬ orderOf a ∣ 2 := by
      intro hdvd
      exact ha_pow2_ne_one (orderOf_dvd_iff_pow_eq_one.mp hdvd)
    have h_pos : 0 < orderOf a := orderOf_pos a
    have h_le : orderOf a ≤ 4 := Nat.le_of_dvd (by norm_num) h_dvd_4
    interval_cases (orderOf a)
    · exfalso; apply h_not_dvd_2; exact one_dvd 2
    · exfalso; apply h_not_dvd_2; rfl
    · exfalso; omega
    · rfl
  -- Step 7: b ∉ zpowers a.
  have hb_notin_pow_a : b ∉ Subgroup.zpowers a := by
    intro hb_mem
    apply hy_notmem
    obtain ⟨n, hn⟩ := hb_mem
    -- b = a^n, so φ(↑y) = φ(↑x)^n = φ((↑x)^n) = φ(↑(x^n)).
    have hy_eq : ((y : G ⧸ Subgroup.center G)) = ((x ^ n : G) : G ⧸ Subgroup.center G) := by
      apply φ.injective
      have : a ^ n = b := hn
      have : φ ((x : G ⧸ Subgroup.center G)) ^ n = φ ((y : G ⧸ Subgroup.center G)) := by
        rw [← ha_def, ← hb_def]; exact hn
      have h_x_pow : ((x : G ⧸ Subgroup.center G)) ^ n =
          ((x ^ n : G) : G ⧸ Subgroup.center G) := by rfl
      rw [← h_x_pow, map_zpow]
      exact this.symm
    have h_quot_eq : ((y * (x ^ n)⁻¹ : G) : G ⧸ Subgroup.center G) = 1 := by
      rw [QuotientGroup.mk_mul, hy_eq, QuotientGroup.mk_inv]
      exact mul_inv_cancel _
    have h_in_Z : y * (x ^ n)⁻¹ ∈ Subgroup.center G :=
      (QuotientGroup.eq_one_iff _).mp h_quot_eq
    have h_yx_inv_in : y * (x ^ n)⁻¹ ∈ Subgroup.zpowers x := h_Z_sub _ h_in_Z
    have : y = (y * (x ^ n)⁻¹) * x ^ n := by group
    rw [this]
    exact Subgroup.mul_mem _ h_yx_inv_in (zpow_mem (Subgroup.mem_zpowers x) n)
  -- Step 8: Show b * a * b⁻¹ * a = 1 and b ^ 2 = 1 in D_4.
  -- Helper: any element of order 4 in D_4 is a rotation r ia.
  -- Helper: b is a reflection sr ib (since not in zpowers a).
  -- We use the following key facts about D_4 (DihedralGroup 4):
  -- (i) sr ib * (r ia) * (sr ib)⁻¹ = r (-ia).
  -- (ii) (sr ib)^2 = 1.
  have h_main : b * a * b⁻¹ * a = 1 ∧ b ^ 2 = 1 := by
    -- Generic helper for reflections in DihedralGroup n.
    have key : ∀ ia ib : ZMod 4,
        (DihedralGroup.sr ib : DihedralGroup 4) * DihedralGroup.r ia *
          (DihedralGroup.sr ib)⁻¹ * DihedralGroup.r ia = 1 ∧
        (DihedralGroup.sr ib : DihedralGroup 4) ^ 2 = 1 := by
      intro ia ib
      have hsr_inv : (DihedralGroup.sr ib : DihedralGroup 4)⁻¹ = DihedralGroup.sr ib := by
        rw [inv_eq_iff_mul_eq_one]; exact DihedralGroup.sr_mul_self ib
      refine ⟨?_, ?_⟩
      · rw [hsr_inv]
        rw [DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_r]
        show DihedralGroup.r (ib - (ib + ia) + ia) = 1
        have : ib - (ib + ia) + ia = 0 := by ring
        rw [this]; rfl
      · rw [sq]; exact DihedralGroup.sr_mul_self ib
    -- Now case split on a (must be `r ia`).
    have h_a_form : ∃ ia : ZMod 4, a = DihedralGroup.r ia := by
      cases h_a_match : a with
      | r ia => exact ⟨ia, rfl⟩
      | sr ia =>
        exfalso
        have : orderOf (DihedralGroup.sr ia : DihedralGroup 4) = 2 :=
          DihedralGroup.orderOf_sr ia
        rw [← h_a_match] at this
        rw [ha_order] at this; omega
    obtain ⟨ia, hai⟩ := h_a_form
    -- Now b is sr ib.
    have h_b_form : ∃ ib : ZMod 4, b = DihedralGroup.sr ib := by
      cases h_b_match : b with
      | r ib =>
        exfalso; apply hb_notin_pow_a
        rw [h_b_match, Subgroup.mem_zpowers_iff, hai]
        -- For r ia with orderOf = 4, ia.val ∈ {1, 3}.
        have h_ord_eq : orderOf (DihedralGroup.r ia : DihedralGroup 4) = 4 := by
          rw [← hai]; exact ha_order
        rw [DihedralGroup.orderOf_r] at h_ord_eq
        have h_gcd : Nat.gcd 4 ia.val = 1 := by
          have h_dvd : Nat.gcd 4 ia.val ∣ 4 := Nat.gcd_dvd_left _ _
          have h_mul : Nat.gcd 4 ia.val * (4 / Nat.gcd 4 ia.val) = 4 :=
            Nat.mul_div_cancel' h_dvd
          rw [h_ord_eq] at h_mul
          omega
        have h_ia_val_lt : ia.val < 4 := ZMod.val_lt ia
        have h_val_eq : ia.val = 1 ∨ ia.val = 3 := by
          interval_cases ia.val
          · simp at h_gcd
          · left; rfl
          · exfalso; norm_num at h_gcd
          · right; rfl
        have hia_eq : ia = (ia.val : ZMod 4) := (ZMod.natCast_zmod_val ia).symm
        rcases h_val_eq with hv | hv
        · -- ia = 1.
          have hia_one : ia = 1 := by rw [hia_eq, hv]; rfl
          rw [hia_one]
          refine ⟨(ib.val : ℤ), ?_⟩
          show DihedralGroup.r (1 : ZMod 4) ^ ((ib.val : ℤ) : ℤ) = DihedralGroup.r ib
          rw [show (DihedralGroup.r (1 : ZMod 4) : DihedralGroup 4) ^ ((ib.val : ℤ) : ℤ) =
              DihedralGroup.r ((1 : ZMod 4) * (ib.val : ℤ) : ZMod 4) from
              DihedralGroup.r_zpow 1 (ib.val : ℤ)]
          congr 1
          push_cast
          rw [one_mul]
          exact ZMod.natCast_zmod_val ib
        · -- ia = 3.
          have hia_three : ia = 3 := by rw [hia_eq, hv]; rfl
          rw [hia_three]
          refine ⟨(3 * ib.val : ℤ), ?_⟩
          rw [show (DihedralGroup.r (3 : ZMod 4) : DihedralGroup 4) ^ ((3 * ib.val : ℤ)) =
              DihedralGroup.r ((3 : ZMod 4) * (3 * ib.val : ℤ) : ZMod 4) from
              DihedralGroup.r_zpow 3 _]
          congr 1
          push_cast
          have h9 : (3 : ZMod 4) * 3 = 1 := by decide
          rw [show (3 : ZMod 4) * (3 * (ib.val : ZMod 4)) =
              ((3 : ZMod 4) * 3) * (ib.val : ZMod 4) from by ring]
          rw [h9, one_mul]
          exact ZMod.natCast_zmod_val ib
      | sr ib => exact ⟨ib, rfl⟩
    obtain ⟨ib, hbi⟩ := h_b_form
    rw [hai, hbi]
    exact key ia ib
  obtain ⟨h_conj, h_b2⟩ := h_main
  -- Derive y * x * y⁻¹ * x ∈ Z(G).
  have hyxyx_in_center : y * x * y⁻¹ * x ∈ Subgroup.center G := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply φ.injective
    rw [map_one]
    show φ ↑(y * x * y⁻¹ * x) = 1
    have : (↑(y * x * y⁻¹ * x) : G ⧸ Subgroup.center G) =
        (↑y) * (↑x) * (↑y)⁻¹ * (↑x) := by rfl
    rw [this, map_mul, map_mul, map_mul, map_inv, ← ha_def, ← hb_def]
    exact h_conj
  -- Derive y^2 ∈ Z(G).
  have hy2_center : y ^ 2 ∈ Subgroup.center G := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply φ.injective
    rw [map_one]
    show φ ↑(y ^ 2) = 1
    have : (↑(y ^ 2) : G ⧸ Subgroup.center G) = (↑y) ^ 2 := by rfl
    rw [this, map_pow, ← hb_def]
    exact h_b2
  -- Now y*x*y⁻¹*x ∈ Z(G) = {1, x^4}.
  have hyxyx_cases : y * x * y⁻¹ * x = 1 ∨ y * x * y⁻¹ * x = x ^ 4 :=
    hcenter_mem_iff _ hyxyx_in_center
  -- y*x*y⁻¹ ∈ {x⁻¹, x^3}.
  have hx3_eq : x ^ 4 * x⁻¹ = x ^ 3 := by
    rw [show (4 : ℕ) = 3 + 1 from by norm_num, pow_succ, mul_assoc, mul_inv_cancel, mul_one]
  have hconj_in_set : y * x * y⁻¹ = x ^ 3 ∨ y * x * y⁻¹ = x⁻¹ := by
    rcases hyxyx_cases with h_eq | h_eq
    · right
      have h_simp : y * x * y⁻¹ = (y * x * y⁻¹ * x) * x⁻¹ := by group
      rw [h_simp, h_eq, one_mul]
    · left
      have h_simp : y * x * y⁻¹ = (y * x * y⁻¹ * x) * x⁻¹ := by group
      rw [h_simp, h_eq, hx3_eq]
  -- y² ∈ Z(G) = {1, x^4}.
  have hy2_cases : y ^ 2 = 1 ∨ y ^ 2 = x ^ 4 := hcenter_mem_iff _ hy2_center
  -- Now case split.
  rcases hconj_in_set with hconj_x3 | hconj_inv
  · -- y * x * y⁻¹ = x^3.
    rcases hy2_cases with hy2_1 | hy2_x4
    · -- (B) semidihedral.
      refine Or.inr (Or.inl ⟨x, y, hx, ?_, hy_notmem, ?_⟩)
      · have hy_ne_one : y ≠ 1 := by
          intro h_eq
          apply hy_notmem
          rw [h_eq]; exact one_mem _
        exact orderOf_eq_prime hy2_1 hy_ne_one
      · have heq : y * x * y = (y * x * y⁻¹) * y ^ 2 := by group
        rw [heq, hconj_x3, hy2_1, mul_one]
    · -- (D) y² = x^4, y * x * y⁻¹ = x^3. Substitute y' = x * y to get semidihedral.
      have h_xpows : x * x ^ 3 * x ^ 4 = x ^ 8 := by
        rw [show x * x ^ 3 = x ^ 4 from by rw [show (4 : ℕ) = 1 + 3 from rfl, pow_add, pow_one],
            show x ^ 4 * x ^ 4 = x ^ 8 from by rw [← pow_add]]
      have h_xy_sq : (x * y) ^ 2 = 1 := by
        have heq1 : (x * y) ^ 2 = x * (y * x * y⁻¹) * y ^ 2 := by
          rw [sq]; group
        rw [heq1, hconj_x3, hy2_x4, h_xpows, hx8]
      refine Or.inr (Or.inl ⟨x, x * y, hx, ?_, ?_, ?_⟩)
      · have h_xy_ne_one : x * y ≠ 1 := by
          intro h_eq
          apply hy_notmem
          have : y = x⁻¹ := (mul_eq_one_iff_eq_inv'.mp h_eq)
          rw [this]
          exact Subgroup.inv_mem _ (Subgroup.mem_zpowers x)
        exact orderOf_eq_prime h_xy_sq h_xy_ne_one
      · intro h_in
        apply hy_notmem
        have hy_eq : y = x⁻¹ * (x * y) := by group
        rw [hy_eq]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)) h_in
      · have heq : (x * y) * x * (x * y) = (x * y) * x * (x * y)⁻¹ * (x * y) ^ 2 := by
          rw [sq]; group
        rw [heq, h_xy_sq, mul_one]
        have heq2 : (x * y) * x * (x * y)⁻¹ = x * (y * x * y⁻¹) * x⁻¹ := by group
        rw [heq2, hconj_x3]
        have h_assoc : x * x ^ 3 * x⁻¹ = x ^ 4 * x⁻¹ := by
          rw [show (4 : ℕ) = 1 + 3 from rfl, pow_add, pow_one]
        rw [h_assoc, hx3_eq]
  · -- y * x * y⁻¹ = x⁻¹.
    rcases hy2_cases with hy2_1 | hy2_x4
    · -- (A) dihedral.
      refine Or.inl ⟨x, y, hx, ?_, hy_notmem, ?_⟩
      · have hy_ne_one : y ≠ 1 := by
          intro h_eq
          apply hy_notmem
          rw [h_eq]; exact one_mem _
        exact orderOf_eq_prime hy2_1 hy_ne_one
      · have heq : y * x * y = (y * x * y⁻¹) * y ^ 2 := by group
        rw [heq, hconj_inv, hy2_1, mul_one]
    · -- (C) quaternion.
      exact Or.inr (Or.inr ⟨x, y, hx, hy2_x4, hy_notmem, hconj_inv⟩)

include h_sixteen in
theorem center_order_two (h : Nat.card (Subgroup.center G) = 2)
  : Nonempty (G ≃* DihedralGroup 8) ∨
    Nonempty (G ≃* CyclicGroup 8 ⋊[c2OnC8Pow3] CyclicGroup 2) ∨
    Nonempty (G ≃* QuaternionGroup 4)
  := by
  -- Step 1: reduce to the structural fact `G/Z(G) ≅ D_4`.
  have hquot : Nonempty ((G ⧸ Subgroup.center G) ≃* DihedralGroup 4) :=
    center_two_quotient_dihedral (h_sixteen := h_sixteen) G h
  -- Step 2: extract one of three structural witness pairs.
  obtain (hd | hs | hq) :=
    center_two_witness (h_sixteen := h_sixteen) G h hquot
  · -- Dihedral case.
    obtain ⟨x, y, hx, hy, hyx, hrel⟩ := hd
    exact Or.inl
      (center_two_dihedral (h_sixteen := h_sixteen) G x hx y hy hyx hrel)
  · -- Semidihedral case.
    obtain ⟨x, y, hx, hy, hyx, hrel⟩ := hs
    exact Or.inr (Or.inl
      (center_two_semidihedral (h_sixteen := h_sixteen) G x hx y hy hyx hrel))
  · -- Quaternion case.
    obtain ⟨x, y, hx, hys, hyx, hrel⟩ := hq
    exact Or.inr (Or.inr
      (center_two_quaternion (h_sixteen := h_sixteen) G x hx y hys hyx hrel))

end OrderSixteen

theorem sixteen_classification {G : Type*} [Group G] (h_sixteen : Nat.card G = 16)
  : ∃ i : Nat, ∃ hv : ValidIndex 16 i,
    haveI : ValidIndex 16 i := hv
    Nonempty (MulEquiv G (retrieve 16 i))
  := by
  haveI h_finite : Finite G := Nat.finite_of_card_ne_zero (by rw [h_sixteen]; norm_num)
  haveI h_nontrivial : Nontrivial G := by
    haveI : Fintype G := Fintype.ofFinite G
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, h_sixteen]
    norm_num
  have h_2group : IsPGroup 2 G :=
    IsPGroup.of_card (show Nat.card G = 2 ^ 4 from by rw [h_sixteen]; norm_num)
  haveI h_center_nontrivial : Nontrivial ↥(Subgroup.center G) :=
    IsPGroup.center_nontrivial h_2group
  have h_center_gt_one : 1 < Nat.card ↥(Subgroup.center G) := Finite.one_lt_card
  have h_center_dvd : Nat.card ↥(Subgroup.center G) ∣ 16 := by
    have := Subgroup.card_subgroup_dvd_card (Subgroup.center G)
    rwa [h_sixteen] at this
  obtain ⟨k, hk_le, hk_eq⟩ : ∃ k ≤ 4, Nat.card ↥(Subgroup.center G) = 2 ^ k := by
    rwa [show (16 : ℕ) = 2 ^ 4 from by norm_num,
         Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)] at h_center_dvd
  interval_cases k
  · -- k = 0: |Z(G)| = 1, contradicts nontrivial center
    simp only [pow_zero] at hk_eq; linarith
  · -- k = 1: |Z(G)| = 2
    norm_num at hk_eq
    obtain (hiso | hiso | hiso) :=
      OrderSixteen.center_order_two (h_sixteen := h_sixteen) G hk_eq
    · exact ⟨7, by decide, hiso⟩
    · exact ⟨8, by decide, hiso⟩
    · exact ⟨9, by decide, hiso⟩
  · -- k = 2: |Z(G)| = 4
    norm_num at hk_eq
    obtain (hiso | hiso | hiso | hiso | hiso | hiso) :=
      OrderSixteen.center_order_four (h_sixteen := h_sixteen) G hk_eq
    · exact ⟨3, by decide, hiso⟩
    · exact ⟨4, by decide, hiso⟩
    · exact ⟨6, by decide, hiso⟩
    · exact ⟨11, by decide, hiso⟩
    · exact ⟨12, by decide, hiso⟩
    · exact ⟨13, by decide, hiso⟩
  · -- k = 3: |Z(G)| = 8, impossible (center_order_eight returns False)
    norm_num at hk_eq
    exact (OrderSixteen.center_order_eight (h_sixteen := h_sixteen) G hk_eq).elim
  · -- k = 4: |Z(G)| = 16, G is abelian
    norm_num at hk_eq
    obtain (hiso | hiso | hiso | hiso | hiso) :=
      OrderSixteen.center_order_sixteen (h_sixteen := h_sixteen) G hk_eq
    · exact ⟨1, by decide, hiso⟩
    · exact ⟨5, by decide, hiso⟩
    · exact ⟨2, by decide, hiso⟩
    · exact ⟨10, by decide, hiso⟩
    · exact ⟨14, by decide, hiso⟩
