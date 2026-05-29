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

theorem center_order_four (h : Nat.card (Subgroup.center G) = 4)
  : Nonempty (G ≃* (CyclicGroup 2 × CyclicGroup 2) ⋊[c4OnC2sqSwap] CyclicGroup 4) ∨
    Nonempty (G ≃* CyclicGroup 4 ⋊[c4OnC4Inv] CyclicGroup 4) ∨
    Nonempty (G ≃* CyclicGroup 8 ⋊[c2OnC8Pow5] CyclicGroup 2) ∨
    Nonempty (G ≃* CyclicGroup 2 × DihedralGroup 4) ∨
    Nonempty (G ≃* CyclicGroup 2 × QuaternionGroup 2) ∨
    Nonempty (G ≃* (CyclicGroup 4 × CyclicGroup 2) ⋊[c2OnK8Psi6] CyclicGroup 2)
  := by
  sorry

theorem center_order_two (h : Nat.card (Subgroup.center G) = 2)
  : Nonempty (G ≃* DihedralGroup 8) ∨
    Nonempty (G ≃* CyclicGroup 8 ⋊[c2OnC8Pow3] CyclicGroup 2) ∨
    Nonempty (G ≃* QuaternionGroup 4)
  := by
  sorry

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
    obtain (hiso | hiso | hiso) := OrderSixteen.center_order_two G hk_eq
    · exact ⟨7, by decide, hiso⟩
    · exact ⟨8, by decide, hiso⟩
    · exact ⟨9, by decide, hiso⟩
  · -- k = 2: |Z(G)| = 4
    norm_num at hk_eq
    obtain (hiso | hiso | hiso | hiso | hiso | hiso) := OrderSixteen.center_order_four G hk_eq
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
