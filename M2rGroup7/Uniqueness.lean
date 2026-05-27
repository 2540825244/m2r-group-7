import «M2rGroup7».SmallGroupsLibrary

universe u u' v

structure GroupInvariant (α : Type u) [DecidableEq α] where
  eval (K : Type v) [Group K] [Fintype K] [DecidableEq K] : α
  preservation {K L : Type v}
    [Group K] [Group L] [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]
    (iso : K ≃* L) : eval K = eval L

def combine {α : Type u} {β : Type u'} [DecidableEq α] [DecidableEq β]
  (inv : GroupInvariant α) (inv' : GroupInvariant β)
  : GroupInvariant (α × β) where
    eval K _ _ _ := ⟨inv.eval K, inv'.eval K⟩
    preservation e := by
      congr 1
      · exact inv.preservation e
      · exact inv'.preservation e

infixl:65 " ⊗ " => combine

lemma not_iso_by {G H : Type v}
  [Group G] [Group H] [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
  {α : Type u} [DecidableEq α]
  (inv : GroupInvariant α)
  (h_inv_neq : inv.eval G ≠ inv.eval H)
  : IsEmpty (G ≃* H) := by
  contrapose! h_inv_neq with hiso
  exact inv.preservation Classical.ofNonempty


def trivialInv : GroupInvariant Unit where
  eval _ _ _ _ := ()
  preservation _ := by tauto

def orderInv : GroupInvariant Nat where
  eval K _ _ _ := Fintype.card K
  preservation iso := Fintype.card_of_bijective (iso.bijective)

noncomputable def exponentInv : GroupInvariant Nat where
  eval K _ _ _ := Monoid.exponent K
  preservation e := Monoid.exponent_eq_of_mulEquiv e

-- ∃ x, x^k ≠ 1  (decidable for any Fintype with DecidableEq)
-- hasPowerNotOneInv 2 : true for C4 (generator has order 4), false for C2×C2 (all x^2=1)
-- hasPowerNotOneInv 3 : true for C9 (generator has order 9), false for C3×C3 (all x^3=1)
def hasPowerNotOneInv (k : ℕ) : GroupInvariant Bool where
  eval K _ _ _ := decide (∃ x : K, x ^ k ≠ (1 : K))
  preservation e := by
    apply Bool.decide_congr
    constructor
    · intro ⟨x, hx⟩
      exact ⟨e x, by rw [← map_pow, ← map_one e]; exact e.injective.ne hx⟩
    · intro ⟨y, hy⟩
      exact ⟨e.symm y, by rw [← map_pow, ← map_one e.symm]; exact e.symm.injective.ne hy⟩

-- ∀ x y, x*y = y*x  (decidable for any Fintype with DecidableEq)
-- true for C6, C10; false for D3, D5
def isAbelianInv : GroupInvariant Bool where
  eval K _ _ _ := decide (∀ x y : K, x * y = y * x)
  preservation e := by
    apply Bool.decide_congr
    constructor
    · intro h a b
      have key := congr_arg e (h (e.symm a) (e.symm b))
      simp only [map_mul, MulEquiv.apply_symm_apply] at key
      exact key
    · intro h a b
      have key := congr_arg e.symm (h (e a) (e b))
      simp only [map_mul, MulEquiv.symm_apply_apply] at key
      exact key

structure GroupPredicate where
  check {K : Type v} [Group K] [Fintype K] [DecidableEq K] (x : K) : Bool
  preservation {K L : Type v}
    [Group K] [Group L] [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]
    (iso : K ≃* L) (x : K) : check x = check (iso x)

def numElementsSatisfyingInv (pred : GroupPredicate) : GroupInvariant Nat :=
  let satisfyingSubsetOf (K : Type v) [Group K] [Fintype K] [DecidableEq K] :=
    (Finset.univ : Finset K).filter (pred.check ·)
  {
    eval K _ _ _ := (satisfyingSubsetOf K).card
    preservation {K L : Type v} _ _ _ _ _ _ iso := by
      let X := satisfyingSubsetOf K
      let Y := satisfyingSubsetOf L
      change X.card = Y.card
      exact Finset.card_bij (α := K) (β := L) (s := X) (t := Y)
        (fun _ ↦ iso ·)
        ( -- Map elements of X to elements of Y
          by
            intro a ha
            change iso a ∈ Y
            have ha_pred : pred.check a = true := by grind
            have : pred.check (iso a) = true := by
              rw [← pred.preservation iso a]
              exact ha_pred
            grind
        )
        ( -- Injectivity
          by
            intro a ha b hb
            change iso a = iso b → a = b
            intro heq
            exact iso.injective heq
        )
        ( -- Surjectivity
          by
            intro y hy
            let x : K := iso.symm y
            have hxy : iso x = y := iso.apply_symm_apply y
            have hx : x ∈ X := by
              contrapose! hy
              have hx_pred : pred.check x = false := by grind
              have hy_pred : pred.check y = false := by
                rw [← hxy, ← pred.preservation iso x]
                exact hx_pred
              grind
            use x
        )
  }

def numElementsOfOrderInv (n : Nat) : GroupInvariant Nat :=
  numElementsSatisfyingInv {
    check {K} _ _ _ x := decide (x^n = 1 ∧ (∀ i : Fin (n - 1), x^(i.val + 1) ≠ 1))
    preservation {K L} _ _ _ _ _ _ iso x := by
      apply Bool.decide_congr
      constructor
      · rintro ⟨hpow_n, hpow_le_n⟩
        constructor
        · rw [← map_pow, hpow_n]
          exact MulEquiv.map_one iso
        · intro i
          specialize hpow_le_n i
          rw [← map_pow]
          contrapose! hpow_le_n
          exact (MulEquiv.map_eq_one_iff iso).mp hpow_le_n
      · rintro ⟨hpow_n, hpow_le_n⟩
        constructor
        · exact iso.injective (by rw [map_pow, hpow_n, map_one])
        · intro i h
          apply hpow_le_n i
          rw [← map_pow, h, map_one]
  }

-- Lifts any GroupInvariant to one that evaluates on the center of the group.
-- Decidability is preserved: Subgroup.center K inherits Group, Fintype, and DecidableEq from K.
def onCenterInv {α : Type u} [DecidableEq α] (inv : GroupInvariant α) : GroupInvariant α where
  eval K _ _ _ := inv.eval ↥(Subgroup.center K)
  preservation e := inv.preservation (Subgroup.centerCongr e)

-- |{x² | x ∈ G}| — cheap (one pass) and preserved by isomorphisms since e(x²) = e(x)²
def squaresInv : GroupInvariant Nat where
  eval K _ _ _ := ((Finset.univ : Finset K).image (· ^ 2)).card
  preservation {K L} _ _ _ _ _ _ e :=
    Finset.card_bij (fun x _ => e x)
      (fun x hx => by
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
        obtain ⟨y, rfl⟩ := hx
        exact ⟨e y, by simp [map_pow]⟩)
      (fun _ _ _ _ h => e.injective h)
      (fun y hy => by
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy
        obtain ⟨z, rfl⟩ := hy
        exact ⟨(e.symm z) ^ 2, Finset.mem_image.mpr ⟨e.symm z, Finset.mem_univ _, rfl⟩,
               by simp [map_pow]⟩)

macro "by_single_group" : tactic => `(tactic | (
  simp only [num_entries] at *
  omega
))

set_option linter.style.nativeDecide false in
-- To speed up computation of non-isomorphism
macro "by_invariant" i:ident i':ident inv:term : tactic => `(tactic | (
  simp only [num_entries] at *
  interval_cases $i <;> interval_cases $i' <;>
    first
    | omega
    | simp only [retrieve]
      exact not_iso_by $inv (by native_decide)
))

set_option maxHeartbeats 800000 in
-- This is needed because the proof of uniqueness and obtaining the invariant
-- is mostly computational
theorem uniqueness (n i n' i' : Nat)
  [ValidIndex n i] [ValidIndex n' i'] [Fact (n ≠ n' ∨ i ≠ i')]
  : IsEmpty ((retrieve n i) ≃* (retrieve n' i')) := by
  let G := retrieve n i
  let G' := retrieve n' i'
  rcases eq_or_ne n n' with rfl | hn
  · -- n = n'
    have hv : ValidIndex n i := inferInstance
    have hv' : ValidIndex n i' := inferInstance
    have hneq : n ≠ n ∨ i ≠ i' := Fact.out
    have hi_neq : i ≠ i' := by tauto
    obtain ⟨hn_pos, hn_range, hi_pos, hi_range⟩ := hv
    obtain ⟨_, _, hi'_pos, hi'_range⟩ := hv'
    interval_cases n
    · -- n = 1
      by_single_group
    · -- n = 2
      by_single_group
    · -- n = 3
      by_single_group
    · -- n = 4: C4 vs C2×C2; C4 has element with x^2≠1, C2×C2 does not
      by_invariant i i' (hasPowerNotOneInv 2)
    · -- n = 5
      by_single_group
    · -- n = 6: C6 vs D3; C6 is abelian, D3 is not
      by_invariant i i' isAbelianInv
    · -- n = 7
      by_single_group
    · -- n = 8
      by_invariant i i'
        isAbelianInv ⊗
        (hasPowerNotOneInv 4) ⊗
        (hasPowerNotOneInv 2) ⊗
        (numElementsOfOrderInv 2)
    · -- n = 9: C9 vs C3×C3; C9 has element with x^3≠1, C3×C3 does not
      by_invariant i i' (hasPowerNotOneInv 3)
    · -- n = 10: C10 vs D5; C10 is abelian, D5 is not
      by_invariant i i' isAbelianInv
    · -- n = 11
      by_single_group
    · -- n = 12
      by_invariant i i' isAbelianInv ⊗ (numElementsOfOrderInv 2) ⊗ (numElementsOfOrderInv 4)
    · -- n = 13
      by_single_group
    · -- n = 14
      by_invariant i i' isAbelianInv
    · -- n = 15
      by_single_group
    · -- n = 16
      by_invariant i i'
        isAbelianInv ⊗
        (numElementsOfOrderInv 2) ⊗
        (numElementsOfOrderInv 4) ⊗
        (numElementsOfOrderInv 8) ⊗
        squaresInv
    · -- n = 17
      by_single_group
  · -- n ≠ n'
    have : Nat.card G = n := retrieve_card n i
    have : Nat.card G' = n' := retrieve_card n' i'
    have hcard_neq : Nat.card G ≠ Nat.card G' := by
      simp_all only [ne_eq, not_false_eq_true, true_or, G, G']
    contrapose! hcard_neq with hiso
    exact Nat.card_congr (Classical.ofNonempty : retrieve n i ≃* retrieve n' i')
