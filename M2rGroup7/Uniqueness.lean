import «M2rGroup7».SmallGroupsLibrary

universe u u' v

/-- A group invariant valued in `α`: a function that assigns a value of type `α` to every
    finite group `K`, and is preserved by group isomorphisms.  Two groups with different
    invariant values cannot be isomorphic (see `not_iso_by`).

    Invariants can be combined with `⊗` (notation for `combine`) to produce a product
    invariant that distinguishes groups whenever either component does. -/
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

infixl:65 " ⊗ " => combine -- same precedence as `+`

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

-- Sorted list of (order, count) pairs for every element order that occurs.
-- Built from numElementsOfOrderInv so it is computable (no noncomputable orderOf call).
-- Element orders divide |K| by Lagrange, so Nat.divisors covers all occurring orders.
def orderSpectrumInv : GroupInvariant (List (ℕ × ℕ)) where
  eval K _ [Fintype K] [DecidableEq K] :=
    let n := Fintype.card K
    -- List.range gives [0..n] already sorted; filter to positive divisors of n.
    -- Avoids Finset.sort (which goes through Multiset.toList → Classical.choice)
    -- so the whole definition stays kernel-reducible for `decide`.
    (List.range (n + 1)).filterMap fun d =>
      if 0 < d && n % d == 0 then
        let cnt := (numElementsOfOrderInv d).eval K
        if 0 < cnt then some (d, cnt) else none
      else none
  preservation {K L} _ _ _ _ _ _ e := by
    simp only [Fintype.card_congr e.toEquiv]
    apply List.filterMap_congr
    intro d _
    simp only [(numElementsOfOrderInv d).preservation e]

/-- Close a uniqueness goal for an order with exactly one group in `SmallGroupsLibrary`.
    Reduces `num_entries n = 1` via `simp` then uses `omega` to derive a contradiction
    from the hypothesis `i ≠ i'` and the single-entry bound. -/
macro "by_single_group" : tactic => `(tactic | (
  simp only [num_entries] at *
  omega
))

-- Convert a reduced Lean expression (Nat/Bool/nested Prod literal) to term syntax.
private partial def exprLiteralToSyntax (e : Lean.Expr) : Lean.MetaM (Lean.TSyntax `term) := do
  let e ← Lean.Meta.whnf e
  if let .lit (.natVal n) := e then return Lean.Syntax.mkNumLit (toString n)
  if e == Lean.mkConst ``Bool.true  then return ← `(true)
  if e == Lean.mkConst ``Bool.false then return ← `(false)
  -- Prod.mk.{u v} α β a b  →  four applications
  if let .app (.app (.app (.app f _) _) aExpr) bExpr := e then
    if f.isAppOf ``Prod.mk then
      let aSt ← exprLiteralToSyntax aExpr
      let bSt ← exprLiteralToSyntax bExpr
      return ← `(($aSt, $bSt))
  -- List.nil  →  []
  if e.isAppOf ``List.nil then return ← `([])
  -- List.cons α head tail  →  head :: tail
  if e.isAppOf ``List.cons then
    let args := e.getAppArgs  -- #[α, head, tail]
    let headSt ← exprLiteralToSyntax args[1]!
    let tailSt ← exprLiteralToSyntax args[2]!
    return ← `($headSt :: $tailSt)
  Lean.throwError "exprLiteralToSyntax: cannot convert {e}"

-- Evaluate a closed term `e : α` via native compilation (elab-time only).
-- Handles Nat, Bool, and nested Prod types; never appears in the proof term.
private unsafe def evalToLiteral (αExpr : Lean.Expr) (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let α ← Lean.Meta.whnf αExpr
  if α == Lean.mkConst ``Nat then
    return Lean.mkNatLit (← Lean.Meta.evalExpr Nat (Lean.mkConst ``Nat) e)
  else if α == Lean.mkConst ``Bool then
    let v ← Lean.Meta.evalExpr Bool (Lean.mkConst ``Bool) e
    return if v then Lean.mkConst ``Bool.true else Lean.mkConst ``Bool.false
  else if let .app (.app (.const ``Prod _) αA) αB := α then
    let fstLit ← evalToLiteral αA (← Lean.Meta.mkAppM ``Prod.fst #[e])
    let sndLit ← evalToLiteral αB (← Lean.Meta.mkAppM ``Prod.snd #[e])
    let lvlA ← Lean.Meta.getLevel αA
    let lvlB ← Lean.Meta.getLevel αB
    return Lean.mkApp4 (Lean.mkConst ``Prod.mk [lvlA, lvlB]) αA αB fstLit sndLit
  -- List (ℕ × ℕ): evalExpr the whole list then reconstruct as Expr
  else if let .app (.const ``List _) αElem := α then
    if αElem == Lean.mkApp2 (Lean.mkConst ``Prod [.zero, .zero])
                             (Lean.mkConst ``Nat) (Lean.mkConst ``Nat) then
      let pairs ← Lean.Meta.evalExpr (List (Nat × Nat)) α e
      let pairToExpr (a b : Nat) :=
        Lean.mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero])
          (Lean.mkConst ``Nat) (Lean.mkConst ``Nat) (Lean.mkNatLit a) (Lean.mkNatLit b)
      let listNil := Lean.mkApp (Lean.mkConst ``List.nil [.zero]) αElem
      let cons h t := Lean.mkApp3 (Lean.mkConst ``List.cons [.zero]) αElem h t
      return pairs.foldr (fun (a, b) acc => cons (pairToExpr a b) acc) listNil
    else Lean.throwError "evalToLiteral: unsupported List element type {αElem}"
  else
    Lean.throwError "evalToLiteral: unsupported invariant type {α}"

/-- `by_invariant n i i' inv` proves that two groups of the same order `n`, indexed by
    distinct `i` and `i'`, are non-isomorphic using the `GroupInvariant` `inv`.

    The tactic runs in three phases at elaboration time:
    - **Phase 1 (cache)**: for each group index `k ∈ 1..N`, evaluate `inv.eval (retrieve n k)`
      via native compilation (`evalExpr`), then inject a kernel-verified hypothesis
      `hG_k : inv.eval (retrieve n k) = <literal>` proved by `decide` into the goal context.
    - **Phase 2 (simp set)**: collect all `hG_k` hypotheses into a simp lemma list.
    - **Phase 3 (case split)**: `interval_cases i; interval_cases i'` enumerates all N² pairs;
      diagonal cases are closed by `omega`; off-diagonal cases apply `not_iso_by`, rewrite
      both invariant values to their cached literals via `simp`, then close with `decide`. -/
syntax (name := byInvariant) "by_invariant" num ident ident term : tactic

private unsafe def elabByInvariantImpl : Lean.Elab.Tactic.Tactic
  | `(tactic| by_invariant $nStx $i $i' $inv) => do
    let nGroups := num_entries nStx.getNat
    -- Elaborate inv once to extract the return type α from GroupInvariant α.
    let invExpr ← Lean.Elab.Tactic.elabTerm inv none
    let αExpr := (← Lean.Meta.whnf (← Lean.Meta.inferType invExpr)).getAppArgs[0]!
    -- Phase 1: for each group k, compute inv.eval (retrieve n k) at elaboration time,
    -- then inject `have hG_k : ... = <literal> := by decide`.
    -- `decide` is fully kernel-verified; evalToLiteral only guides which literal to expect.
    let mut cacheIdents : Array Lean.Ident := #[]
    for k in List.range nGroups do
      let k1Stx := Lean.Syntax.mkNumLit (toString (k + 1))
      let hName := Lean.mkIdent (Lean.Name.mkSimple s!"hG_{k + 1}")
      cacheIdents := cacheIdents.push hName
      let invEvalNK ← Lean.Elab.Tactic.elabTerm (← `(($inv).eval (retrieve $nStx $k1Stx))) none
      let valStx    ← exprLiteralToSyntax (← evalToLiteral αExpr invEvalNK)
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        have $hName : ($inv).eval (retrieve $nStx $k1Stx) = $valStx := by
          set_option maxRecDepth 2000 in decide))
    -- Phase 2: build simp lemma list from the cached idents.
    let simpArgs ← cacheIdents.mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:ident)
    -- Phase 3: case-split then close.
    --   · omega closes i = i' subgoals (hi_neq in context)
    --   · otherwise: simp rewrites both sides to cached literals, decide compares them
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      simp only [num_entries] at * <;>
      interval_cases $i <;> interval_cases $i' <;>
      first
      | omega
      | (apply not_iso_by $inv
         simp only [$simpArgs,*]
         decide +kernel)))
  | _ => Lean.Elab.throwUnsupportedSyntax

@[implemented_by elabByInvariantImpl]
private opaque elabByInvariantSafe : Lean.Elab.Tactic.Tactic

@[tactic byInvariant]
private def elabByInvariant : Lean.Elab.Tactic.Tactic := elabByInvariantSafe

set_option maxHeartbeats 4000000 in
-- Bumping heartbeats to allow the elaborator to construct the O(N²) case-split AST.
-- The underlying kernel proofs use pure `decide` and execute.
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
      by_invariant 4 i i' (hasPowerNotOneInv 2)
    · -- n = 5
      by_single_group
    · -- n = 6: C6 vs D3; C6 is abelian, D3 is not
      by_invariant 6 i i' isAbelianInv
    · -- n = 7
      by_single_group
    · -- n = 8
      by_invariant 8 i i'
        (isAbelianInv ⊗ (hasPowerNotOneInv 4) ⊗ (hasPowerNotOneInv 2) ⊗ (numElementsOfOrderInv 2))
    · -- n = 9: C9 vs C3×C3; C9 has element with x^3≠1, C3×C3 does not
      by_invariant 9 i i' (hasPowerNotOneInv 3)
    · -- n = 10: C10 vs D5; C10 is abelian, D5 is not
      by_invariant 10 i i' isAbelianInv
    · -- n = 11
      by_single_group
    · -- n = 12
      by_invariant 12 i i'
        (isAbelianInv ⊗ (numElementsOfOrderInv 2) ⊗ (numElementsOfOrderInv 4))
    · -- n = 13
      by_single_group
    · -- n = 14
      by_invariant 14 i i' isAbelianInv
    · -- n = 15
      by_single_group
    · -- n = 16
      by_invariant 16 i i'
        (isAbelianInv ⊗
        orderSpectrumInv ⊗
        squaresInv)
    · -- n = 17
      by_single_group
    · -- n = 18
      by_invariant 18 i i'
        isAbelianInv ⊗
        orderSpectrumInv
    · -- n = 19
      by_single_group
    · -- n = 20
      by_invariant 20 i i'
        isAbelianInv ⊗
        orderSpectrumInv
    · -- n = 21: C21 vs C7⋊C3; abelian vs non-abelian
      by_invariant 21 i i' isAbelianInv
    · -- n = 22: D11 vs C22; non-abelian vs abelian
      by_invariant 22 i i' isAbelianInv
    · -- n = 23
      by_single_group
    · -- n = 24
      by_invariant 24 i i' orderSpectrumInv
    · -- n = 25: C25 vs C5×C5; C25 has element with x^5≠1, C5×C5 does not
      by_invariant 25 i i' (hasPowerNotOneInv 5)
    · -- n = 26: D13 vs C26; non-abelian vs abelian
      by_invariant 26 i i' isAbelianInv
    · -- n = 27
      by_invariant 27 i i' (isAbelianInv ⊗ orderSpectrumInv)
    · -- n = 28
      by_invariant 28 i i'
        isAbelianInv ⊗
        orderSpectrumInv
    · -- n = 29
      by_single_group
    · -- n = 30
      by_invariant 30 i i' (isAbelianInv ⊗ (numElementsOfOrderInv 2))
    · -- n = 31
      by_single_group
  · -- n ≠ n'
    have : Nat.card G = n := retrieve_card n i
    have : Nat.card G' = n' := retrieve_card n' i'
    have hcard_neq : Nat.card G ≠ Nat.card G' := by
      simp_all only [ne_eq, not_false_eq_true, true_or, G, G']
    contrapose! hcard_neq with hiso
    exact Nat.card_congr (Classical.ofNonempty : retrieve n i ≃* retrieve n' i')
