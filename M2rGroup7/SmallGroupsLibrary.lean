import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.OrderOfElement
import «M2rGroup7».CyclicGroup
import «M2rGroup7».P2qClassification.PqClassification
import «M2rGroup7».P2qClassification.FourQClassification
import Mathlib.Tactic
import Mathlib.RingTheory.ZMod.UnitsCyclic

-- The generic Group (retrieve n i) instance uses split + infer_instance across ~70 arms;
-- importing FourQClassification enlarges the instance environment enough to push past 200k.
set_option maxHeartbeats 400000

abbrev maximumOrder : Nat := 31

/-- Alternating group generator -/
def AlternatingGroup (n : Nat) [NeZero n] := ↥(alternatingGroup (Fin n))
  deriving DecidableEq, Group, Fintype

instance {p : ℕ} [h : Fact p.Prime] {n : ℕ} : NeZero (p ^ n) := by
  have hp : Nat.Prime p := h.out
  exact ⟨(pow_pos hp.pos n).ne'⟩

instance {p : ℕ} [h : Fact p.Prime] : NeZero (p * (p - 1)) := by
  have hp : Nat.Prime p := h.out
  have h2 : 2 ≤ p := hp.two_le
  exact ⟨Nat.mul_ne_zero (by omega) (by omega)⟩

/-- The non-trivial swap action of `C_4` on `C_2 × C_2`, factoring through `C_4/C_2 = C_2`. -/
def c4OnC2sqSwap : CyclicGroup 4 →* MulAut (CyclicGroup 2 × CyclicGroup 2) :=
  let swap : MulAut (CyclicGroup 2 × CyclicGroup 2) := MulEquiv.prodComm
  cyclicHom 4 swap (by
    have h2 : swap ^ 2 = 1 := by ext ⟨a, b⟩ <;> rfl
    change swap ^ 4 = 1
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, one_pow])

/-- The non-trivial action of `C_4` on `C_4` by inversion, factoring through `C_4/C_2 = C_2`. -/
def c4OnC4Inv : CyclicGroup 4 →* MulAut (CyclicGroup 4) :=
  let inv : MulAut (CyclicGroup 4) := MulEquiv.inv (CyclicGroup 4)
  cyclicHom 4 inv (by
    have h2 : inv ^ 2 = 1 := by
      ext x
      change (x⁻¹)⁻¹ = x
      exact inv_inv x
    change inv ^ (2 * 2) = 1
    rw [pow_mul, h2, one_pow])

/-- The non-trivial action of `C_2` on `C_8` by `x ↦ x^5`. -/
def c2OnC8Pow5 : CyclicGroup 2 →* MulAut (CyclicGroup 8) :=
  have h25 : ∀ x : CyclicGroup 8, (x ^ 5) ^ 5 = x := by decide
  let pow5 : MulAut (CyclicGroup 8) :=
    { toFun := (· ^ 5)
      invFun := (· ^ 5)
      left_inv := h25
      right_inv := h25
      map_mul' := fun a b => mul_pow a b 5 }
  cyclicHom 2 pow5 (by
    ext x
    change (x ^ 5) ^ 5 = x
    exact h25 x)

/-- The non-trivial action of `C_2` on `C_8` by `x ↦ x^3`. -/
def c2OnC8Pow3 : CyclicGroup 2 →* MulAut (CyclicGroup 8) :=
  have h9 : ∀ x : CyclicGroup 8, (x ^ 3) ^ 3 = x := by decide
  let pow3 : MulAut (CyclicGroup 8) :=
    { toFun := (· ^ 3)
      invFun := (· ^ 3)
      left_inv := h9
      right_inv := h9
      map_mul' := fun a b => mul_pow a b 3 }
  cyclicHom 2 pow3 (by
    ext x
    change (x ^ 3) ^ 3 = x
    exact h9 x)

/-- The unique element of order 2 in `CyclicGroup 4`. -/
def c4Half : CyclicGroup 4 := Multiplicative.ofAdd (2 : ZMod 4)

/-- The order-2 automorphism of `K_8 = C_4 × C_2` sending `x ↦ x^3` and `y ↦ x²y`, where
`x` generates `C_4` and `y` generates `C_2`. On pairs: `(a, b) ↦ (a^3 · c4Half^b, b)`. -/
def psi6 : MulAut (CyclicGroup 4 × CyclicGroup 2) where
  toFun ab := (ab.1 ^ 3 * c4Half ^ (Multiplicative.toAdd ab.2).val, ab.2)
  invFun ab := (ab.1 ^ 3 * c4Half ^ (Multiplicative.toAdd ab.2).val, ab.2)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

/-- The action of `C_2` on `K_8 = C_4 × C_2` via the `psi6` automorphism. -/
def c2OnK8Psi6 : CyclicGroup 2 →* MulAut (CyclicGroup 4 × CyclicGroup 2) :=
  cyclicHom 2 psi6 (by
    rw [pow_two]
    apply MulEquiv.ext
    intro x
    exact psi6.left_inv x)

-- SemidirectProduct N ⋊[φ] G is structurally N × G, so Fintype and DecidableEq lift directly.
instance {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N} [Fintype N] [Fintype G] :
    Fintype (N ⋊[φ] G) :=
  Fintype.ofEquiv (N × G) {
    toFun   := fun p => ⟨p.1, p.2⟩
    invFun  := fun x => ⟨x.left, x.right⟩
    left_inv  := fun _ => rfl
    right_inv := fun _ => rfl
  }

instance {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N} [DecidableEq N] [DecidableEq G] :
    DecidableEq (N ⋊[φ] G) :=
  fun a b => decidable_of_iff (a.left = b.left ∧ a.right = b.right)
    ⟨fun ⟨hl, hr⟩ => SemidirectProduct.ext hl hr, fun h => ⟨congr_arg _ h, congr_arg _ h⟩⟩

instance : Group Unit where
  mul _ _ := ()
  mul_assoc _ _ _ := by rfl
  one := ()
  one_mul _ := by rfl
  mul_one _ := by rfl
  inv _ := ()
  inv_mul_cancel _ := by rfl

-- Fact instances for the primes used in retrieve's pq semidirect product entries.
instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

-- ─── Computable surrogate actions for `retrieve` ──────────────────────────────
-- The canonical actions used by the classification theorems
-- (`canonicalCpOnCqAction`, `canonicalC4OnCqAction`, `canonicalC2C2OnCqAction`,
-- `canonicalC3OnC2C2Action`) are noncomputable (they rely on `Classical.choice`
-- via `IsCyclic.exists_generator` / `canonicalAutElement`). To keep `retrieve`
-- computable — so `native_decide` works for the invariant checks in
-- `Uniqueness.lean` — we use the surrogate actions below. Bridging between the
-- canonical actions and these surrogates is done once per family in
-- `Classification.lean`.

/-- The order-2 action `C_2 →* Aut(C_q)` sending the generator to inversion. -/
def c2OnCqInv (q : Nat) [NeZero q] : CyclicGroup 2 →* MulAut (CyclicGroup q) :=
  let inv : MulAut (CyclicGroup q) := MulEquiv.inv (CyclicGroup q)
  cyclicHom 2 inv (by
    ext x
    change (x⁻¹)⁻¹ = x
    exact inv_inv x)

/-- The order-2 action `C_4 →* Aut(C_q)` factoring through `C_4 / C_2`, sending
the generator to inversion. -/
def c4OnCqInv (q : Nat) [NeZero q] : CyclicGroup 4 →* MulAut (CyclicGroup q) :=
  let inv : MulAut (CyclicGroup q) := MulEquiv.inv (CyclicGroup q)
  cyclicHom 4 inv (by
    have h2 : inv ^ 2 = 1 := by
      ext x
      change (x⁻¹)⁻¹ = x
      exact inv_inv x
    change inv ^ (2 * 2) = 1
    rw [pow_mul, h2, one_pow])

/-- The order-2 action `C_8 →* Aut(C_q)` factoring through `C_8 / C_4`, sending
the generator to inversion. -/
def c8OnCqInv (q : Nat) [NeZero q] : CyclicGroup 8 →* MulAut (CyclicGroup q) :=
  let inv : MulAut (CyclicGroup q) := MulEquiv.inv (CyclicGroup q)
  cyclicHom 8 inv (by
    have h2 : inv ^ 2 = 1 := by
      ext x
      change (x⁻¹)⁻¹ = x
      exact inv_inv x
    change inv ^ (2 * 4) = 1
    rw [pow_mul, h2, one_pow])

/-- The order-2 action `C_2 × C_2 →* Aut(C_q)` projecting to the first factor
and then inverting. -/
def c2c2OnCqInv (q : Nat) [NeZero q] : (CyclicGroup 2 × CyclicGroup 2) →* MulAut (CyclicGroup q) :=
  (c2OnCqInv q).comp (MonoidHom.fst (CyclicGroup 2) (CyclicGroup 2))

/-- The order-3 action `C_3 →* Aut(C_7)` sending the generator to `x ↦ x^2`
(an element of order 3 in `(ZMod 7)^×`). -/
def c3OnC7Mul2 : CyclicGroup 3 →* MulAut (CyclicGroup 7) :=
  have h27 : ∀ x : CyclicGroup 7, ((x ^ 2) ^ 2) ^ 2 = x := by decide
  let mul2 : MulAut (CyclicGroup 7) :=
    { toFun := (· ^ 2)
      invFun := (· ^ 4)
      left_inv := by decide
      right_inv := by decide
      map_mul' := fun a b => mul_pow a b 2 }
  cyclicHom 3 mul2 (by
    ext x
    change ((x ^ 2) ^ 2) ^ 2 = x
    exact h27 x)

/-- The pow-by-2 automorphism of `CyclicGroup 5` (an element of order 4 in
`Aut(C_5)`). Used as a building block for `c4OnC5Pow2`. -/
def pow2AutC5 : MulAut (CyclicGroup 5) :=
  { toFun := (· ^ 2)
    invFun := (· ^ 3)
    left_inv := by decide
    right_inv := by decide
    map_mul' := fun a b => mul_pow a b 2 }

/-- The order-4 action `C_4 →* Aut(C_5)` sending the generator to `x ↦ x^2`
(an element of order 4 in `(ZMod 5)^×`). -/
def c4OnC5Pow2 : CyclicGroup 4 →* MulAut (CyclicGroup 5) :=
  cyclicHom 4 pow2AutC5 (by
    ext x
    change (((x ^ 2) ^ 2) ^ 2) ^ 2 = x
    revert x; decide)

/-- Order-3 automorphism of `C_2 × C_2` used to build the unique non-abelian
order-12 group `A_4`. Sends `(x, y) ↦ (x*y, x)`. (Computable replica of
`c2c2OrderThreeAut` from `FourQClassification.lean`.) -/
def c2c2OrderThreeAutComp : MulAut (CyclicGroup 2 × CyclicGroup 2) where
  toFun p := (p.1 * p.2, p.1)
  invFun p := (p.2, p.1 * p.2)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

/-- The order-3 action `C_3 →* Aut(C_2 × C_2)` defining the `A_4` semidirect
product structure. -/
def c3OnC2C2 : CyclicGroup 3 →* MulAut (CyclicGroup 2 × CyclicGroup 2) :=
  cyclicHom 3 c2c2OrderThreeAutComp (by decide)

/-- Small groups database. Computable: each entry is built from `CyclicGroup`,
direct products, `DihedralGroup`, `QuaternionGroup`, or a semidirect product
with one of the explicit computable actions defined above (or in this file). -/
@[reducible] def retrieve (n : Nat) (i : Nat) : Type :=
  match n, i with
  | 1, 1 => Unit
  | 2, 1 => CyclicGroup 2
  | 3, 1 => CyclicGroup 3
  | 4, 1 => CyclicGroup 4
  | 4, 2 => CyclicGroup 2 × CyclicGroup 2
  | 5, 1 => CyclicGroup 5
  | 6, 1 => DihedralGroup 3
  | 6, 2 => CyclicGroup 6
  | 7, 1 => CyclicGroup 7
  | 8, 1 => CyclicGroup 8
  | 8, 2 => CyclicGroup 4 × CyclicGroup 2
  | 8, 3 => DihedralGroup 4
  | 8, 4 => QuaternionGroup 2
  | 8, 5 => CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2
  | 9, 1 => CyclicGroup 9
  | 9, 2 => CyclicGroup 3 × CyclicGroup 3
  | 10, 1 => DihedralGroup 5
  | 10, 2 => CyclicGroup 10
  | 11, 1 => CyclicGroup 11
  | 12, 1 => CyclicGroup 12
  | 12, 2 => CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 3
  | 12, 3 => CyclicGroup 3 ⋊[c4OnCqInv 3] CyclicGroup 4
  | 12, 4 => CyclicGroup 3 ⋊[c2c2OnCqInv 3] (CyclicGroup 2 × CyclicGroup 2)
  | 12, 5 => (CyclicGroup 2 × CyclicGroup 2) ⋊[c3OnC2C2] CyclicGroup 3
  | 13, 1 => CyclicGroup 13
  | 14, 1 => DihedralGroup 7
  | 14, 2 => CyclicGroup 14
  | 15, 1 => CyclicGroup 15
  | 16, 1 => CyclicGroup 16
  | 16, 2 => CyclicGroup 4 × CyclicGroup 4
  | 16, 3 => (CyclicGroup 2 × CyclicGroup 2) ⋊[c4OnC2sqSwap] CyclicGroup 4
  | 16, 4 => CyclicGroup 4 ⋊[c4OnC4Inv] CyclicGroup 4
  | 16, 5 => CyclicGroup 8 × CyclicGroup 2
  | 16, 6 => CyclicGroup 8 ⋊[c2OnC8Pow5] CyclicGroup 2
  | 16, 7 => DihedralGroup 8
  | 16, 8 => CyclicGroup 8 ⋊[c2OnC8Pow3] CyclicGroup 2
  | 16, 9 => QuaternionGroup 4
  | 16, 10 => CyclicGroup 4 × CyclicGroup 2 × CyclicGroup 2
  | 16, 11 => CyclicGroup 2 × DihedralGroup 4
  | 16, 12 => CyclicGroup 2 × QuaternionGroup 2
  | 16, 13 => (CyclicGroup 4 × CyclicGroup 2) ⋊[c2OnK8Psi6] CyclicGroup 2
  | 16, 14 => CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2
  | 17, 1 => CyclicGroup 17
  | 18, 1 => CyclicGroup 18
  | 19, 1 => CyclicGroup 19
  | 20, 1 => CyclicGroup 20
  | 20, 2 => CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 5
  | 20, 3 => CyclicGroup 5 ⋊[c4OnCqInv 5] CyclicGroup 4
  | 20, 4 => CyclicGroup 5 ⋊[c4OnC5Pow2] CyclicGroup 4
  | 20, 5 => CyclicGroup 5 ⋊[c2c2OnCqInv 5] (CyclicGroup 2 × CyclicGroup 2)
  | 21, 1 => CyclicGroup 7 ⋊[c3OnC7Mul2] CyclicGroup 3
  | 21, 2 => CyclicGroup 21
  | 22, 1 => DihedralGroup 11
  | 22, 2 => CyclicGroup 22
  | 23, 1 => CyclicGroup 23
  | 24, 1 => CyclicGroup 24
  | 25, 1 => CyclicGroup 25
  | 25, 2 => CyclicGroup 5 × CyclicGroup 5
  | 26, 1 => DihedralGroup 13
  | 26, 2 => CyclicGroup 26
  | 27, 1 => CyclicGroup 27
  | 28, 1 => CyclicGroup 28
  | 28, 2 => CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 7
  | 28, 3 => CyclicGroup 7 ⋊[c4OnCqInv 7] CyclicGroup 4
  | 28, 4 => CyclicGroup 7 ⋊[c2c2OnCqInv 7] (CyclicGroup 2 × CyclicGroup 2)
  | 29, 1 => CyclicGroup 29
  | 30, 1 => CyclicGroup 30
  | 31, 1 => CyclicGroup 31
  | _, _ => PUnit -- Fallback to make retrieve total

@[reducible]
def num_entries (n : Nat) : Nat :=
  match n with
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 1
  | 6 => 2
  | 7 => 1
  | 8 => 5
  | 9 => 2
  | 10 => 2
  | 11 => 1
  | 12 => 5
  | 13 => 1
  | 14 => 2
  | 15 => 1
  | 16 => 14
  | 17 => 1
  | 18 => 1 -- It is 5 actually, will fill rest later
  | 19 => 1
  | 20 => 5
  | 21 => 2
  | 22 => 2
  | 23 => 1
  | 24 => 1 -- It is 15 actually, will fill rest later
  | 25 => 2
  | 26 => 2
  | 27 => 1 -- It is 5 actually, will fill rest later
  | 28 => 4
  | 29 => 1
  | 30 => 1 -- It is 4 actually, will fill rest later
  | 31 => 1
  | _ => 0

def validIndex (n i : Nat) : Bool :=
  decide (n > 0 ∧ n ≤ maximumOrder ∧ i > 0 ∧ i ≤ num_entries n)

class ValidIndex (n : Nat) (i : Nat) : Prop where
  n_pos : n > 0
  n_range : n ≤ maximumOrder
  i_pos : i > 0
  i_range : i ≤ num_entries n

instance (n i : Nat) : Decidable (ValidIndex n i) :=
  decidable_of_iff (validIndex n i = true) (by
    simp only [validIndex, decide_eq_true_eq]
    exact ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩,
           fun h => ⟨h.n_pos, h.n_range, h.i_pos, h.i_range⟩⟩)

instance (n : Nat) (i : Nat) [hv : ValidIndex n i] : Group (retrieve n i) := by
  unfold retrieve; split <;> try infer_instance

theorem retrieve_card (n : Nat) (i : Nat) [hv : ValidIndex n i] : Nat.card (retrieve n i) = n := by
  obtain ⟨hn_pos, hn_range, hi_pos, hi_range⟩ := hv
  rw [maximumOrder] at hn_range
  interval_cases n <;>
    simp only [num_entries] at hi_range <;>
    interval_cases i <;>
      simp only [retrieve] <;>
      simp_all only [Fintype.card_prod, Fintype.card_unique, Nat.card_eq_fintype_card,
        Nat.ofNat_pos, Nat.one_le_ofNat, Nat.reduceLeDiff, Order.lt_one_iff, Order.lt_two_iff,
        Std.le_refl, gt_iff_lt, zero_le] <;>
      rfl

-- ─── Bridge lemmas connecting canonical (noncomputable) actions to the computable
-- surrogate actions used by `retrieve`. Each bridge is itself noncomputable (it goes
-- through `Classical.choice` via the underlying classification utilities), but the
-- `retrieve` *type* and its `Group` instance remain computable — which is what
-- `native_decide` in `Uniqueness.lean` requires.

open SemidirectProduct in
/-- For odd prime `q`, the canonical noncomputable SDP `C_q ⋊ C_2` is isomorphic to
`DihedralGroup q`. Both have order `2q` and are non-cyclic for `q ≠ 1`. -/
lemma canonicalSDP_iso_DihedralGroup
    (q : ℕ) [hq : Fact q.Prime] (hq2 : q ≠ 2)
    (hr : 1 ≤ min 1 ((q - 1).factorization 2)) :
    Nonempty (SemidirectProduct (CyclicGroup q) (CyclicGroup 2)
        (canonicalCpOnCqAction (show (2:ℕ) ≠ q by have := hq.out.two_le; omega) hq2 hr)
      ≃* DihedralGroup q) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hp_ne_q : (2:ℕ) ≠ q := by have := hq.out.two_le; omega
  have h_card_sdp : Nat.card
      (SemidirectProduct (CyclicGroup q) (CyclicGroup 2)
        (canonicalCpOnCqAction hp_ne_q hq2 hr)) = 2 * q :=
    canonicalSDP_card hp_ne_q hq2 hr
  have h_not_cyc_sdp : ¬ IsCyclic
      (SemidirectProduct (CyclicGroup q) (CyclicGroup 2)
        (canonicalCpOnCqAction hp_ne_q hq2 hr)) :=
    canonicalSDP_not_isCyclic hp_ne_q hq2 hr
  have h_card_dih : Nat.card (DihedralGroup q) = 2 * q := DihedralGroup.nat_card
  have h_not_cyc_dih : ¬ IsCyclic (DihedralGroup q) :=
    DihedralGroup.not_isCyclic (by have := hq.out.two_le; omega)
  exact nonempty_mulEquiv_of_card_eq_prime_mul_prime_of_not_isCyclic'
    (by have := hq.out.two_le; omega : (2:ℕ) < q)
    h_card_sdp h_not_cyc_sdp h_card_dih h_not_cyc_dih

/-- The canonical noncomputable SDP `C_7 ⋊ C_3` is isomorphic to the computable surrogate
`CyclicGroup 7 ⋊[c3OnC7Mul2] CyclicGroup 3`. Both have order 21 and are non-cyclic. -/
lemma canonicalSDP_iso_retrieve_21
    (hr : 1 ≤ min 1 ((7 - 1 : ℕ).factorization 3)) :
    Nonempty (SemidirectProduct (CyclicGroup 7) (CyclicGroup 3)
        (canonicalCpOnCqAction (show (3:ℕ) ≠ 7 by norm_num) (by norm_num) hr)
      ≃* (CyclicGroup 7 ⋊[c3OnC7Mul2] CyclicGroup 3)) := by
  have h_card_lhs : Nat.card
      (SemidirectProduct (CyclicGroup 7) (CyclicGroup 3)
        (canonicalCpOnCqAction (show (3:ℕ) ≠ 7 by norm_num) (by norm_num) hr)) = 3 * 7 :=
    canonicalSDP_card _ _ _
  have h_not_cyc_lhs : ¬ IsCyclic
      (SemidirectProduct (CyclicGroup 7) (CyclicGroup 3)
        (canonicalCpOnCqAction (show (3:ℕ) ≠ 7 by norm_num) (by norm_num) hr)) :=
    canonicalSDP_not_isCyclic _ _ _
  -- For the RHS: card = 21 (= 3*7) by SemidirectProduct.card; non-cyclic via nontriviality of c3OnC7Mul2.
  have h_card_rhs : Nat.card (CyclicGroup 7 ⋊[c3OnC7Mul2] CyclicGroup 3) = 3 * 7 := by
    rw [SemidirectProduct.card, card_cyclicGroup, card_cyclicGroup]
  have hc3_ne : c3OnC7Mul2 ≠ 1 := by
    intro h
    -- evaluate at the generator of CyclicGroup 3
    have := DFunLike.congr_fun h (Multiplicative.ofAdd (1 : ZMod 3))
    -- now `this : c3OnC7Mul2 (gen) = 1`; the LHS sends gen of C_7 to its square.
    have happ := MulEquiv.ext_iff.mp this (Multiplicative.ofAdd (1 : ZMod 7))
    -- happ : c3OnC7Mul2 gen (Multiplicative.ofAdd 1 : ZMod 7) = Multiplicative.ofAdd 1
    -- but the LHS computes to Multiplicative.ofAdd 2, a contradiction.
    revert happ
    decide
  have h_not_cyc_rhs : ¬ IsCyclic (CyclicGroup 7 ⋊[c3OnC7Mul2] CyclicGroup 3) :=
    sdp_not_isCyclic_of_action_ne_one hc3_ne
  exact nonempty_mulEquiv_of_card_eq_prime_mul_prime_of_not_isCyclic'
    (by norm_num : (3:ℕ) < 7)
    h_card_lhs h_not_cyc_lhs h_card_rhs h_not_cyc_rhs

-- ─── Bridges for 4q (12, 20, 28) classifications ──────────────────────────

-- Concrete range cards for the surrogate actions. Each cyclicHom-defined action
-- has range equal to `Subgroup.zpowers a` (where `a` is the chosen target).

/-- For any `cyclicHom n a h`, applied at `x : CyclicGroup n`, we get `a ^ (toAdd x).val`. -/
lemma cyclicHom_apply_eq_zpow
    (n : Nat) [NeZero n] {G : Type*} [Group G] (a : G) (h : a ^ n = 1) (x : CyclicGroup n) :
    cyclicHom n a h x = a ^ ((Multiplicative.toAdd x).val : ℤ) := by
  show Additive.toMul ((ZMod.lift n
      ⟨zmultiplesHom (Additive G) (Additive.ofMul a),
        by change (n : ℤ) • Additive.ofMul a = 0
           rw [← ofMul_zpow, zpow_natCast, h, ofMul_one]⟩) (Multiplicative.toAdd x))
      = a ^ ((Multiplicative.toAdd x).val : ℤ)
  -- Let `m` be the natural-number value of `toAdd x`. The RHS is `a^m`.
  -- For the LHS, rewrite `toAdd x : ZMod n` as the cast of `m : ℤ` into `ZMod n`
  -- and apply `ZMod.lift_coe`.
  set m : ℕ := (Multiplicative.toAdd x).val with hm
  conv_lhs => rw [show (Multiplicative.toAdd x : ZMod n) = (((m : ℤ) : ZMod n)) from by
    push_cast; exact (ZMod.natCast_zmod_val _).symm]
  rw [ZMod.lift_coe]
  rw [zmultiplesHom_apply, ← ofMul_zpow]
  rfl

/-- Inversion on `CyclicGroup q` squared equals identity. -/
lemma inv_aut_pow_two_eq_one (q : ℕ) [NeZero q] :
    (MulEquiv.inv (CyclicGroup q)) ^ 2 = 1 := by
  ext x; change (x⁻¹)⁻¹ = x; exact inv_inv x

/-- Inversion on `CyclicGroup q` to the 4th power equals identity. -/
lemma inv_aut_pow_four_eq_one (q : ℕ) [NeZero q] :
    (MulEquiv.inv (CyclicGroup q)) ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, inv_aut_pow_two_eq_one, one_pow]

/-- For the surrogate `c4OnCqInv q`, applied at `x`, the value is `inv^(toAdd x).val`. -/
lemma c4OnCqInv_apply (q : ℕ) [NeZero q] (x : CyclicGroup 4) :
    c4OnCqInv q x = (MulEquiv.inv (CyclicGroup q)) ^ ((Multiplicative.toAdd x).val : ℤ) :=
  cyclicHom_apply_eq_zpow 4 (MulEquiv.inv (CyclicGroup q)) (inv_aut_pow_four_eq_one q) x

/-- For the surrogate `c2OnCqInv q`, applied at `x`, the value is `inv^(toAdd x).val`. -/
lemma c2OnCqInv_apply (q : ℕ) [NeZero q] (x : CyclicGroup 2) :
    c2OnCqInv q x = (MulEquiv.inv (CyclicGroup q)) ^ ((Multiplicative.toAdd x).val : ℤ) :=
  cyclicHom_apply_eq_zpow 2 (MulEquiv.inv (CyclicGroup q)) (inv_aut_pow_two_eq_one q) x

lemma inv_aut_ne_one_three : (MulEquiv.inv (CyclicGroup 3)) ≠ 1 := by decide
lemma inv_aut_ne_one_five  : (MulEquiv.inv (CyclicGroup 5)) ≠ 1 := by decide
lemma inv_aut_ne_one_seven : (MulEquiv.inv (CyclicGroup 7)) ≠ 1 := by decide

lemma orderOf_inv_aut_three : orderOf (MulEquiv.inv (CyclicGroup 3)) = 2 :=
  orderOf_eq_prime (inv_aut_pow_two_eq_one 3) inv_aut_ne_one_three
lemma orderOf_inv_aut_five : orderOf (MulEquiv.inv (CyclicGroup 5)) = 2 :=
  orderOf_eq_prime (inv_aut_pow_two_eq_one 5) inv_aut_ne_one_five
lemma orderOf_inv_aut_seven : orderOf (MulEquiv.inv (CyclicGroup 7)) = 2 :=
  orderOf_eq_prime (inv_aut_pow_two_eq_one 7) inv_aut_ne_one_seven

/-- `(c4OnCqInv q).range ≤ Subgroup.zpowers (MulEquiv.inv (CyclicGroup q))`. -/
lemma c4OnCqInv_range_le_zpowers_inv (q : ℕ) [NeZero q] :
    (c4OnCqInv q).range ≤ Subgroup.zpowers (MulEquiv.inv (CyclicGroup q)) := by
  rintro y ⟨x, rfl⟩
  exact ⟨((Multiplicative.toAdd x).val : ℤ), (c4OnCqInv_apply q x).symm⟩

lemma c4OnCqInv_inv_mem_range (q : ℕ) [NeZero q] :
    MulEquiv.inv (CyclicGroup q) ∈ (c4OnCqInv q).range := by
  haveI : Fact (1 < 4) := ⟨by norm_num⟩
  refine ⟨Multiplicative.ofAdd (1 : ZMod 4), ?_⟩
  rw [c4OnCqInv_apply]
  show (MulEquiv.inv (CyclicGroup q)) ^ ((1 : ZMod 4).val : ℤ) = MulEquiv.inv (CyclicGroup q)
  rw [ZMod.val_one]; exact zpow_one _

lemma c4OnCqInv_range_card_3 : Nat.card (c4OnCqInv 3).range = 2 := by
  have hle := c4OnCqInv_range_le_zpowers_inv 3
  have hmem := c4OnCqInv_inv_mem_range 3
  have hge := Subgroup.zpowers_le.mpr hmem
  rw [le_antisymm hle hge, Nat.card_zpowers, orderOf_inv_aut_three]

lemma c4OnCqInv_range_card_5 : Nat.card (c4OnCqInv 5).range = 2 := by
  have hle := c4OnCqInv_range_le_zpowers_inv 5
  have hmem := c4OnCqInv_inv_mem_range 5
  have hge := Subgroup.zpowers_le.mpr hmem
  rw [le_antisymm hle hge, Nat.card_zpowers, orderOf_inv_aut_five]

lemma c4OnCqInv_range_card_7 : Nat.card (c4OnCqInv 7).range = 2 := by
  have hle := c4OnCqInv_range_le_zpowers_inv 7
  have hmem := c4OnCqInv_inv_mem_range 7
  have hge := Subgroup.zpowers_le.mpr hmem
  rw [le_antisymm hle hge, Nat.card_zpowers, orderOf_inv_aut_seven]

-- c2OnCqInv: image of generator is inversion.
lemma c2OnCqInv_range_le_zpowers_inv (q : ℕ) [NeZero q] :
    (c2OnCqInv q).range ≤ Subgroup.zpowers (MulEquiv.inv (CyclicGroup q)) := by
  rintro y ⟨x, rfl⟩
  exact ⟨((Multiplicative.toAdd x).val : ℤ), (c2OnCqInv_apply q x).symm⟩

lemma c2OnCqInv_inv_mem_range (q : ℕ) [NeZero q] :
    MulEquiv.inv (CyclicGroup q) ∈ (c2OnCqInv q).range := by
  haveI : Fact (1 < 2) := ⟨by norm_num⟩
  refine ⟨Multiplicative.ofAdd (1 : ZMod 2), ?_⟩
  rw [c2OnCqInv_apply]
  show (MulEquiv.inv (CyclicGroup q)) ^ ((1 : ZMod 2).val : ℤ) = MulEquiv.inv (CyclicGroup q)
  rw [ZMod.val_one]; exact zpow_one _

lemma c2c2OnCqInv_range_eq_c2OnCqInv_range (q : ℕ) [NeZero q] :
    (c2c2OnCqInv q).range = (c2OnCqInv q).range := by
  ext y
  simp only [c2c2OnCqInv, MonoidHom.mem_range, MonoidHom.comp_apply, MonoidHom.coe_fst]
  exact ⟨fun ⟨⟨a, _⟩, h⟩ => ⟨a, h⟩, fun ⟨a, ha⟩ => ⟨(a, 1), ha⟩⟩

lemma c2c2OnCqInv_range_card_3 : Nat.card (c2c2OnCqInv 3).range = 2 := by
  rw [c2c2OnCqInv_range_eq_c2OnCqInv_range]
  have hle := c2OnCqInv_range_le_zpowers_inv 3
  have hmem := c2OnCqInv_inv_mem_range 3
  have hge := Subgroup.zpowers_le.mpr hmem
  rw [le_antisymm hle hge, Nat.card_zpowers, orderOf_inv_aut_three]

lemma c2c2OnCqInv_range_card_5 : Nat.card (c2c2OnCqInv 5).range = 2 := by
  rw [c2c2OnCqInv_range_eq_c2OnCqInv_range]
  have hle := c2OnCqInv_range_le_zpowers_inv 5
  have hmem := c2OnCqInv_inv_mem_range 5
  have hge := Subgroup.zpowers_le.mpr hmem
  rw [le_antisymm hle hge, Nat.card_zpowers, orderOf_inv_aut_five]

lemma c2c2OnCqInv_range_card_7 : Nat.card (c2c2OnCqInv 7).range = 2 := by
  rw [c2c2OnCqInv_range_eq_c2OnCqInv_range]
  have hle := c2OnCqInv_range_le_zpowers_inv 7
  have hmem := c2OnCqInv_inv_mem_range 7
  have hge := Subgroup.zpowers_le.mpr hmem
  rw [le_antisymm hle hge, Nat.card_zpowers, orderOf_inv_aut_seven]

-- c3OnC2C2 range cardinality
lemma c2c2OrderThreeAutComp_pow_three_eq_one :
    c2c2OrderThreeAutComp ^ 3 = 1 := by decide

lemma c2c2OrderThreeAutComp_ne_one : c2c2OrderThreeAutComp ≠ 1 := by decide

lemma orderOf_c2c2OrderThreeAutComp : orderOf c2c2OrderThreeAutComp = 3 :=
  orderOf_eq_prime c2c2OrderThreeAutComp_pow_three_eq_one c2c2OrderThreeAutComp_ne_one

/-- For `c3OnC2C2`, applied at `x`, the value is `c2c2OrderThreeAutComp^(toAdd x).val`. -/
lemma c3OnC2C2_apply (x : CyclicGroup 3) :
    c3OnC2C2 x = c2c2OrderThreeAutComp ^ ((Multiplicative.toAdd x).val : ℤ) :=
  cyclicHom_apply_eq_zpow 3 c2c2OrderThreeAutComp c2c2OrderThreeAutComp_pow_three_eq_one x

lemma c3OnC2C2_range_le_zpowers :
    c3OnC2C2.range ≤ Subgroup.zpowers c2c2OrderThreeAutComp := by
  rintro y ⟨x, rfl⟩
  exact ⟨((Multiplicative.toAdd x).val : ℤ), (c3OnC2C2_apply x).symm⟩

lemma c2c2OrderThreeAutComp_mem_c3OnC2C2_range :
    c2c2OrderThreeAutComp ∈ c3OnC2C2.range := by
  haveI : Fact (1 < 3) := ⟨by norm_num⟩
  refine ⟨Multiplicative.ofAdd (1 : ZMod 3), ?_⟩
  rw [c3OnC2C2_apply]
  show c2c2OrderThreeAutComp ^ ((1 : ZMod 3).val : ℤ) = c2c2OrderThreeAutComp
  rw [ZMod.val_one]; exact zpow_one _

lemma c3OnC2C2_range_card : Nat.card c3OnC2C2.range = 3 := by
  have hle := c3OnC2C2_range_le_zpowers
  have hmem := c2c2OrderThreeAutComp_mem_c3OnC2C2_range
  have hge := Subgroup.zpowers_le.mpr hmem
  rw [le_antisymm hle hge, Nat.card_zpowers, orderOf_c2c2OrderThreeAutComp]

-- c4OnC5Pow2 range cardinality: range is generated by `pow2AutC5`, which has order 4.

lemma pow2AutC5_pow_four_eq_one : pow2AutC5 ^ 4 = 1 := by
  ext x; change (((x^2)^2)^2)^2 = x; revert x; decide

lemma pow2AutC5_pow_two_ne_one : pow2AutC5 ^ 2 ≠ 1 := by
  intro h
  have := MulEquiv.ext_iff.mp h (Multiplicative.ofAdd (1 : ZMod 5))
  revert this; decide

lemma pow2AutC5_ne_one : pow2AutC5 ≠ 1 := by
  intro h
  have := MulEquiv.ext_iff.mp h (Multiplicative.ofAdd (1 : ZMod 5))
  revert this; decide

lemma orderOf_pow2AutC5 : orderOf pow2AutC5 = 4 := by
  have hdvd : orderOf pow2AutC5 ∣ 4 := orderOf_dvd_of_pow_eq_one pow2AutC5_pow_four_eq_one
  have hle : orderOf pow2AutC5 ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hne1 : orderOf pow2AutC5 ≠ 1 :=
    fun h => pow2AutC5_ne_one (orderOf_eq_one_iff.mp h)
  have hne2 : orderOf pow2AutC5 ≠ 2 :=
    fun h => pow2AutC5_pow_two_ne_one (orderOf_dvd_iff_pow_eq_one.mp (h ▸ dvd_refl _))
  have hpos : 0 < orderOf pow2AutC5 := orderOf_pos _
  interval_cases (orderOf pow2AutC5) <;>
    first | rfl | (exfalso; omega) | (exfalso; revert hdvd; decide)

/-- For `c4OnC5Pow2`, applied at `x`, the value is `pow2AutC5^(toAdd x).val`. -/
lemma c4OnC5Pow2_apply (x : CyclicGroup 4) :
    c4OnC5Pow2 x = pow2AutC5 ^ ((Multiplicative.toAdd x).val : ℤ) :=
  cyclicHom_apply_eq_zpow 4 pow2AutC5 pow2AutC5_pow_four_eq_one x

lemma c4OnC5Pow2_range_le_zpowers_pow2 :
    c4OnC5Pow2.range ≤ Subgroup.zpowers pow2AutC5 := by
  rintro y ⟨x, rfl⟩
  exact ⟨((Multiplicative.toAdd x).val : ℤ), (c4OnC5Pow2_apply x).symm⟩

lemma pow2AutC5_mem_c4OnC5Pow2_range : pow2AutC5 ∈ c4OnC5Pow2.range := by
  haveI : Fact (1 < 4) := ⟨by norm_num⟩
  refine ⟨Multiplicative.ofAdd (1 : ZMod 4), ?_⟩
  rw [c4OnC5Pow2_apply]
  show pow2AutC5 ^ ((1 : ZMod 4).val : ℤ) = pow2AutC5
  rw [ZMod.val_one]; exact zpow_one _

lemma c4OnC5Pow2_range_card  : Nat.card c4OnC5Pow2.range = 4 := by
  have hle := c4OnC5Pow2_range_le_zpowers_pow2
  have hmem := pow2AutC5_mem_c4OnC5Pow2_range
  have hge := Subgroup.zpowers_le.mpr hmem
  rw [le_antisymm hle hge, Nat.card_zpowers, orderOf_pow2AutC5]

-- Bridge for retrieve 12 3, retrieve 20 3, retrieve 28 3 (uses c4OnCqInv).
lemma canonicalC4OnCqAction_iso_c4OnCqInv
    (q : ℕ) [hq : Fact q.Prime] (hq2 : q ≠ 2)
    (h_range_card_eq : Nat.card (c4OnCqInv q).range = 2) :
    Nonempty (SemidirectProduct (CyclicGroup q) (CyclicGroup 4) (canonicalC4OnCqAction hq2)
      ≃* SemidirectProduct (CyclicGroup q) (CyclicGroup 4) (c4OnCqInv q)) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  haveI : Finite (CyclicGroup q) :=
    Nat.finite_of_card_ne_zero (by rw [card_cyclicGroup]; exact hq.out.ne_zero)
  have h_aut_iso : MulAut (CyclicGroup q) ≃* (ZMod q)ˣ := by
    have h' := IsCyclic.mulAutMulEquiv (CyclicGroup q)
    rwa [card_cyclicGroup] at h'
  haveI : Finite (MulAut (CyclicGroup q)) := Finite.of_equiv _ h_aut_iso.toEquiv.symm
  haveI hcyc : IsCyclic (MulAut (CyclicGroup q)) :=
    (MulEquiv.isCyclic h_aut_iso).mpr (ZMod.isCyclic_units_prime hq.out)
  have h_canon_card : Nat.card (canonicalC4OnCqAction hq2).range = 2 := by
    have h := sdpCanonicalAction_range_card (N := CyclicGroup q) (K := CyclicGroup 4)
      (show (2:ℕ) ≠ q by omega) hq2 2 1 Nat.one_pos
      (by rw [card_cyclicGroup, pow_one]) (by rw [card_cyclicGroup]; norm_num)
      1 (one_le_min_two_factorization_two hq2)
    simpa using h
  exact semidirectProduct_iso_if_range_card_eq (p := 2) (m := 2)
    ⟨by norm_num⟩
    (by rw [card_cyclicGroup]; norm_num)
    (canonicalC4OnCqAction hq2) (c4OnCqInv q) hcyc
    (h_canon_card.trans h_range_card_eq.symm)

-- Bridge for retrieve 20 4 (uses c4OnC5Pow2, range card 4).
lemma canonicalC4OnCqAction_r2_iso_c4OnC5Pow2
    (h_1_mod_4 : (5:ℕ) ≡ 1 [MOD 4]) :
    Nonempty (SemidirectProduct (CyclicGroup 5) (CyclicGroup 4) (canonicalC4OnCqAction_r2 h_1_mod_4)
      ≃* SemidirectProduct (CyclicGroup 5) (CyclicGroup 4) c4OnC5Pow2) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Finite (CyclicGroup 5) :=
    Nat.finite_of_card_ne_zero (by rw [card_cyclicGroup]; norm_num)
  have h_aut_iso : MulAut (CyclicGroup 5) ≃* (ZMod 5)ˣ := by
    have h' := IsCyclic.mulAutMulEquiv (CyclicGroup 5)
    rwa [card_cyclicGroup] at h'
  haveI : Finite (MulAut (CyclicGroup 5)) := Finite.of_equiv _ h_aut_iso.toEquiv.symm
  haveI hcyc : IsCyclic (MulAut (CyclicGroup 5)) :=
    (MulEquiv.isCyclic h_aut_iso).mpr (ZMod.isCyclic_units_prime (by norm_num : Nat.Prime 5))
  have h_canon_card : Nat.card (canonicalC4OnCqAction_r2 h_1_mod_4).range = 4 := by
    have h := sdpCanonicalAction_range_card (N := CyclicGroup 5) (K := CyclicGroup 4)
      (show (2:ℕ) ≠ 5 by norm_num) (by norm_num) 2 1 Nat.one_pos
      (by rw [card_cyclicGroup, pow_one]) (by rw [card_cyclicGroup]; norm_num)
      2 (two_le_min_two_factorization_two_of_one_mod_four h_1_mod_4)
    simpa using h
  exact semidirectProduct_iso_if_range_card_eq (p := 2) (m := 2)
    ⟨by norm_num⟩
    (by rw [card_cyclicGroup]; norm_num)
    (canonicalC4OnCqAction_r2 h_1_mod_4) c4OnC5Pow2 hcyc
    (h_canon_card.trans c4OnC5Pow2_range_card.symm)

-- Bridge for retrieve 12 4, retrieve 20 5, retrieve 28 4 (uses c2c2OnCqInv).
lemma canonicalC2C2OnCqAction_iso_c2c2OnCqInv
    (q : ℕ) [hq : Fact q.Prime] (hq2 : q ≠ 2)
    (h_pdvd : (2:ℕ) ∣ q - 1)
    (h_range_card_eq : Nat.card (c2c2OnCqInv q).range = 2) :
    Nonempty (SemidirectProduct (CyclicGroup q) (CyclicGroup 2 × CyclicGroup 2)
        (canonicalC2C2OnCqAction hq2)
      ≃* SemidirectProduct (CyclicGroup q) (CyclicGroup 2 × CyclicGroup 2) (c2c2OnCqInv q)) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h_canon_card : Nat.card (canonicalC2C2OnCqAction hq2).range = 2 := by
    -- canonicalC2C2OnCqAction = (sdpCanonicalAction ...) .comp MonoidHom.fst, and the .comp doesn't
    -- change the range (the .fst is surjective on the C_2 factor).
    change Nat.card ((sdpCanonicalAction (p := 2) (q := q) _ _ 1 1 _ _ _ 1 _).comp
        (MonoidHom.fst (CyclicGroup 2) (CyclicGroup 2))).range = 2
    have h_comp_range : ∀ (f : CyclicGroup 2 →* MulAut (CyclicGroup q)),
        (f.comp (MonoidHom.fst (CyclicGroup 2) (CyclicGroup 2))).range = f.range :=
      fun f => by
        ext y; simp only [MonoidHom.mem_range, MonoidHom.comp_apply, MonoidHom.coe_fst]
        exact ⟨fun ⟨⟨a, _⟩, h⟩ => ⟨a, h⟩, fun ⟨a, ha⟩ => ⟨(a, 1), ha⟩⟩
    rw [h_comp_range]
    have h := sdpCanonicalAction_range_card (N := CyclicGroup q) (K := CyclicGroup 2)
      (show (2:ℕ) ≠ q by omega) hq2 1 1 Nat.one_pos
      (by rw [card_cyclicGroup, pow_one]) (by rw [card_cyclicGroup, pow_one])
      1 (by have := one_le_min_two_factorization_two hq2; omega)
    simpa using h
  have h_canon_ne : canonicalC2C2OnCqAction hq2 ≠ 1 := by
    intro hc; simp [hc] at h_canon_card
  have h_surr_ne : c2c2OnCqInv q ≠ 1 := by
    intro hc; rw [hc] at h_range_card_eq
    have : (1 : CyclicGroup 2 × CyclicGroup 2 →* MulAut (CyclicGroup q)).range = ⊥ := by
      ext x; simp [Subgroup.mem_bot]
    rw [this, Subgroup.card_bot] at h_range_card_eq
    norm_num at h_range_card_eq
  exact semidirectProduct_CpCp_iso (p := 2) (q := q) h_pdvd
    (canonicalC2C2OnCqAction hq2) (c2c2OnCqInv q) h_canon_ne h_surr_ne
    h_canon_card h_range_card_eq

-- Bridge for retrieve 12 5 (uses c3OnC2C2).
lemma canonicalC3OnC2C2Action_iso_c3OnC2C2 :
    Nonempty (SemidirectProduct (CyclicGroup 2 × CyclicGroup 2) (CyclicGroup 3)
        canonicalC3OnC2C2Action
      ≃* SemidirectProduct (CyclicGroup 2 × CyclicGroup 2) (CyclicGroup 3) c3OnC2C2) :=
  semidirectProduct_C3_on_C2C2_iso canonicalC3OnC2C2Action c3OnC2C2
    canonicalC3OnC2C2Action_range_card c3OnC2C2_range_card
