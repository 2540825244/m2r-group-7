import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import «M2rGroup7».CyclicGroup
import «M2rGroup7».P2qClassification.PqClassification
import «M2rGroup7».P2qClassification.FourQClassification
import «M2rGroup7».P2qClassification.TwoPSquaredClassification
import «M2rGroup7».Order30.Order30Classification
import Mathlib.Tactic
import Mathlib.RingTheory.ZMod.UnitsCyclic

-- The generic Group (retrieve n i) instance uses split + infer_instance across ~70 arms;
-- importing FourQClassification enlarges the instance environment enough to push past 200k.
set_option maxHeartbeats 800000

abbrev maximumOrder : Nat := 31

/-- Alternating group generator -/
def AlternatingGroup (n : Nat) [NeZero n] := ↥(alternatingGroup (Fin n))
  deriving DecidableEq, Group, Fintype

/-- Symmetric group generator -/
def SymmetricGroup (n : Nat) := Equiv.Perm (Fin n)
  deriving DecidableEq, Group, Fintype

/-- Special linear group `SL(2, ZMod p)` (order `p(p²-1)` for prime `p`). -/
def SL2 (p : Nat) [NeZero p] := Matrix.SpecialLinearGroup (Fin 2) (ZMod p)
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

/-- Inversion on `CyclicGroup q` squared equals identity. -/
lemma inv_aut_pow_two_eq_one (q : ℕ) [NeZero q] :
    (MulEquiv.inv (CyclicGroup q)) ^ 2 = 1 := by
  ext x; change (x⁻¹)⁻¹ = x; exact inv_inv x

/-- For the surrogate `c2OnCqInv q`, applied at `x`, the value is `inv^(toAdd x).val`. -/
lemma c2OnCqInv_apply (q : ℕ) [NeZero q] (x : CyclicGroup 2) :
    c2OnCqInv q x = (MulEquiv.inv (CyclicGroup q)) ^ ((Multiplicative.toAdd x).val : ℤ) :=
  cyclicHom_apply_eq_zpow 2 (MulEquiv.inv (CyclicGroup q)) (inv_aut_pow_two_eq_one q) x

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

/-- The hom `D_4 → C_2` projecting through `D_4/V_4 = C_2`, with kernel the V_4
subgroup `{r 0, r 2, sr 0, sr 2}`. Sends an element to the parity of its index. -/
def d4ToC2 : DihedralGroup 4 →* CyclicGroup 2 where
  toFun
    | .r i => Multiplicative.ofAdd (i.val : ZMod 2)
    | .sr i => Multiplicative.ofAdd (i.val : ZMod 2)
  map_one' := rfl
  map_mul' p q := by
    rcases p with i | i <;> rcases q with j | j <;> revert i j <;> decide

/-- The order-2 action `D_4 →* Aut(C_q)` factoring through `D_4 / V_4 = C_2`, sending
the non-V_4 elements (`{r 1, r 3, sr 1, sr 3}`) to inversion. -/
def d4OnCqInv (q : Nat) [NeZero q] : DihedralGroup 4 →* MulAut (CyclicGroup q) :=
  (c2OnCqInv q).comp d4ToC2

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
  | 6, 1 => SemidirectProduct (CyclicGroup 3) (CyclicGroup 2)
      (canonicalCpOnCqAction (by norm_num : (3:ℕ) ≠ 2)
        (by native_decide : 1 ≤ min 1 ((3 - 1 : ℕ).factorization 2)))
  | 6, 2 => CyclicGroup 6
  | 7, 1 => CyclicGroup 7
  | 8, 1 => CyclicGroup 8
  | 8, 2 => CyclicGroup 4 × CyclicGroup 2
  | 8, 3 => DihedralGroup 4
  | 8, 4 => QuaternionGroup 2
  | 8, 5 => CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2
  | 9, 1 => CyclicGroup 9
  | 9, 2 => CyclicGroup 3 × CyclicGroup 3
  | 10, 1 => SemidirectProduct (CyclicGroup 5) (CyclicGroup 2)
      (canonicalCpOnCqAction (by norm_num : (5:ℕ) ≠ 2)
        (by native_decide : 1 ≤ min 1 ((5 - 1 : ℕ).factorization 2)))
  | 10, 2 => CyclicGroup 10
  | 11, 1 => CyclicGroup 11
  | 12, 1 => CyclicGroup 12
  | 12, 2 => CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 3
  | 12, 3 => SemidirectProduct (CyclicGroup 3) (CyclicGroup 4)
      (canonicalC4OnCqAction (by norm_num : (3:ℕ) ≠ 2))
  | 12, 4 => SemidirectProduct (CyclicGroup 3) (CyclicGroup 2 × CyclicGroup 2)
      (canonicalC2C2OnCqAction (by norm_num : (3:ℕ) ≠ 2))
  | 12, 5 => SemidirectProduct (CyclicGroup 2 × CyclicGroup 2) (CyclicGroup 3)
      canonicalC3OnC2C2Action
  | 13, 1 => CyclicGroup 13
  | 14, 1 => SemidirectProduct (CyclicGroup 7) (CyclicGroup 2)
      (canonicalCpOnCqAction (by norm_num : (7:ℕ) ≠ 2)
        (by native_decide : 1 ≤ min 1 ((7 - 1 : ℕ).factorization 2)))
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
  | 18, 2 => CyclicGroup 3 × CyclicGroup 3 × CyclicGroup 2
  | 18, 3 => SemidirectProduct (CyclicGroup (3 ^ 2)) (CyclicGroup 2)
      (canonicalC2OnCp2Action (by norm_num : (3:ℕ) ≠ 2))
  | 18, 4 => SemidirectProduct (CyclicGroup 3 × CyclicGroup 3) (CyclicGroup 2)
      (canonicalC2OnCpCpAction_r1 (by norm_num : (3:ℕ) ≠ 2))
  | 18, 5 => SemidirectProduct (CyclicGroup 3 × CyclicGroup 3) (CyclicGroup 2)
      (canonicalC2OnCpCpAction_r2 3)
  | 19, 1 => CyclicGroup 19
  | 20, 1 => CyclicGroup 20
  | 20, 2 => CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 5
  | 20, 3 => SemidirectProduct (CyclicGroup 5) (CyclicGroup 4)
      (canonicalC4OnCqAction (by norm_num : (5:ℕ) ≠ 2))
  | 20, 4 => SemidirectProduct (CyclicGroup 5) (CyclicGroup 4)
      (canonicalC4OnCqAction_r2 (by native_decide : (5:ℕ) ≡ 1 [MOD 4]))
  | 20, 5 => SemidirectProduct (CyclicGroup 5) (CyclicGroup 2 × CyclicGroup 2)
      (canonicalC2C2OnCqAction (by norm_num : (5:ℕ) ≠ 2))
  | 21, 1 => SemidirectProduct (CyclicGroup 7) (CyclicGroup 3)
      (canonicalCpOnCqAction (by norm_num : (7:ℕ) ≠ 2)
        (by native_decide : 1 ≤ min 1 ((7 - 1 : ℕ).factorization 3)))
  | 21, 2 => CyclicGroup 21
  | 22, 1 => SemidirectProduct (CyclicGroup 11) (CyclicGroup 2)
      (canonicalCpOnCqAction (by norm_num : (11:ℕ) ≠ 2)
        (by native_decide : 1 ≤ min 1 ((11 - 1 : ℕ).factorization 2)))
  | 22, 2 => CyclicGroup 22
  | 23, 1 => CyclicGroup 23
  | 24, 1 => CyclicGroup 3 ⋊[c8OnCqInv 3] CyclicGroup 8
  | 24, 2 => CyclicGroup 24
  | 24, 3 => SL2 3
  | 24, 4 => QuaternionGroup 6
  | 24, 5 => DihedralGroup 3 × CyclicGroup 4
  | 24, 6 => DihedralGroup 12
  | 24, 7 => CyclicGroup 2 × QuaternionGroup 3
  | 24, 8 => CyclicGroup 3 ⋊[d4OnCqInv 3] DihedralGroup 4
  | 24, 9 => CyclicGroup 2 × CyclicGroup 12
  | 24, 10 => CyclicGroup 3 × DihedralGroup 4
  | 24, 11 => CyclicGroup 3 × QuaternionGroup 2
  | 24, 12 => SymmetricGroup 4
  | 24, 13 => CyclicGroup 2 × AlternatingGroup 4
  | 24, 14 => DihedralGroup 3 × (CyclicGroup 2 × CyclicGroup 2)
  | 24, 15 => CyclicGroup 3 × (CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 2)
  | 25, 1 => CyclicGroup 25
  | 25, 2 => CyclicGroup 5 × CyclicGroup 5
  | 26, 1 => SemidirectProduct (CyclicGroup 13) (CyclicGroup 2)
      (canonicalCpOnCqAction (by norm_num : (13:ℕ) ≠ 2)
        (by native_decide : 1 ≤ min 1 ((13 - 1 : ℕ).factorization 2)))
  | 26, 2 => CyclicGroup 26
  | 27, 1 => CyclicGroup 27
  | 28, 1 => CyclicGroup 28
  | 28, 2 => CyclicGroup 2 × CyclicGroup 2 × CyclicGroup 7
  | 28, 3 => SemidirectProduct (CyclicGroup 7) (CyclicGroup 4)
      (canonicalC4OnCqAction (by norm_num : (7:ℕ) ≠ 2))
  | 28, 4 => SemidirectProduct (CyclicGroup 7) (CyclicGroup 2 × CyclicGroup 2)
      (canonicalC2C2OnCqAction (by norm_num : (7:ℕ) ≠ 2))
  | 29, 1 => CyclicGroup 29
  | 30, 1 => CyclicGroup 30
  | 30, 2 => CyclicGroup 15 ⋊[canonicalC2OnC15Pow 14 (by decide)] CyclicGroup 2
  | 30, 3 => CyclicGroup 15 ⋊[canonicalC2OnC15Pow 11 (by decide)] CyclicGroup 2
  | 30, 4 => CyclicGroup 15 ⋊[canonicalC2OnC15Pow 4 (by decide)] CyclicGroup 2
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
  | 18 => 5
  | 19 => 1
  | 20 => 5
  | 21 => 2
  | 22 => 2
  | 23 => 1
  | 24 => 15
  | 25 => 2
  | 26 => 2
  | 27 => 1 -- It is 5 actually, will fill rest later
  | 28 => 4
  | 29 => 1
  | 30 => 4
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

