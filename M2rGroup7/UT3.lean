import Mathlib

set_option maxHeartbeats 400000

/-!
# UT₃(p) — The Unitriangular Matrix Group

The group of upper unitriangular 3×3 matrices over 𝔽_p,
encoded as triples (a, b, c) with multiplication:
  (x * y).a = x.a + y.a
  (x * y).b = x.b + y.b + x.a * y.c
  (x * y).c = x.c + y.c
-/

@[ext]
structure UT3 (p : ℕ) [Fact (Nat.Prime p)] where
  a : ZMod p
  b : ZMod p
  c : ZMod p

namespace UT3

variable {p : ℕ} [Fact (Nat.Prime p)]

instance : Mul (UT3 p) where
  mul x y :=
    { a := x.a + y.a
      b := x.b + y.b + x.a * y.c
      c := x.c + y.c }

instance : One (UT3 p) where
  one := { a := 0, b := 0, c := 0 }

instance : Inv (UT3 p) where
  inv x :=
    { a := -x.a
      b := -x.b + x.a * x.c
      c := -x.c }

@[simp] lemma mul_a (x y : UT3 p) : (x * y).a = x.a + y.a := rfl
@[simp] lemma mul_b (x y : UT3 p) : (x * y).b = x.b + y.b + x.a * y.c := rfl
@[simp] lemma mul_c (x y : UT3 p) : (x * y).c = x.c + y.c := rfl
@[simp] lemma one_a : (1 : UT3 p).a = 0 := rfl
@[simp] lemma one_b : (1 : UT3 p).b = 0 := rfl
@[simp] lemma one_c : (1 : UT3 p).c = 0 := rfl
@[simp] lemma inv_a (x : UT3 p) : x⁻¹.a = -x.a := rfl
@[simp] lemma inv_b (x : UT3 p) : x⁻¹.b = -x.b + x.a * x.c := rfl
@[simp] lemma inv_c (x : UT3 p) : x⁻¹.c = -x.c := rfl

instance : Group (UT3 p) where
  mul_assoc x y z := by ext <;> simp <;> ring
  one_mul x       := by ext <;> simp
  mul_one x       := by ext <;> simp
  inv_mul_cancel x := by ext <;> simp <;> ring

instance : Fintype (UT3 p) :=
  Fintype.ofEquiv (ZMod p × ZMod p × ZMod p)
    { toFun := fun ⟨a, b, c⟩ => ⟨a, b, c⟩
      invFun := fun x => ⟨x.a, x.b, x.c⟩
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }

lemma card_eq : Nat.card (UT3 p) = p ^ 3 := by
  rw [Nat.card_eq_fintype_card]
  have : Fintype.card (UT3 p) = Fintype.card (ZMod p × ZMod p × ZMod p) := by
    exact Fintype.card_congr
      { toFun := fun x => (x.a, x.b, x.c)
        invFun := fun ⟨a, b, c⟩ => ⟨a, b, c⟩
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
  simp only [this, Fintype.card_prod, ZMod.card]
  ring

end UT3
