import «M2rGroup7».SmallGroupsLibrary
import «M2rGroup7».PqCase
import Mathlib

namespace OrderSixteen

structure ExtensionType where
  N : Type*
  [g : Group N]
  n : Nat
  act : MulAut N
  glue : N
  map_glue : act glue = glue
  pow_n : act^ n = MulAut.conj glue

instance (E : ExtensionType) : Group E.N := E.g

structure ExtRel (E_1 E_2 : ExtensionType) where
  φ : E_1.N ≃* E_2.N
  act_conj : E_2.act = (φ.symm.trans E_1.act).trans φ
  act_glue : E_2.glue = φ E_1.glue



end OrderSixteen
