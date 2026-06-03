# Suggestions for `Preliminary.lean`: Wild's Facts 3 and 4

From the team formalising `realise_ext_type_if_not_iso_to_C2_4` in
`M2rGroup7/SixteenClassification/Lemma3.lean`.

The current statements

```lean
lemma aut_C4_iso_C2 : Nonempty (MulAut (CyclicGroup 4) ≃* CyclicGroup 2)
lemma aut_C8_iso_C2_prod_C2 :
    Nonempty (MulAut (CyclicGroup 8) ≃* CyclicGroup 2 × CyclicGroup 2)
lemma aut_C4_prod_C2_iso_D8 :
    Nonempty (MulAut (CyclicGroup 4 × CyclicGroup 2) ≃* DihedralGroup 4)
```

are mathematically correct and the proofs are clean. For our downstream
case-analysis proofs they are however the *wrong shape*: they discard the
concrete iso we built and force every consumer to recover it via
`Classical.choice`. We can no longer talk about which iso we have, so we
cannot apply it to specific automorphisms.

This document lists the changes we would like to land in
`Preliminary.lean`. None of them require new mathematics; they only
reshape what is already proved.

## 1. Return `MulEquiv`, not `Nonempty`

Please expose the three results as concrete (`noncomputable`) `def`s and
derive the `Nonempty` wrapper as a one-liner if any caller still wants
it.

```lean
noncomputable def autC4Equiv :
    MulAut (CyclicGroup 4) ≃* CyclicGroup 2 := ...

noncomputable def autC8Equiv :
    MulAut (CyclicGroup 8) ≃* CyclicGroup 2 × CyclicGroup 2 := ...

noncomputable def autK8Equiv :
    MulAut (CyclicGroup 4 × CyclicGroup 2) ≃* DihedralGroup 4 := ...

lemma aut_C4_iso_C2 :
    Nonempty (MulAut (CyclicGroup 4) ≃* CyclicGroup 2) := ⟨autC4Equiv⟩
-- and similarly for the other two
```

The `aut_C4_prod_C2_iso_D8` proof already builds an explicit `f : D₄ →*
MulAut (K₈)` and calls `MulEquiv.ofBijective f (by native_decide)` —
keeping that term as a `def` costs nothing.

## 2. Add `decide`-style enumeration lemmas

For Lemma 3 we need, repeatedly, to know that an arbitrary
`τ : MulAut (CyclicGroup 8)` is one of the four library automorphisms,
and similarly for `MulAut (CyclicGroup 4 × CyclicGroup 2)`. Because both
ambient `MulAut` groups are finite with `DecidableEq`, the enumerations
are pure `decide`/`native_decide` once stated. Please add:

```lean
open Multiplicative in
lemma MulAut.forall_eq_C8 (τ : MulAut (CyclicGroup 8)) :
    τ = 1 ∨
    τ = c2OnC8Pow3 (ofAdd 1) ∨
    τ = c2OnC8Pow5 (ofAdd 1) ∨
    τ = c2OnC8Pow7 (ofAdd 1) := by
  native_decide

open Multiplicative in
lemma MulAut.forall_eq_C4 (τ : MulAut (CyclicGroup 4)) :
    τ = 1 ∨ τ = c4OnC4Inv (ofAdd 1) := by
  native_decide
```

`c2OnC8Pow3`, `c2OnC8Pow5` are in `SmallGroupsLibrary.lean`; `c2OnC8Pow7`
is in `SixteenClassification/Blueprints.lean`.

For K₈ we need an enumeration of involutions modulo conjugation.
A statement that suffices for us:

```lean
open Multiplicative in
lemma MulAut.involution_K8_conj_to_rep
    (τ : MulAut (CyclicGroup 4 × CyclicGroup 2)) (hτ : τ ^ 2 = 1) :
    ∃ σ : MulAut (CyclicGroup 4 × CyclicGroup 2),
      σ * τ * σ⁻¹ = 1 ∨
      σ * τ * σ⁻¹ = psi3 ∨
      σ * τ * σ⁻¹ = psi5 ∨
      σ * τ * σ⁻¹ = psi6 := by
  native_decide
```

(`psi3`, `psi5` from `Blueprints.lean`; `psi6` from
`SmallGroupsLibrary.lean`.)

If `native_decide` is too slow for the K₈ version, splitting it into
"list all 8 involutions" + "split into 4 conjugacy classes" is also
fine — anything that exposes the four named representatives as the
canonical reps is workable. A `maxHeartbeats` bump as in
`aut_C4_prod_C2_iso_D8` is acceptable.

## 3. Optional: transfer-along-`MulEquiv` lemma

We have `RealiseExtType.transfer` already, but a tiny helper specialised
to `MulAut` would also help us state Fact 3/4 consequences uniformly:

```lean
lemma mulAut_eq_of_mulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (τ : MulAut G) :
    e.mulAutCongr τ = (MulAut.conj _).symm ... -- whatever shape you prefer
```

This is *not* required; we can write it on our side. Mentioning it only
in case it fits naturally with the way you already think about these
isos.

## Why this matters for us

In `realise_with_normal_C8` we need, given `H ◁ G` with `H ≃* C₈` and
the induced `τ : MulAut H` from conjugation by an inducing element `a`,
to identify `τ` with one of `1, c2OnC8Pow3 (ofAdd 1), c2OnC8Pow5 (ofAdd
1), c2OnC8Pow7 (ofAdd 1)`. With

* `autC8Equiv` as a concrete `MulEquiv`, we can transport `τ` to
  `MulAut (CyclicGroup 8)`;
* `MulAut.forall_eq_C8` then collapses the case analysis to four
  branches.

Without either, we either dig through `Classical.choice` (`Nonempty`
form) or re-derive the enumeration ourselves. Same story for the K₈
side and `realise_with_normal_K8`, where we additionally need the
conjugacy reduction so that we can pick a class representative for `τ`.

## TL;DR

- Make the three results `noncomputable def ... ≃* ...`, keep
  `Nonempty` lemmas as thin wrappers.
- Add `MulAut.forall_eq_C4`, `MulAut.forall_eq_C8`, and a K₈
  involution-up-to-conjugation enumeration, all by `decide` /
  `native_decide`.
- No new mathematics needed — only reshaping.

Happy to land any of these on our side if it is easier; just let us
know which file you would like them in.
