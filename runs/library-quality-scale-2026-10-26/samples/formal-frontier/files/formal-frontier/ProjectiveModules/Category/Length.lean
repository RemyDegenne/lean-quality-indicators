/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Category.SubmoduleEquivalence
public import Mathlib.RingTheory.Length

/-!
# Module length under module-category equivalences

An ordinary equivalence of categories of left modules preserves numerical length
in `ℕ∞`, including infinite length. It therefore preserves and reflects the
proposition `IsFiniteLength`. These statements apply to every module, with
independent scalar and carrier universes and no commutativity assumption.

The submodule order isomorphism `ModuleCat.submoduleOrderIsoOfEquivalence`
identifies the submodule lattices. Mathlib expresses length as their Krull
dimension, and `Module.length_ne_top_iff` characterizes finite length.

## References

The numerical invariant and its finite-length characterization use Mathlib's
module-length formalization by Andrew Yang and its order-theoretic Krull
dimension API by Jujian Zhang, Fangming Li and Joachim Breitner. Submodule
transport uses the Mathlib formalizations credited in
`ProjectiveModules.Category.SubmoduleEquivalence`.
-/

@[expose] public section

universe uR uS vR vS

open CategoryTheory

namespace ModuleCat

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- An ordinary equivalence of categories of left modules preserves numerical
length for every module, including length `⊤`. -/
theorem length_eq_of_equivalence
    (e : ModuleCat.{vR} R ≌ ModuleCat.{vS} S) (X : ModuleCat.{vR} R) :
    Module.length S (e.functor.obj X) = Module.length R X := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact (Order.krullDim_eq_of_orderIso (submoduleOrderIsoOfEquivalence e X)).symm

/-- An ordinary equivalence of categories of left modules preserves and reflects
finite length, as characterized by `Module.length_ne_top_iff`. -/
theorem isFiniteLength_iff_of_equivalence
    (e : ModuleCat.{vR} R ≌ ModuleCat.{vS} S) (X : ModuleCat.{vR} R) :
    IsFiniteLength S (e.functor.obj X) ↔ IsFiniteLength R X := by
  rw [← Module.length_ne_top_iff, ← Module.length_ne_top_iff,
    length_eq_of_equivalence e X]

end ModuleCat
