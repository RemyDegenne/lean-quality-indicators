/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Integer singleton spans in unital rings

An additively cyclic unital ring has surjective integer casts. Consequently, if
integer casts into a ring are not surjective, every singleton integer span is
proper. Multiplication need not be associative or commutative, and the integer
module structure is the canonical one induced by the additive group.

## Implementation notes

The cyclic-ring bridge reuses Mathlib's `AddMonoidHom.map_addCyclic` on
`AddMonoidHom.mulRight`, then evaluates at `1` using `Int.smul_one_eq_cast`.
The span implication uses `Submodule.span_singleton_eq_top_iff` to supply the
existing `IsAddCyclic` witness. No self-scalar module structure is needed.

## References

* Mathlib's cyclic-group development by Johannes Hölzl, ring development by
  Jeremy Avigad and collaborators, integer-module development by Nathaniel
  Thomas and collaborators, and singleton-span development by Johannes Hölzl
  and collaborators supply the reused formalization interfaces and approach.
-/

@[expose] public section

universe u

/-- Integer casts into an additively cyclic unital ring are surjective.
The proof applies Mathlib's `AddMonoidHom.map_addCyclic` to right multiplication
by each element and evaluates the resulting integer scalar map at `1`. -/
theorem IsAddCyclic.intCast_surjective
    {R : Type u} [NonAssocRing R] [IsAddCyclic R] :
    Function.Surjective (Int.cast : ℤ → R) := by
  intro a
  obtain ⟨m, hm⟩ := AddMonoidHom.map_addCyclic (AddMonoidHom.mulRight a)
  refine ⟨m, ?_⟩
  simpa only [AddMonoidHom.mulRight_apply, one_mul, Int.smul_one_eq_cast]
    using (hm 1).symm

/-- If one element generates a unital ring as an integer module, integer casts
are surjective. Mathlib's `Submodule.span_singleton_eq_top_iff` gives the cyclic
additive-group witness for the canonical integer action. -/
theorem Submodule.intCast_surjective_of_span_singleton_eq_top
    {R : Type u} [NonAssocRing R] {x : R}
    (hx : Submodule.span ℤ ({x} : Set R) = ⊤) :
    Function.Surjective (Int.cast : ℤ → R) := by
  let : IsAddCyclic R :=
    ⟨⟨x, (Submodule.span_singleton_eq_top_iff ℤ x).mp hx⟩⟩
  exact IsAddCyclic.intCast_surjective

/-- If integer casts into a unital ring are not surjective, every singleton
integer span is proper. This is the contrapositive of
`Submodule.intCast_surjective_of_span_singleton_eq_top`, with no restriction on
the generator. -/
theorem Submodule.int_span_singleton_ne_top_of_not_surjective_intCast
    {R : Type u} [NonAssocRing R]
    (hℤ : ¬ Function.Surjective (Int.cast : ℤ → R)) (x : R) :
    Submodule.span ℤ ({x} : Set R) ≠ ⊤ := by
  intro hx
  exact hℤ (Submodule.intCast_surjective_of_span_singleton_eq_top hx)
