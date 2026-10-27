/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Coalgebra
public import AlgebraicGroups.Algebra.Coalgebra.FiniteSubcoalgebra
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite subcoalgebra containment over a field

The fundamental theorem of coalgebras gives a finite-dimensional subcoalgebra containing
any finitely generated subspace of a coalgebra over a field. Here finiteness is expressed
by `Module.Finite` on the subcoalgebra subtype, equipped with its restricted coalgebra.
The ambient coalgebra need not be finite-dimensional.

`Coalgebra.exists_finite_subcoalgebra` packages the finite submodule supplied by
`Coalgebra.exists_fg_submodule_comul_closed_of_finite` using `Subcoalgebra.mk'`.
`Coalgebra.exists_finite_subcoalgebra_of_finite` applies it to the span of a finite set.
These are existence statements: no least or uniquely determined finite subcoalgebra is
asserted.

## References

* J. S. Milne, *Algebraic Groups*, for the fundamental theorem of coalgebras over a field
  (bibliographic credit).
* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969, for the coefficient-coalgebra
  method used by the finite-submodule theorem.
* `AlgebraicGroups.Algebra.Coalgebra.FiniteSubcoalgebra`, for finite tensor-square-closed
  submodule containment. Its proof first uses a projective free-presentation splitting
  for a finite right coideal, then field coordinates for closure in both tensor factors.
* Mathlib's `Submodule.FG`, `Submodule.span_le`, `Submodule.fg_span` and
  `Module.Finite.iff_fg` for finite generation and the span-to-module-finiteness bridge;
  its field freeness and projectivity instances supply the finite-submodule theorem's
  projective step without an additional hypothesis.
* `AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Coalgebra`, for the restricted
  comultiplication, counit and coalgebra laws on a subcoalgebra subtype.
-/

@[expose] public section

universe u v

namespace Coalgebra

variable {K : Type u} {C : Type v}
variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

/-- The fundamental theorem of coalgebras over a field: every finitely generated subspace
is contained in a finite-dimensional subcoalgebra. This is the fundamental statement in
Milne's *Algebraic Groups*, obtained here from the finite-submodule coefficient-coalgebra
theorem and the restricted coalgebra construction. -/
theorem exists_finite_subcoalgebra (M : Submodule K C) (hM : M.FG) :
    ∃ D : Subcoalgebra K C, M ≤ D.toSubmodule ∧ Module.Finite K D := by
  obtain ⟨t, ht⟩ := hM
  obtain ⟨S, htS, hSfg, hSclosed⟩ :=
    exists_fg_submodule_comul_closed_of_finite (K := K) t.finite_toSet
  have hMS : M ≤ S := by
    rw [← ht]
    exact Submodule.span_le.mpr htS
  refine ⟨Subcoalgebra.mk' S (fun {x} hx => hSclosed x hx), ?_, ?_⟩
  · simpa only [Subcoalgebra.toSubmodule_mk'] using hMS
  · exact (Module.Finite.iff_fg.mpr hSfg : Module.Finite K S)

/-- Every finite subset of a coalgebra over a field lies in a finite-dimensional
subcoalgebra, by applying the fundamental theorem of coalgebras to its span. -/
theorem exists_finite_subcoalgebra_of_finite {s : Set C} (hs : s.Finite) :
    ∃ D : Subcoalgebra K C, s ⊆ (D : Set C) ∧ Module.Finite K D := by
  obtain ⟨D, hD, hfinite⟩ :=
    exists_finite_subcoalgebra (Submodule.span K s) (Submodule.fg_span hs)
  refine ⟨D, ?_, hfinite⟩
  intro x hx
  exact Subcoalgebra.mem_toSubmodule.mp (hD (Submodule.subset_span hx))

end Coalgebra
