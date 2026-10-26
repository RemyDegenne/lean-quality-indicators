/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.MatrixNilpotentIdeal
public import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# Finite matrices with nilpotent entries

A finite square matrix over a commutative semiring is nilpotent if each entry is
nilpotent. The entries span a finitely generated ideal contained in the nilradical;
Mathlib's finite-generation criterion makes that ideal nilpotent, and
`Matrix.isNilpotent_of_isNilpotent_ideal` then applies to the matrix.

Commutativity is used for the nilradical ideal and its finite-generation criterion.
No Noetherian hypothesis is needed. Empty index types and zero semirings are included.

## References

* Mathlib's `Submodule.fg_span`, `mem_nilradical`, and
  `Ideal.FG.isNilpotent_iff_le_nilradical` supply the ideal argument.
* The General Linear Groups uniform-ideal matrix nilpotence theorem supplies the
  passage from ideal nilpotence to matrix nilpotence.
-/

@[expose] public section

universe u v

namespace Matrix

/-- A finite square matrix over a commutative semiring is nilpotent when all its
entries are nilpotent. The finitely generated entry ideal is nilpotent by
`Ideal.FG.isNilpotent_iff_le_nilradical`, so
`Matrix.isNilpotent_of_isNilpotent_ideal` applies. Commutativity is used for this
ideal criterion; neither nonemptiness of the index nor nontriviality of the semiring
is required. -/
theorem isNilpotent_of_isNilpotent_entries {R : Type u} [CommSemiring R]
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (hA : ∀ i j, IsNilpotent (A i j)) : IsNilpotent A := by
  let I : Ideal R := Ideal.span (Set.range fun p : ι × ι => A p.1 p.2)
  have hI : I.FG := Submodule.fg_span (Set.finite_range _)
  refine isNilpotent_of_isNilpotent_ideal I A (fun i j => ?_) ?_
  · exact Ideal.subset_span ⟨(i, j), rfl⟩
  · apply hI.isNilpotent_iff_le_nilradical.mpr
    refine Ideal.span_le.mpr ?_
    rintro x ⟨⟨i, j⟩, rfl⟩
    exact mem_nilradical.mpr (hA i j)

end Matrix
