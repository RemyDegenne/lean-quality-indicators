/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Algebra.Module.Torsion.Field

/-!
# Cardinality of group-like elements

For a torsion-free coalgebra over a commutative domain, the cardinality of its group-like
elements is at most its module rank. This follows from Mathlib's linear independence theorem
for group-like elements. The bundled type `GroupLike R C` and the predicate `IsGroupLikeElem R`
are those of Mathlib.

## Main results

* `GroupLike.cardinalMk_le_rank`: the cardinal bound, without a finiteness hypothesis.
* `GroupLike.finite_of_rank_lt_aleph0` and `GroupLike.setFinite_of_rank_lt_aleph0`: finite
  cardinal rank implies finiteness of both the bundled carrier and the predicate set.
* `GroupLike.nat_card_le_finrank_of_rank_lt_aleph0`: under the same finite-rank hypothesis,
  the number of group-like elements is bounded by the module's `finrank`.
* `GroupLike.instFinite`, `GroupLike.nat_card_le_finrank`, and `GroupLike.setFinite`: the
  corresponding consequences for a finitely generated module.

## Implementation notes

Finite cardinal rank is weaker than finite generation; neither freeness nor a field structure
is required. The `Finite` instance is proposition-valued and chooses no enumeration. Over a
field, Mathlib supplies `Module.IsTorsionFree` automatically.

Torsion-freeness means injectivity of scalar multiplication by regular scalars. Together with
the domain assumption this gives the scalar cancellation used by Mathlib's group-like linear
independence theorem. No nontriviality assumption on the coalgebra is needed. The domain
assumption cannot simply be omitted: orthogonal idempotents in `ℤ × ℤ` give four group-like
vectors in its rank-two diagonal coalgebra. Diagonal coalgebras on finitely supported integer
functions also give sharp finite bounds and infinite-rank examples.

Both `Nat.card` of an infinite type and `Module.finrank` of an infinite-rank module are zero.
The strict rank hypothesis is therefore retained in the finite-rank numerical bound, alongside
separate finiteness conclusions.

## References

* Mathlib's `Mathlib.RingTheory.Coalgebra.GroupLike`, by Yaël Dillies and Michał Mrugała,
  for the group-like carrier, its predicate-subtype equivalence, and linear independence.
* Mathlib's `Mathlib.LinearAlgebra.Dimension.Basic` and
  `Mathlib.LinearAlgebra.Dimension.Finite`, by Mario Carneiro, Johannes Hölzl, Sander Dahmen,
  and Kim Morrison, for cardinal rank bounds and finiteness of linearly independent families;
  `Mathlib.LinearAlgebra.Dimension.Finrank`, by Chris Hughes and Anne Baanen, and
  `Mathlib.LinearAlgebra.FreeModule.StrongRankCondition`, by Riccardo Brasca.
* Mathlib's cardinal finiteness and `toNat` APIs, by Johannes Hölzl, Mario Carneiro,
  Floris van Doorn, and Aaron Anderson.
* Mathlib's `Mathlib.RingTheory.Coalgebra.Basic`, by Ali Ramsey and Eric Wieser,
  `Mathlib.LinearAlgebra.Finsupp.VectorSpace`, by Johannes Hölzl, and
  `Mathlib.LinearAlgebra.FreeModule.Basic`, by Riccardo Brasca, for the diagonal coalgebra
  and basis APIs underlying the standard examples described above.
-/

@[expose] public section

universe u v

open scoped Cardinal

namespace GroupLike

variable (R : Type u) (C : Type v)
variable [CommRing R] [IsDomain R] [AddCommGroup C] [Module R C] [Coalgebra R C]
  [Module.IsTorsionFree R C]

/-- The cardinality of the group-like elements is bounded by the rank of the coalgebra.
This applies Mathlib's `linearIndep_groupLikeVal` and `LinearIndependent.cardinal_le_rank`. -/
theorem cardinalMk_le_rank : Cardinal.mk (GroupLike R C) ≤ Module.rank R C :=
  (linearIndep_groupLikeVal (R := R) (A := C)).cardinal_le_rank

/-- A torsion-free coalgebra of finite cardinal rank over a commutative domain has finitely many
group-like elements. This is the finite-rank consequence of Mathlib's group-like linear
independence theorem. -/
theorem finite_of_rank_lt_aleph0 (hrank : Module.rank R C < ℵ₀) :
    Finite (GroupLike R C) :=
  Cardinal.lt_aleph0_iff_finite.mp ((cardinalMk_le_rank R C).trans_lt hrank)

/-- The number of group-like elements is bounded by the finite rank of the coalgebra.
The rank hypothesis prevents the infinity-to-zero convention for `Module.finrank` from erasing
this bound. This applies Mathlib's group-like linear independence and cardinal rank bound. -/
theorem nat_card_le_finrank_of_rank_lt_aleph0 (hrank : Module.rank R C < ℵ₀) :
    Nat.card (GroupLike R C) ≤ Module.finrank R C :=
  Cardinal.toNat_le_toNat (cardinalMk_le_rank R C) hrank

/-- The set of elements satisfying Mathlib's group-like predicate is finite when the coalgebra
has finite cardinal rank. Finiteness is transported along Mathlib's `GroupLike.valEquiv`. -/
theorem setFinite_of_rank_lt_aleph0 (hrank : Module.rank R C < ℵ₀) :
    Set.Finite {c : C | IsGroupLikeElem R c} :=
  Set.finite_coe_iff.mp <|
    (valEquiv (R := R) (A := C)).finite_iff.mp (finite_of_rank_lt_aleph0 R C hrank)

/-- A module-finite torsion-free coalgebra over a domain has a finite type of group-like elements.
This is the module-finite specialization of the cardinal rank bound obtained from Mathlib's
group-like linear independence theorem. -/
instance instFinite [Module.Finite R C] : Finite (GroupLike R C) :=
  finite_of_rank_lt_aleph0 R C (Module.rank_lt_aleph0 R C)

/-- In a module-finite torsion-free coalgebra over a domain, the number of group-like elements is
at most the module's `finrank`. This specializes the finite-rank bound obtained from Mathlib's
group-like linear independence theorem. -/
theorem nat_card_le_finrank [Module.Finite R C] :
    Nat.card (GroupLike R C) ≤ Module.finrank R C :=
  nat_card_le_finrank_of_rank_lt_aleph0 R C (Module.rank_lt_aleph0 R C)

/-- In a module-finite torsion-free coalgebra over a domain, the set of group-like elements is
finite. This is the predicate-set form of the finiteness consequence of Mathlib's group-like
linear independence theorem. -/
theorem setFinite [Module.Finite R C] : Set.Finite {c : C | IsGroupLikeElem R c} :=
  setFinite_of_rank_lt_aleph0 R C (Module.rank_lt_aleph0 R C)

end GroupLike
