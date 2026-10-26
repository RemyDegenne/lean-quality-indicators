/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.GroupLikeHom
public import Mathlib.RingTheory.Bialgebra.GroupLike
public import Mathlib.RingTheory.Bialgebra.Hom

/-!
# Transport of group-like elements by bialgebra morphisms

A bialgebra morphism induces a monoid homomorphism on group-like elements.
Its underlying function is transport by the associated coalgebra morphism.
The construction respects identity and composition over a commutative semiring,
without commutativity or additive inverses in the source and target semirings.
The scalar, source, target and composition target may lie in independent universes.

## References

The group-like carrier and its monoid structure are due to Yaël Dillies and
Michał Mrugała in Mathlib's `Mathlib.RingTheory.Coalgebra.GroupLike` and
`Mathlib.RingTheory.Bialgebra.GroupLike`. The coalgebra transport uses their
`IsGroupLikeElem.map` through `GroupLike.map`. The bialgebra morphism and its
coalgebra projection are provided by Kenny Lau, Yury Kudryashov and Amelia
Livingston's `Mathlib.RingTheory.Bialgebra.Hom`.
-/

@[expose] public section

universe u v w x

namespace BialgHom

variable {R : Type u} {A : Type v} {B : Type w} {C : Type x}
variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
variable [Bialgebra R A] [Bialgebra R B] [Bialgebra R C]

/-- The monoid homomorphism on group-like elements induced by a bialgebra morphism. -/
def groupLikeMap (f : A →ₐc[R] B) : GroupLike R A →* GroupLike R B where
  toFun := GroupLike.map f.toCoalgHom
  map_one' := by
    apply GroupLike.ext
    exact map_one f
  map_mul' := by
    intro g h
    apply GroupLike.ext
    exact map_mul f g.val h.val

/-- The underlying value of the induced map on group-like elements is its image. -/
@[simp]
theorem groupLikeMap_val (f : A →ₐc[R] B) (g : GroupLike R A) :
    (f.groupLikeMap g).val = f g.val := rfl

/-- The identity bialgebra morphism induces the identity on group-like elements. -/
@[simp]
theorem groupLikeMap_id :
    (BialgHom.id R A).groupLikeMap = MonoidHom.id (GroupLike R A) := by
  apply MonoidHom.ext
  intro g
  exact GroupLike.map_id g

/-- The map on group-like elements of a composite is the composite of the induced maps. -/
@[simp]
theorem groupLikeMap_comp (f : A →ₐc[R] B) (h : B →ₐc[R] C) :
    (h.comp f).groupLikeMap = h.groupLikeMap.comp f.groupLikeMap := by
  apply MonoidHom.ext
  intro g
  exact GroupLike.map_comp f.toCoalgHom h.toCoalgHom g

end BialgHom
