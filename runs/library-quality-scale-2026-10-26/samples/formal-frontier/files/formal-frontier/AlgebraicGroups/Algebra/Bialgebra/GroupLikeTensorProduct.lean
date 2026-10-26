/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.GroupLikeTensorProduct
public import AlgebraicGroups.Algebra.Bialgebra.GroupLike
public import Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# Group-like elements of a tensor product of bialgebras

`GroupLike.tensorMulEquiv` identifies the group-like elements of a tensor product
with pairs of group-like elements, compatibly with multiplication. Its underlying
equivalence is `GroupLike.tensorEquiv`: the forward maps are the two counit
projections, and the inverse has value the pure tensor of the two factors.

The scalar semiring is commutative, but the two bialgebras need not be. No
nontriviality assumption is needed: group-like elements are normalized by their
counits, including over a subsingleton scalar semiring. Naturality is inherited
from `GroupLike.tensorEquiv_mapCoalgHoms` using `BialgHom.groupLikeMap`. When group
structures are available, preservation of inverses follows from `map_inv`.

## References

The equivalence and coalgebra transport are provided by
`AlgebraicGroups.Algebra.Coalgebra.GroupLikeTensorProduct` and
`AlgebraicGroups.Algebra.Coalgebra.GroupLikeHom`. The group-like carrier and its
monoid structure are due to Yaël Dillies and Michał Mrugała in Mathlib's
`Mathlib.RingTheory.Coalgebra.GroupLike` and
`Mathlib.RingTheory.Bialgebra.GroupLike`. The tensor coalgebra and bialgebra
infrastructure is due to Amelia Livingston and Andrew Yang in
`Mathlib.RingTheory.Coalgebra.TensorProduct` and
`Mathlib.RingTheory.Bialgebra.TensorProduct`. Multiplication of pure tensors uses
Kim Morrison and Johan Commelin's `Mathlib.RingTheory.TensorProduct.Basic`.
-/

@[expose] public section

open scoped TensorProduct

universe uR uC uD

namespace GroupLike

/-- Group-like elements of a tensor product of bialgebras correspond
multiplicatively to pairs of group-like elements. The underlying equivalence is
`GroupLike.tensorEquiv`, and its inverse has value the pure tensor of the factors. -/
noncomputable def tensorMulEquiv
    (R : Type uR) (C : Type uC) (D : Type uD)
    [CommSemiring R] [Semiring C] [Bialgebra R C]
    [Semiring D] [Bialgebra R D] :
    GroupLike R (C ⊗[R] D) ≃* GroupLike R C × GroupLike R D where
  toEquiv := GroupLike.tensorEquiv R C D
  map_mul' x y := by
    obtain ⟨p, rfl⟩ := (tensorEquiv R C D).symm.surjective x
    obtain ⟨q, rfl⟩ := (tensorEquiv R C D).symm.surjective y
    apply (tensorEquiv R C D).symm.injective
    apply GroupLike.ext
    simp only [Equiv.toFun_as_coe, Equiv.symm_apply_apply, Equiv.apply_symm_apply,
      tensorEquiv_symm_val, val_mul, Prod.fst_mul, Prod.snd_mul,
      Algebra.TensorProduct.tmul_mul_tmul]

end GroupLike
