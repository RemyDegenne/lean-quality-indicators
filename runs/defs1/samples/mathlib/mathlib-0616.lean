@[expose] public section

universe u v w w'

open TensorAlgebra DirectSum TensorPower

variable {I : Type u} [DecidableEq I] {i : I} -- The type of the indexing set
  (R : Type v) [CommSemiring R] -- The commutative semiring `R`
  (A : I → Type w) [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] -- The collection of `R`-algebras
  {B : Type w'} [Semiring B] [Algebra R B] -- Another `R`-algebra
  (maps : {i : I} → A i →ₐ[R] B)

namespace LinearAlgebra.FreeProduct

open scoped Function

/-- The free product of the collection of `R`-algebras `A i`,
as a quotient of `PowerAlgebra R A` -/
@[reducible] def asPowers := FreeProduct.ringCon' R A |>.Quotient

end LinearAlgebra.FreeProduct
end
