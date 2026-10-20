@[expose] public section

open scoped DirectSum TensorProduct

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

namespace TensorAlgebra

/-- The canonical map from a direct sum of tensor powers to the tensor algebra. -/
def ofDirectSum : (⨁ n, ⨂[R]^n M) →ₐ[R] TensorAlgebra R M :=
  DirectSum.toAlgebra _ _ (fun _ => TensorPower.toTensorAlgebra) TensorPower.toTensorAlgebra_gOne
    (fun {_ _} => TensorPower.toTensorAlgebra_gMul)

end TensorAlgebra
end
