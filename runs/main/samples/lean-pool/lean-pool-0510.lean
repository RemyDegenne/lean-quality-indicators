@[expose] public section

open scoped BigOperators

open Matrix Module.End InnerProductSpace

variable {𝕜 : Type _} [RCLike 𝕜]

theorem EuclideanSpace.orthonormalBasis.repr_eq_one {n : Type _} [Fintype n] :
    (EuclideanSpace.orthonormalBasis n 𝕜 :
      OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n)).repr = 1 :=
  rfl

end
