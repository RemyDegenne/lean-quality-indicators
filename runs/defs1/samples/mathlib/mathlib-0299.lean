@[expose] public section

universe u1 u2 u3

variable {R M N : Type*}

variable [CommRing R] [AddCommGroup M] [AddCommGroup N]

variable [Module R M] [Module R N]

variable (Q : QuadraticForm R M)

namespace CliffordAlgebra

/-- Fold a bilinear map along the generators of a term of the clifford algebra, with the rule
given by `foldr' Q f hf n (ι Q m * x) = f m (x, foldr' Q f hf n x)`.
Note this is like `CliffordAlgebra.foldr`, but with an extra `x` argument.
Implement the recursion scheme `F[n0](m * x) = f(m, (x, F[n0](x)))`. -/
def foldr' (f : M →ₗ[R] CliffordAlgebra Q × N →ₗ[R] N)
    (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n : N) : CliffordAlgebra Q →ₗ[R] N :=
  LinearMap.snd _ _ _ ∘ₗ foldr Q (foldr'Aux Q f) (foldr'Aux_foldr'Aux Q _ hf) (1, n)

end CliffordAlgebra
end
