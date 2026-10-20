@[expose] public section

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace IntegralDenseOpenRationalScheme

/-- Package an integral scheme as an object in the dense-open rational-map category. -/
def of (X : Scheme.{u}) [IsIntegral X] : IntegralDenseOpenRationalScheme.{u} :=
  ⟨DenseOpenRationalScheme.of X, ‹IsIntegral X›⟩

end IntegralDenseOpenRationalScheme
end AlgebraicGeometry
end
