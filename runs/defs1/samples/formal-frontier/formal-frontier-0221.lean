@[expose] public section

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A scheme viewed as an object of the dense-open rational-map category. -/
structure DenseOpenRationalScheme where
  toScheme : Scheme.{u}

end AlgebraicGeometry
end
