@[expose] public section

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace DenseOpenRationalSchemeOver

/-- Construct an object with an arbitrary total structure morphism. -/
def of {S X : Scheme.{u}} (p : X ⟶ S) : DenseOpenRationalSchemeOver S := ⟨X, p⟩

end DenseOpenRationalSchemeOver
end AlgebraicGeometry
end
