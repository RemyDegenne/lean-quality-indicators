public section

namespace Submodule

open Matrix Module

open LinearMap (BilinForm)

open TauCeti

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

variable {C D : Submodule R (ι → R)}

theorem IsSelfOrthogonal.le_euclideanDual (hC : IsSelfOrthogonal C) : C ≤ euclideanDual C :=
  hC

end Submodule
end
