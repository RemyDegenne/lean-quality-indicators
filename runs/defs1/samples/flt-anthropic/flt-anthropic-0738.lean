namespace P2MW.S_ModularCurve_UVCrossingModel_exists_algEquiv_tensorProduct_map_of_finite_of_free

set_option autoImplicit false

universe u

open scoped TensorProduct

open MvPowerSeries (coeff)

namespace ModelBCAux

section PowerSeries

variable {W W' : Type u} [CommRing W] [CommRing W'] [Algebra W W']

variable (σ : Type*)

variable {ι : Type*} [Fintype ι] (b : Module.Basis ι W W')

noncomputable def bcInv (g : MvPowerSeries σ W') : MvPowerSeries σ W ⊗[W] W' :=
  ∑ i, coordSeries σ b i g ⊗ₜ[W] b i

end PowerSeries
end ModelBCAux
end P2MW.S_ModularCurve_UVCrossingModel_exists_algEquiv_tensorProduct_map_of_finite_of_free
