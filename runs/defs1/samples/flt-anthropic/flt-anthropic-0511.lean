namespace P2MW.S_Deformation_truncate_map_mem_wittHom_of_forall_coeff_ghostComponent_eq_logCovector

set_option autoImplicit false

universe u v

namespace S17L2c

open scoped TensorProduct

open MvPowerSeries

section Kappa

variable (𝓞 : Type*) [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)] (R : Type*) [CommRing R] [HopfAlgebra 𝓞 R]

noncomputable def iL : Ak 𝓞 p R →ₐ[ZMod p] Bk 𝓞 p R := Algebra.TensorProduct.includeLeft

end Kappa
end S17L2c
end P2MW.S_Deformation_truncate_map_mem_wittHom_of_forall_coeff_ghostComponent_eq_logCovector
