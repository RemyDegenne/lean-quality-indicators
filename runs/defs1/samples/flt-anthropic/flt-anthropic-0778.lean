namespace P2MW.S_ModularCurve_UVCrossingModel_exists_mem_fixedSubring_eq_add_mul_U

universe u

noncomputable section

namespace ModularCurve

p2m_open

namespace SymmetricTwoVars

noncomputable section

open MvPowerSeries

variable {W : Type u} [CommRing W]

def newtonAssembled (f : MvPowerSeries (Fin 2) W) : MvPowerSeries (Fin 2) W :=
  fun d => coeff (pairIdx (d 0) 0) (newton f (d 1))

end
end SymmetricTwoVars
end ModularCurve
end
end P2MW.S_ModularCurve_UVCrossingModel_exists_mem_fixedSubring_eq_add_mul_U
