public section

namespace TauCeti.IntegralLattice

universe u v

variable {V : Type u} {W : Type v}

variable [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

@[simp]
theorem discriminantQuadraticIsometryNeg_toFiniteBilinearModule
    (L : IntegralLattice V) [L.IsNondegenerate] (hL : L.IsEven) :
    (L.discriminantQuadraticIsometryNeg hL).toFiniteBilinearModule =
      L.discriminantBilinearIsometryNeg := by
  apply FiniteBilinearModule.Isometry.toAddEquiv_injective
  rw [FiniteQuadraticModule.Isometry.toFiniteBilinearModule_toAddEquiv,
    discriminantQuadraticIsometryNeg_toAddEquiv,
    discriminantBilinearIsometryNeg_toAddEquiv]

end TauCeti.IntegralLattice
end
