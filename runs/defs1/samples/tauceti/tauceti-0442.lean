public section

namespace TauCeti.Toric

/-- The standard fan of the affine line consists of the faces of the positive ray. -/
abbrev affineRayFan : Fan ((Int.castAddHom ℝ).compLeft (Fin 1)) :=
  Fan.ofCone (isIntegralLattice_intCast 1) isRegularCone_affineRayCone.toIsToricCone

end TauCeti.Toric
end
