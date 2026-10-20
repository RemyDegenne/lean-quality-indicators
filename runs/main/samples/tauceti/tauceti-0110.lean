public section

namespace AlgebraicGeometry.Scheme.Hom

open CategoryTheory

universe u

variable {Y Y' J : Scheme.{u}} (f : Y ⟶ J) [QuasiCompact f] [QuasiSeparated f]
  (g : Y' ⟶ J) [QuasiCompact g] [QuasiSeparated g]

@[reassoc (attr := simp)]
theorem normalizationMap_fromNormalization (φ : Y ⟶ Y') (hφ : φ ≫ g = f) :
    f.normalizationMap g φ hφ ≫ g.fromNormalization = f.fromNormalization := by
  simp [normalizationMap]

end AlgebraicGeometry.Scheme.Hom
end
