public section

universe u

open CategoryTheory Module

namespace FGModuleCat

variable (R : Type u) [CommRing R]

variable {R}

/-- The transpose of a morphism of finitely generated projective modules. -/
def dualMap {M N : FGModuleCat.{u} R} [Module.Projective R M] [Module.Projective R N]
    (f : M ⟶ N) : dual R N ⟶ dual R M :=
  ofHom f.hom.hom.dualMap

end FGModuleCat
end
