public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.PartialMap

variable {X Y S : Scheme.{u}} [IsIntegral X]

variable (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY] (p : X.PartialMap Y)

variable (hp : p.hom ≫ sY = p.domain.ι ≫ sX)

variable (x : X) [ValuationRing (X.presheaf.stalk x)]

theorem mem_domain_extensionOfValuationRingStalk :
    x ∈ (extensionOfValuationRingStalk sX sY p hp x).domain :=
  (exists_extension_of_valuationRing_stalk_aux sX sY p hp x).choose_spec.1

end AlgebraicGeometry.Scheme.PartialMap
end
