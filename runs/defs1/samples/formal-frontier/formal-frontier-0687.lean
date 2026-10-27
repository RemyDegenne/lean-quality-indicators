@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.PartialMap

variable {X Y S : Scheme.{u}}

/-- Glue two partial maps whose morphisms agree on the intersection of their domains.

This is `glueHom` applied to the second partial map's domain and morphism. -/
noncomputable def glue (p q : X.PartialMap Y)
    (h : X.homOfLE (inf_le_left : p.domain ⊓ q.domain ≤ p.domain) ≫ p.hom =
      X.homOfLE (inf_le_right : p.domain ⊓ q.domain ≤ q.domain) ≫ q.hom) :
    X.PartialMap Y :=
  p.glueHom q.domain q.hom h

end AlgebraicGeometry.Scheme.PartialMap
end
