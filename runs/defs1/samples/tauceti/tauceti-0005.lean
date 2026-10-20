public section

open WeierstrassCurve.Affine

namespace TauCeti.Isogeny.Hom

variable {F : Type*} [Field F] {W₁ W₂ W₃ : WeierstrassCurve.Affine F}
  [W₁.IsElliptic] [W₂.IsElliptic]

section PointMap

variable [DecidableEq F]

/-- **The action of a morphism on points, as a homomorphism of point groups.** -/
noncomputable def pointMapHom (f : Hom W₁ W₂) : W₁.Point →+ W₂.Point :=
  AddMonoidHom.mk' f.pointMap (pointMap_add f)

end PointMap
end TauCeti.Isogeny.Hom
end
