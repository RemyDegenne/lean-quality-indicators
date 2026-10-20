public section

open WeierstrassCurve.Affine

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

namespace Hom

@[simp]
theorem pullbackDifferential_id (W : WeierstrassCurve.Affine F) :
    (Hom.id W).pullbackDifferential = LinearMap.id := by
  rw [id_def, pullbackDifferential_ofIsogeny, Isogeny.pullbackDifferential_id]

end Hom
end TauCeti.Isogeny
end
