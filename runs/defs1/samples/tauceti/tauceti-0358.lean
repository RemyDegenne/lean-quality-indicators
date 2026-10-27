public section

namespace TauCeti.Isogeny

open _root_.WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

namespace Hom

/-- The isogeny a nonzero element of the carrier comes from: it is unital, so its underlying
map promotes to a pullback, and pointedness is the carrier's own condition. -/
noncomputable def toIsogeny {h : Hom W₁ W₂} (hz : h ≠ 0) : Isogeny W₁ W₂ :=
  ⟨_, h.mapsInfinity_of_map_one
    (MulHomClass.map_one_of_exists_apply_ne_zero (by
      by_contra hall
      rw [not_exists] at hall
      refine hz (Hom.ext (NonUnitalAlgHom.ext fun x => ?_))
      rw [not_not.mp (hall x), toNonUnitalAlgHom_zero, NonUnitalAlgHom.zero_apply]))⟩

end Hom
end TauCeti.Isogeny
end
