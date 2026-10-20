public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

theorem isSchemeTheoreticallyDominant_iff_appTop_injective (f : X ⟶ Y) [IsAffine Y] :
    IsSchemeTheoreticallyDominant f ↔ Function.Injective f.appTop := by
  -- an ideal sheaf on an affine scheme is trivial exactly when its ideal of global sections is
  rw [isSchemeTheoreticallyDominant_iff, Scheme.ker_of_isAffine,
    ← Scheme.IdealSheafData.equivOfIsAffine_symm_apply, map_eq_bot_iff,
    RingHom.injective_iff_ker_eq_bot]

end AlgebraicGeometry
end
end
