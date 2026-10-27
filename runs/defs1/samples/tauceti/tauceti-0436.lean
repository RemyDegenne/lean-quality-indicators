public section

open Polynomial

namespace TauCeti

variable (R : Type*) [CommRing R]

namespace LevelThreeRing

section equivLocalization

variable {R}

/-- When `3` is invertible in `R`, the level-three ring is the localization `R[μ][(μ³ - 1)⁻¹]` of
the polynomial ring in `μ`. -/
noncomputable def equivLocalization (h3 : IsUnit (3 : R)) :
    LevelThreeRing R ≃ₐ[R] Localization.Away (X ^ 3 - 1 : R[X]) :=
  have hX : IsUnit (algebraMap R[X] (Localization.Away (X ^ 3 - 1 : R[X])) X ^ 3 - 1) := by
    have h := IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away (X ^ 3 - 1 : R[X])) (X ^ 3 - 1 : R[X])
    rwa [map_sub, map_pow, map_one] at h
  AlgEquiv.ofAlgHom (lift _ hX)
    (IsLocalization.Away.liftAlgHom (X ^ 3 - 1 : R[X]) (f := aeval (mu R))
      (by simpa using isUnit_mu_pow_three_sub_one R h3))
    (AlgHom.toRingHom_injective <| IsLocalization.ringHom_ext (.powers (X ^ 3 - 1 : R[X])) <|
      Polynomial.ringHom_ext
        (fun r ↦ by
          simp [IsScalarTower.algebraMap_apply R R[X] (Localization.Away (X ^ 3 - 1 : R[X]))])
        (by simp))
    (algHom_ext (by simpa using isUnit_mu_pow_three_sub_one R h3) (by simp))

end equivLocalization
end LevelThreeRing
end TauCeti
end
