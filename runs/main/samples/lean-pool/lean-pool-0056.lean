@[expose] public section

open TauCeti.DavisKahan.Sylvester

open scoped InnerProductSpace

namespace TauCeti

namespace DavisKahan

universe u

section BilateralShift

variable {𝕜 : Type*} [RCLike 𝕜]

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

theorem bilateralShiftL_intertwines (b : HilbertBasis ℤ 𝕜 H) (k : ℤ) :
    bilateralShiftL b * Submodule.starProjection (coordinateHalfSpace b k) =
      Submodule.starProjection (coordinateHalfSpace b (k + 1)) * bilateralShiftL b := by
  ext y
  simp only [mul_apply_eq_comp]
  exact (starProjection_of_map_eq (bilateralShift b)
    (map_coordinateHalfSpace b k) y).symm

end BilateralShift
end DavisKahan
end TauCeti
end
