public section

open DirectSum MulOpposite

namespace TauCeti

universe uR uA uB uM uN

namespace DGRightModule

namespace InternalHom

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A] {𝒜 : ℤ → Submodule R A}
  {B : Type uB} {M : Type uM} {N : Type uN} [Ring B] [Algebra R B]
  [AddCommGroup M] [Module R M] [Module Bᵐᵒᵖ M] [IsScalarTower R Bᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module Bᵐᵒᵖ N] [IsScalarTower R Bᵐᵒᵖ N]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  {𝒩 : ℤ → Submodule R N} [DirectSum.Decomposition 𝒩]

/-- The underlying right-module map, as an `R`-linear map out of the internal Hom. -/
def coeLM : InternalHom 𝒜 B ℳ 𝒩 →ₗ[R] M →ₗ[Bᵐᵒᵖ] N where
  toFun f := f.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end InternalHom
end DGRightModule
end TauCeti
end
