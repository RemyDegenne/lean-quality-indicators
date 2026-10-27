public section

open CategoryTheory MulOpposite

namespace TauCeti

universe uR uA uB uM uN

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}

namespace DGBimoduleCat

open DGRightModule

/-- The internal Hom out of a fixed DG bimodule, as a linear functor on DG right modules.
The carrier lives in the maximum of the bimodule and right-module universes. -/
-- Keep the object carrier reducible for evaluation of morphisms.
noncomputable abbrev internalHom (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) :
    DGRightModuleCat.{uR, uB, uN} hB ⥤ DGRightModuleCat.{uR, uA, max uM uN} hA where
  obj N := M.internalHomObj N
  map v := InternalHom.map (𝟙 M) v
  map_id N := InternalHom.map_id_id M N
  map_comp v v' := by
    simpa only [Category.id_comp] using (InternalHom.map_comp (𝟙 M) (𝟙 M) v v').symm

end DGBimoduleCat
end TauCeti
end
