@[expose] public section

open CategoryTheory

open scoped TensorProduct

universe uR w uC uM

namespace TopModuleCat

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

theorem coefficientTensorHomEquiv_naturality_left
    (R : Type uR) [CommRing R] [TopologicalSpace R]
    (M : TopModuleCat.{w} R) {C D : ModuleCat.{w} R}
    {N : TopModuleCat.{w} R} (u : D ⟶ C)
    (f : (TopModuleCat.coefficientTensor R M).obj C ⟶ N) :
    TopModuleCat.coefficientTensorHomEquiv R M D N
        ((TopModuleCat.coefficientTensor R M).map u ≫ f) =
      u ≫ TopModuleCat.coefficientTensorHomEquiv R M C N f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply ConcreteCategory.ext
  apply ContinuousLinearMap.ext
  intro m
  change
    ((coefficientTensorHomEquiv R M D N
      ((coefficientTensor R M).map u ≫ f)).hom c).hom m =
    ((coefficientTensorHomEquiv R M C N f).hom (u.hom c)).hom m
  calc
    _ = ((coefficientTensor R M).map u ≫ f).hom (c ⊗ₜ[R] m) :=
      coefficientTensorHomEquiv_apply_apply R M _ c m
    _ = f.hom (((coefficientTensor R M).map u).hom (c ⊗ₜ[R] m)) :=
      CategoryTheory.comp_apply (C := TopModuleCat.{w} R)
        (X := (coefficientTensor R M).obj D)
        (Y := (coefficientTensor R M).obj C) (Z := N)
        ((coefficientTensor R M).map u) f (c ⊗ₜ[R] m)
    _ = f.hom (u.hom c ⊗ₜ[R] m) :=
      congrArg f.hom (coefficientTensor_map_tmul R M u c m)
    _ = _ := (coefficientTensorHomEquiv_apply_apply R M f (u.hom c) m).symm

end TopModuleCat
end
