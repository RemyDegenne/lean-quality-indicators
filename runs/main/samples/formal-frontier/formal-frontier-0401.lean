@[expose] public section

open CategoryTheory

open scoped TensorProduct CategoryTheory.Prod

universe uR uC uM

namespace TopModuleCat

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

@[simp]
theorem tensorBifunctor_uncurry_map_hom
    {C D : ModuleCat.{uC} R} {M N : TopModuleCat.{uM} R}
    (f : C ⟶ D) (g : M ⟶ N) :
    ((Functor.uncurry.obj (tensorBifunctor R)).map (f ×ₘ g)).hom =
      tensorMapBilinear R C D M N f.hom g.hom := by
  dsimp only [Functor.uncurry, tensorBifunctor, tensorLeftFunctor, coefficientTensor]
  change (tensorMapCLM R (C := D) (D := D) (M := M) (N := N)
      (LinearMap.id : D →ₗ[R] D) g.hom).comp
    (tensorMapCLM R (C := C) (D := D) (M := M) (N := M)
      f.hom (ContinuousLinearMap.id R M)) =
    tensorMapBilinear R C D M N f.hom g.hom
  rw [tensorMapBilinear_apply]
  simpa only [LinearMap.id_comp, ContinuousLinearMap.comp_id] using
    (tensorMapCLM_comp R (C := C) (D := D) (E := D)
      (M := M) (N := M) (P := N) f.hom (LinearMap.id : D →ₗ[R] D)
      (ContinuousLinearMap.id R M) g.hom).symm

end TopModuleCat
end
