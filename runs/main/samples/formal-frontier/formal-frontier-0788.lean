@[expose] public section

open CategoryTheory

open scoped TensorProduct CategoryTheory.Prod

universe uR uC uM

namespace TopModuleCat

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

@[simp]
theorem tensorBifunctor_uncurry_map_tmul
    {C D : ModuleCat.{uC} R} {M N : TopModuleCat.{uM} R}
    (f : C ⟶ D) (g : M ⟶ N) (c : C) (m : M) :
    ((Functor.uncurry.obj (tensorBifunctor R)).map (f ×ₘ g)).hom
      (c ⊗ₜ[R] m) = f.hom c ⊗ₜ[R] g.hom m := by
  exact (tensorBifunctor_uncurry_map_apply R f g (c ⊗ₜ[R] m)).trans
    (TensorProduct.map_tmul f.hom g.hom.toLinearMap c m)

end TopModuleCat
end
