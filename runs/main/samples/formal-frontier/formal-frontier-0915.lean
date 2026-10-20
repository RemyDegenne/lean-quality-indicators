@[expose] public section

open CategoryTheory

open scoped TensorProduct

universe uR w uC uM

namespace TopModuleCat

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

theorem coefficientTensorHomEquiv_symm_apply (M : TopModuleCat.{w} R)
    {C : ModuleCat.{w} R} {N : TopModuleCat.{w} R}
    (b : C ⟶ ((CategoryTheory.linearCoyoneda R (TopModuleCat.{w} R)).obj
      (Opposite.op M)).obj N) :
    (coefficientTensorHomEquiv R M C N).symm b =
      TopModuleCat.ofHom (tensorLiftCLM R
        ((homLinearEquiv R (X := M) (Y := N)).toLinearMap.comp b.hom)) := by
  apply ConcreteCategory.ext
  exact congrArg (tensorLiftCLM R) (LinearMap.ext (fun c => rfl))

end TopModuleCat
end
