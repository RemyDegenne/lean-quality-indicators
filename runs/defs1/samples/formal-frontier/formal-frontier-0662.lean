@[expose] public section

open CategoryTheory

open scoped TensorProduct

universe uR w uC uM

namespace TopModuleCat

/-- Tensor algebraic coefficients with a fixed topological right module. -/
noncomputable def coefficientTensor
    (R : Type uR) [CommRing R] [TopologicalSpace R]
    (M : TopModuleCat.{uM} R) :
    ModuleCat.{uC} R ⥤ TopModuleCat.{max uC uM} R where
  obj C := tensorLeftObj R C M
  map {C D} a := CategoryTheory.ConcreteCategory.ofHom
    (C := TopModuleCat.{max uC uM} R)
    (X := tensorLeftObj R C M) (Y := tensorLeftObj R D M)
    (tensorMapCLM R a.hom (ContinuousLinearMap.id R M))
  map_id C := ConcreteCategory.ext
    ((CategoryTheory.ConcreteCategory.hom_ofHom
      (C := TopModuleCat.{max uC uM} R)
      (X := tensorLeftObj R C M) (Y := tensorLeftObj R C M)
      (tensorMapCLM R
        (ModuleCat.Hom.hom (R := R) (A := C) (B := C) (𝟙 C))
        (ContinuousLinearMap.id R M))).trans
      ((congrArg (fun l => tensorMapCLM R l (ContinuousLinearMap.id R M))
        (ModuleCat.hom_id (M := C))).trans
        ((tensorMapCLM_id R (C := C) (M := M)).trans
          (TopModuleCat.hom_id R (tensorLeftObj R C M)).symm)))
  map_comp {C D E} a b := ConcreteCategory.ext
    ((CategoryTheory.ConcreteCategory.hom_ofHom
      (C := TopModuleCat.{max uC uM} R)
      (X := tensorLeftObj R C M) (Y := tensorLeftObj R E M)
      (tensorMapCLM R (a ≫ b).hom (ContinuousLinearMap.id R M))).trans
      ((congrArg (fun l => tensorMapCLM R l (ContinuousLinearMap.id R M))
        (ModuleCat.hom_comp a b)).trans
        (((congrArg (tensorMapCLM R (b.hom.comp a.hom))
          (ContinuousLinearMap.id_comp (ContinuousLinearMap.id R M))).symm.trans
          (tensorMapCLM_comp R a.hom b.hom
            (ContinuousLinearMap.id R M) (ContinuousLinearMap.id R M))).trans
          ((congrArg₂ (fun v u => v.comp u)
            (CategoryTheory.ConcreteCategory.hom_ofHom
              (C := TopModuleCat.{max uC uM} R)
              (X := tensorLeftObj R D M) (Y := tensorLeftObj R E M)
              (tensorMapCLM R b.hom (ContinuousLinearMap.id R M))).symm
            (CategoryTheory.ConcreteCategory.hom_ofHom
              (C := TopModuleCat.{max uC uM} R)
              (X := tensorLeftObj R C M) (Y := tensorLeftObj R D M)
              (tensorMapCLM R a.hom (ContinuousLinearMap.id R M))).symm).trans
            (TopModuleCat.hom_comp R
              (CategoryTheory.ConcreteCategory.ofHom
                (C := TopModuleCat.{max uC uM} R)
                (X := tensorLeftObj R C M) (Y := tensorLeftObj R D M)
                (tensorMapCLM R a.hom (ContinuousLinearMap.id R M)))
              (CategoryTheory.ConcreteCategory.ofHom
                (C := TopModuleCat.{max uC uM} R)
                (X := tensorLeftObj R D M) (Y := tensorLeftObj R E M)
                (tensorMapCLM R b.hom (ContinuousLinearMap.id R M)))).symm))))

end TopModuleCat
end
