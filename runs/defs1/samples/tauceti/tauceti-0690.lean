public section

open CategoryTheory

universe u v w

noncomputable section

namespace PresheafOfModulesOfCommRing

variable {C : Type v} [Category.{w} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Auxiliary definition for `exteriorPower`: the exterior power of a presheaf of modules. -/
@[expose]
def exteriorPowerObj (M : PresheafOfModulesOfCommRing.{u} R) (n : ℕ) :
    PresheafOfModulesOfCommRing.{u} R :=
  PresheafOfModulesOfCommRing.mk (fun X ↦ (M.obj X).exteriorPower n)
    (fun f ↦ exteriorPowerObjMap M n f)
    (fun X ↦ ModuleCat.exteriorPower.hom_ext (by
      ext x
      simp only [ModuleCat.AlternatingMap.postcomp_apply, exteriorPowerObjMap_mk,
        PresheafOfModules.map_id, ModuleCat.restrictScalarsId'_inv_app,
        ModuleCat.restrictScalarsId'App_inv_apply]
      rfl))
    (fun {_ _ Z} f g ↦ ModuleCat.exteriorPower.hom_ext (by
      ext x
      refine (exteriorPowerObjMap_mk M n (f ≫ g) x).trans ?_
      -- the restriction-of-scalars comparison maps on the right are identities on elements
      exact (congrArg (ModuleCat.exteriorPower.mk (M := M.obj Z) (n := n))
        (funext fun j ↦ M.map_comp_apply f g (x j))).trans
          ((congrArg (exteriorPowerObjMap M n g) (exteriorPowerObjMap_mk M n f x)).trans
            (exteriorPowerObjMap_mk M n g _)).symm))

end PresheafOfModulesOfCommRing
end
end
