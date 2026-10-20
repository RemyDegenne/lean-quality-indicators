namespace P2MW.S_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.TwoGluedCurves Opposite TopologicalSpace

noncomputable section

namespace TwoGluedCurvesSubsheafAux

variable {Y : Scheme.{u}} {P₁ P₂ : Y.Modules}

variable {S : ∀ W : Y.Opens, Set (Γ(P₁, W) × Γ(P₂, W))} (hS : IsLocalSubmoduleFamily P₁ P₂ S)

scoped instance (W : (Y.Opens)ᵒᵖ) : Module (Y.ringCatSheaf.obj.obj W) ((subPresheaf hS).obj W) :=
  inferInstanceAs (Module Γ(Y, W.unop) (subMod hS W.unop))

def fstPresheafHom : (subModule hS).presheaf ⟶ P₁.presheaf where
  app W := AddCommGrpCat.ofHom
    { toFun := fun p : subMod hS W.unop => p.1.1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  naturality W W' i := by ext p; rfl

end TwoGluedCurvesSubsheafAux
end
end P2MW.S_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn
