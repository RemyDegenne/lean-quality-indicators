public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

open scoped ModuleCat

universe v w

variable (k : Type (max v w)) (Q : Type v) [Field k] [Quiver.{w} Q] [Finite Q]

variable {Q}

/-- The first differential of the module resolution, expressed between the direct sum of
vertex projective modules and the vertex projective module. -/
noncomputable def arrowSumToIndecProjModule (i : Q)
    [Finite ((j : Q) × (i ⟶ j))] :
    (⨁ fun a : (j : Q) × (i ⟶ j) ↦ indecProjModule k Q a.1) ⟶
      indecProjModule k Q i :=
  (vertexSimpleModuleResolutionX₁Iso k i).inv ≫
    (quiverRepFunctor k Q).inv.map (arrowSumToIndecProjRep k i) ≫
      (vertexSimpleModuleResolutionX₂Iso k i).hom

end TauCeti
end
