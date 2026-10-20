public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

open TopologicalSpace

universe v w

namespace AlgebraicGeometry

universe u

noncomputable section

variable {K : Type u} [Field K] [IsAlgClosed K] {G : Scheme.{u}}

variable (f : G ⟶ Spec (.of K)) [GrpObj (Over.mk f)] [LocallyConnectedSpace G]

local instance : LocallyConnectedSpace (Over.mk f).left :=
  inferInstanceAs (LocallyConnectedSpace G)

theorem reducedIdentityComponent_topologicalKrullDim
    [LocallyOfFiniteType f]
    [IsReduced ((Scheme.reductionOver (Over.mk f) ⊗
      Scheme.reductionOver (Over.mk f)).left)] :
    topologicalKrullDim
        (Scheme.reducedIdentityComponentOver (Over.mk f)).left =
      topologicalKrullDim G := by
  let _ : IsClosedImmersion (Scheme.reductionι.app G) := by
    change IsClosedImmersion G.nilradical.subschemeι
    infer_instance
  let _ : LocallyOfFiniteType (Scheme.reductionOver (Over.mk f)).hom := by
    change LocallyOfFiniteType (Scheme.reductionι.app G ≫ f)
    infer_instance
  let _ : GrpObj (Over.mk (Scheme.reductionOver (Over.mk f)).hom) :=
    inferInstanceAs (GrpObj (Scheme.reductionOver (Over.mk f)))
  let _ : LocallyConnectedSpace (Over.mk
      (Scheme.reductionOver (Over.mk f)).hom).left :=
    inferInstanceAs (LocallyConnectedSpace
      (Scheme.reductionOver (Over.mk f)).left)
  calc
    topologicalKrullDim
        (Scheme.reducedIdentityComponentOver (Over.mk f)).left =
        topologicalKrullDim (Scheme.reductionOver (Over.mk f)).left :=
      identityComponent_topologicalKrullDim
        (Scheme.reductionOver (Over.mk f)).hom
    _ = topologicalKrullDim G := Scheme.reduction_topologicalKrullDim G

end
end AlgebraicGeometry
end
