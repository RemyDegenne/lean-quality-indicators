open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

open TopologicalSpace

open scoped CategoryTheory.MonObj

public section

universe u

namespace AlgebraicGeometry

section

variable {K : Type u} [Field K] [IsAlgClosed K] {G : Scheme.{u}}

variable (f : G ⟶ Spec (.of K)) [GrpObj (Over.mk f)] [LocallyConnectedSpace G]

local instance componentMapOverMkLocallyConnected : LocallyConnectedSpace (Over.mk f).left :=
  inferInstanceAs (LocallyConnectedSpace G)

variable [ConnectedSpace ((Scheme.identityComponentOver (Over.mk f) ⊗
  Scheme.identityComponentOver (Over.mk f)).left)]

variable [GeometricallyConnected (Scheme.identityComponentOver (Over.mk f)).hom]

variable [LocallyOfFiniteType f] [QuasiCompact f]

noncomputable local instance componentMapFintype :
    Fintype (rationalComponentGroup f) := Fintype.ofFinite _

/-- Translation promotes the component isomorphism to one over the base. -/
noncomputable def identityComponentOverIsoConnectedComponentOver
    (a : groupSchemePoints f) :
    Scheme.identityComponentOver (Over.mk f) ≅ connectedComponentOpenOver f a := by
  refine Over.isoMk ?_ ?_
  · change (Scheme.identityComponentOver (Over.mk f)).left ≅
      (G.connectedComponentOpen (groupSchemePointComponent f a)).toScheme
    exact identityComponentIsoConnectedComponent f a
  · change (identityComponentIsoConnectedComponent f a).hom ≫
      ((G.connectedComponentOpen (groupSchemePointComponent f a)).ι ≫ f) =
        (Scheme.identityComponentOver (Over.mk f)).hom
    rw [← Category.assoc, identityComponentIsoConnectedComponent_hom_ι]
    rw [Category.assoc]
    change (Scheme.identityComponentι (Over.mk f)).left ≫
      ((CategoryTheory.GrpObj.mulLeft a).hom.left ≫ f) = _
    have hmul : (CategoryTheory.GrpObj.mulLeft a).hom.left ≫ f = f := by
      change (CategoryTheory.GrpObj.mulLeft a).hom.left ≫
        (Over.mk f).hom = (Over.mk f).hom
      exact (CategoryTheory.GrpObj.mulLeft a).hom.w
    rw [hmul]
    rfl

end
end AlgebraicGeometry
end
