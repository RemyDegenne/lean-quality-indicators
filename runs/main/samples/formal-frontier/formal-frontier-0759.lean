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

omit [IsAlgClosed K]
    [GeometricallyConnected (Scheme.identityComponentOver (Over.mk f)).hom]
    [LocallyOfFiniteType f] [QuasiCompact f] in
lemma componentProductOpen_connectedSpace (p : groupSchemePoints f ×
    groupSchemePoints f) :
    ConnectedSpace (connectedComponentOpenOver f p.1 ⊗
      connectedComponentOpenOver f p.2).left := by
  let e := identityComponentOverIsoConnectedComponentOver f p.1 ⊗ᵢ
    identityComponentOverIsoConnectedComponentOver f p.2
  exact ((Over.forget (Spec (.of K))).mapIso e).schemeIsoToHomeo.connectedSpace_iff.mp
    (inferInstance : ConnectedSpace
      (Scheme.identityComponentOver (Over.mk f) ⊗
        Scheme.identityComponentOver (Over.mk f)).left)

end
end AlgebraicGeometry
end
