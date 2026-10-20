public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

open TopologicalSpace

open scoped CategoryTheory.MonObj

noncomputable section

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {G : Scheme.{u}}

section IdentityComponent

variable (f : G ⟶ Spec (.of K)) [GrpObj (Over.mk f)] [LocallyConnectedSpace G]

local instance overMkLocallyConnected : LocallyConnectedSpace (Over.mk f).left :=
  inferInstanceAs (LocallyConnectedSpace G)

variable [ConnectedSpace ((Scheme.identityComponentOver (Over.mk f) ⊗
  Scheme.identityComponentOver (Over.mk f)).left)]

/-- The subgroup of rational points induced from the identity-component
subgroup scheme. -/
abbrev identityComponentPointSubgroup : Subgroup (groupSchemePoints f) :=
  (IsMonHom.monoidHom (Scheme.identityComponentι (Over.mk f))
    (𝟙_ (Over (Spec (.of K))))).range

end IdentityComponent
end AlgebraicGeometry
end
end
