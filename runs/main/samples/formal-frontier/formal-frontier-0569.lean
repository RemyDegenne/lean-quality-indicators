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

@[reassoc]
lemma identityComponentι_comp_componentSchemeMap :
    Scheme.identityComponentι (Over.mk f) ≫ componentSchemeMap f =
      toUnit (Scheme.identityComponentOver (Over.mk f)) ≫
        η[(finiteConstantGroupScheme K (rationalComponentGroup f)).X] := by
  have h := connected_comp_componentSchemeMap f
    (Scheme.identityComponentOne (Over.mk f))
    (Scheme.identityComponentι (Over.mk f))
  rw [Scheme.identityComponentOne_comp_ι] at h
  have hη : (η[Over.mk f] : groupSchemePoints f) = 1 := rfl
  rw [hη] at h
  have hQ : (Quotient.mk'' (1 : groupSchemePoints f) : rationalComponentGroup f) =
      (One.one : rationalComponentGroup f) := rfl
  rw [hQ] at h
  have hOne : finiteConstantGroupSchemePoint K (rationalComponentGroup f) One.one =
      η[(finiteConstantGroupScheme K (rationalComponentGroup f)).X] := by
    change (finiteConstantGroupSchemePointHom K (rationalComponentGroup f)) One.one = _
    exact map_one _
  rw [hOne] at h
  exact h

end
end AlgebraicGeometry
end
