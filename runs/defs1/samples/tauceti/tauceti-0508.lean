public section

open CategoryTheory

namespace TauCeti

universe u v w

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

attribute [local instance 10000] Classical.decRel

variable (R : Type v) [CommRing R] [TopologicalSpace R]
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (U : OpenSubgroup G)
  (A : SmoothDiscreteTopRep.{v, u, max u v w} R U.toSubgroup)

local instance : U.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient

variable {A}
  {B : SmoothDiscreteTopRep.{v, u, max u v w} R U.toSubgroup}

/-- The morphism on smooth discrete induced representations induced by a coefficient
morphism, on the same underlying module as Mathlib's `Rep.indMap`. -/
noncomputable def algebraicIndMap (f : A ⟶ B) :
    algebraicIndAsSmooth.{u, v, w} R G U A ⟶ algebraicIndAsSmooth.{u, v, w} R G U B := by
  letI := (algebraicIndDiscreteRep.{u, v, w} R G U A).topologicalSpace
  letI := (algebraicIndDiscreteRep.{u, v, w} R G U B).topologicalSpace
  letI := (algebraicIndDiscreteRep.{u, v, w} R G U A).discreteTopology
  letI := (algebraicIndDiscreteRep.{u, v, w} R G U B).discreteTopology
  letI := (algebraicIndDiscreteRep.{u, v, w} R G U A).continuousSMulRing
  letI := (algebraicIndDiscreteRep.{u, v, w} R G U B).continuousSMulRing
  exact ObjectProperty.homMk (TopRep.ofHom
    { toContinuousLinearMap :=
        ⟨(Rep.indMap U.toSubgroup.subtype (coefficientMap.{u, v, w} R G U f)).hom.toLinearMap,
          continuous_of_discreteTopology⟩
      isIntertwining' := fun g ↦ by
        apply ContinuousLinearMap.ext
        intro x
        -- The dictionary keeps the underlying carrier and action; identify its action
        -- with the discrete representation before using the native induction equation.
        change (Rep.indMap U.toSubgroup.subtype (coefficientMap.{u, v, w} R G U f)).hom
          ((algebraicIndDiscreteRep.{u, v, w} R G U A).ρ g x) =
            (algebraicIndDiscreteRep.{u, v, w} R G U B).ρ g
              ((Rep.indMap U.toSubgroup.subtype (coefficientMap.{u, v, w} R G U f)).hom x)
        rw [algebraicIndDiscreteRep_ρ, algebraicIndDiscreteRep_ρ]
        exact Rep.hom_comm_apply (Rep.indMap U.toSubgroup.subtype
          (coefficientMap.{u, v, w} R G U f)) g x })

end TauCeti
end
