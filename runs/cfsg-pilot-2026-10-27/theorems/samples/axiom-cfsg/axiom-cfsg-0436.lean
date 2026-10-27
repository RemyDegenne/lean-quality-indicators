public section

namespace CFSG.SeitzReduction.E7Pilot

open Matrix QuadraticMap

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

open CFSG.ComponentClassification.CatalogueBHigherLinearField

open CFSG.RankThree.PartOne.KCOrthogonalSubfield

open CFSG.Quasithin (perfectCore)

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

open scoped commutatorElement

section Form

variable {K : Type} [Field K] (n : ℕ)

theorem isExtension_coordinateQuadPlus (k : Subfield K) :
    IsExtension k (coordinateQuadPlus n k) (coordinateQuadPlus n K) := by
  intro v
  rw [coordinateQuadPlus_apply, coordinateQuadPlus_apply]
  simp [vecIncl]

end Form
end CFSG.SeitzReduction.E7Pilot
end
