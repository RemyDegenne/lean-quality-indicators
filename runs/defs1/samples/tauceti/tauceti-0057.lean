public section

noncomputable section

open CategoryTheory Limits Opposite

universe w v u

namespace TauCeti

namespace TopPair

variable {ι : Type w} (P : ι → TopPair.{w})
  (C : Type u) [Category.{v} C] [Small.{v} ι] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C)

/-- **Additivity of relative singular cohomology.** In every degree the relative cohomology
of a disjoint union of pairs is the product of the relative cohomologies of the pairs. The
projections are induced by the inclusions of the pairs. -/
def isLimitFanSingularCohomology (n : ℕ) :
    IsLimit (Fan.mk ((TopPair.sigma P).singularCohomology R k M n)
      (fun i ↦ TopPair.singularCohomologyMap (TopPair.sigmaι P i) n) :
      Fan fun i ↦ (P i).singularCohomology R k M n) := by
  have : HasLimitsOfShape (Discrete ι) (ModuleCat.{v} k) := ModuleCat.hasLimitsOfShape
  exact isLimitFanMkObjOfIsLimit (HomologicalComplex.homologyFunctor
    (ModuleCat.{v} k) (ComplexShape.up ℕ) n) _ _
      (isLimitFanSingularCochainComplex P C R k M)

end TopPair
end TauCeti
end
end
