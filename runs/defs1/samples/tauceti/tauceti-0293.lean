public section

noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex

variable {C : Type*} [Category* C] {ι : Type*} {c : ComplexShape ι}

variable [Abelian C] (K : HomologicalComplex C c)

/-- The complex with the homology objects of `K` as terms and zero differentials. -/
@[expose, simps X]
def homologyComplex : HomologicalComplex C c where
  X i := K.homology i
  d _ _ := 0

end HomologicalComplex
end
end
