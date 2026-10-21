namespace OAI

section

noncomputable section

open Set Function

open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry

variable {A : Type*} [Group A] (W : WordGeometry A)

lemma projectedFunction_one (f : RegularHilbert A) (t : A) :
    W.projectedFunction f t 1=0 := by simp [projectedFunction]

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end
end OAI
