namespace OAI

noncomputable section

namespace CuntzPureness

open CuntzTrace OrderedSemigroup

open scoped NNReal ENNReal ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]

theorem regularizedStateTwoQuasitrace_unit_pos (hsimple : TopologicallySimple A)
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y) :
    0 < (regularizedStateTwoQuasitrace hsimple y hy f).base 1 := by
  rw [regularizedStateTwoQuasitrace,finiteSpectralTwoQuasitrace_unit]
  apply Complex.zero_lt_real.mpr
  exact ENNReal.toReal_pos (finiteState_regularized_unit hsimple y hy f).1.ne'
    (finiteState_regularized_unit hsimple y hy f).2

end CuntzPureness
end
end OAI
