namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic973 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm973 x = (4404201698619555840000 : ℝ) * Sparse.eval nodeValue2603 x := by
  norm_num [reducedTerm973, nodeValue2603, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics
end OAI
