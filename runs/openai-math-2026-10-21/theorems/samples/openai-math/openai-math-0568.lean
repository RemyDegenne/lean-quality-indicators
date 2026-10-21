namespace OAI

section

open MeasureTheory Filter Set

open scoped ENNReal NNReal Topology BigOperators Classical ContDiff

noncomputable section

namespace Coulomb

lemma regularizedU_pos {l e:ℝ} (he:0<e) (x:Space):0<regularizedU l e x :=
  add_pos_of_nonneg_of_pos (Real.rpow_nonneg (by positivity) _) he

end Coulomb
end
end
end OAI
