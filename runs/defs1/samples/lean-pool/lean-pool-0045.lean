@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory

open scoped ContDiff Topology BigOperators

namespace NavierStokes.GlobalSlowProfiles

/-- A single coherent infinite sequence, constructed by well-founded
recursion; all coefficient indices used in the radial source are smaller. -/
noncomputable def sequence {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ) :
    Admissible s n := Nat.lt_wfRel.wf.fix (recursionStep s) n

end NavierStokes.GlobalSlowProfiles
end
end
