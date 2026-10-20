@[expose] public section

namespace Distributed2Coloring

open MeasureTheory

open scoped unitInterval

namespace ClassicalAlgorithm

lemma measurable_fstTriple :
    Measurable (fun x : Samples 4 => (x 0, x 1, x 2) : Samples 4 → Rand × Rand × Rand) := by
  simpa using
    (measurable_pi_apply 0).prodMk ((measurable_pi_apply 1).prodMk (measurable_pi_apply 2))

end ClassicalAlgorithm
end Distributed2Coloring
end
