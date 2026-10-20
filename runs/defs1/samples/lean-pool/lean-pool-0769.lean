@[expose] public section

namespace BKAR

open scoped BigOperators

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

/-- The `i`th level, in increasing order. -/
def interpolationLevel (F : Forest V) (u : F.EdgeParam → ℝ)
    (i : Fin (F.interpolationLevels u).card) : ℝ :=
  (F.interpolationLevels u).orderEmbOfFin rfl i

end
end Forest
end BKAR
end
