@[expose] public section

variable (K : Type*) [Field K]

namespace NumberField.mixedEmbedding

open NumberField NumberField.InfinitePlace

noncomputable section

open NumberField.Units NumberField.Units.dirichletUnitTheorem

variable [NumberField K]

namespace fundamentalCone

variable {K} {x y : mixedSpace K} {c : ℝ}

variable (K) in
/-- The intersection between the fundamental cone and the `integerLattice`. -/
def integerSet : Set (mixedSpace K) :=
  fundamentalCone K ∩ mixedEmbedding.integerLattice K

end fundamentalCone
end
end NumberField.mixedEmbedding
end
