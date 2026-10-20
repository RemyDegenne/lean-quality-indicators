@[expose] public section

noncomputable section

open Bundle Set Topology

variable (R : Type*) {B : Type*} (F : Type*) (E : B → Type*)

section

open Bundle

variable [NontriviallyNormedField R] [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)]
  [NormedAddCommGroup F] [NormedSpace R F] [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle F E]

variable {F E}

variable (B F)

namespace VectorBundleCore

variable {R B F} {ι : Type*}

variable (Z : VectorBundleCore R B F ι)

/-- The base space of a vector bundle core, as a convenience function for dot notation -/
@[nolint unusedArguments, reducible]
def Base := B

end VectorBundleCore
end
end
end
