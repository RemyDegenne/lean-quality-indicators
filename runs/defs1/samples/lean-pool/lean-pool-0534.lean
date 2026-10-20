@[expose] public section

open scoped ContDiff Manifold

open Set Filter Topology

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

variable {U V : Set X} {x : X} {c : ℂ}

namespace MeroGermOn

variable [IsManifold 𝓘(ℂ) ω X]

/-- CC3's `holoRepr` (D5): the canonical repaired representative. -/
noncomputable def holoRepr (φ : MeroGermOn X U) : X → ℂ := fun x => φ.evalAt x

end MeroGermOn
end RS
end
