public noncomputable section

open Set Filter Complex

open scoped Topology

namespace SeveralComplexVariables

variable {ι : Type*}

/-- The tube over a real coordinate set; imaginary coordinates are unrestricted. -/
@[expose] def tubeDomain (Ω : Set (ι → ℝ)) : Set (ι → ℂ) :=
  {z | (fun i => (z i).re) ∈ Ω}

end SeveralComplexVariables
end
