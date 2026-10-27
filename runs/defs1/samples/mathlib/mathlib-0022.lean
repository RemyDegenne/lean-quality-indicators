@[expose] public section

open NNReal Filter Set

open scoped Topology Uniformity

noncomputable section

variable (α β : Type*) [PseudoMetricSpace α] [PseudoMetricSpace β]

section LipschitzMul

/-- Class `LipschitzAdd M` says that the addition `(+) : X × X → X` is Lipschitz jointly in
the two arguments. -/
class LipschitzAdd [AddMonoid β] : Prop where
  lipschitz_add : ∃ C, LipschitzWith C fun p : β × β => p.1 + p.2

end LipschitzMul
end
end
