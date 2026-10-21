namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.WeightedPortMoore

open SimpleGraph WeightedMoore PortSubdivision WeightedCycles

variable {V D : Type*} (Γ : PortGraph V D)

@[simp] theorem edgeWeight_spoke (len : D → ℝ) (v : V) (d : D) :
    edgeWeight len s(Sum.inl v,Sum.inr d) = 0 := rfl

end TorsionFreeZeroDivisors.WeightedPortMoore
end
end OAI
