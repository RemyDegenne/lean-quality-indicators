namespace OAI

section

namespace Erdos3

namespace BooleanCubeKernel

variable {X I : Type*} [Fintype X] [Fintype I]

theorem spatialWindow_neg (H : X → ℝ) (a : ℝ) (v : X → (Unit ⊕ I) → ℤ)
    (hv : v ∈ spatialWindow H a) : -v ∈ spatialWindow H a := by
  apply (mem_spatialWindow_iff H a (-v)).2
  intro x i
  change |((spatialStar (-(v x)) i : ℤ) : ℝ)| ≤ _
  rw [spatialStar_neg, Pi.neg_apply, Int.cast_neg, abs_neg]
  exact (mem_spatialWindow_iff H a v).1 hv x i

end BooleanCubeKernel
end Erdos3
end
end OAI
