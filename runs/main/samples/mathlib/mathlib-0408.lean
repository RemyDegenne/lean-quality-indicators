@[expose] public section

namespace NormedSpace

open Filter RCLike ContinuousMultilinearMap NormedField Asymptotics FormalMultilinearSeries

open scoped Nat Topology ENNReal Ring

section TopologicalAlgebra

variable (𝕂 𝔸 : Type*) [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸]

variable {𝕂 𝔸}

variable (𝕂)

theorem _root_.Commute.exp_left [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) :
    Commute (exp x) y :=
  h.symm.exp_right.symm

end TopologicalAlgebra
end NormedSpace
end
