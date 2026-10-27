public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace Bal209F4Aux

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

open scoped commutatorElement

section Glue

variable {X : Type} [Group X]

theorem mem_pairSub {x y : X} {hxy : Commute x y} {g : X} :
    g ∈ pairSub hxy ↔ ∃ i j : ℤ, g = x ^ i * y ^ j := Iff.rfl

end Glue
end Bal209F4Aux
end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
end
