public section

namespace CFSG.OddStandard.Harada75

open Subgroup CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

open scoped commutatorElement Pointwise

theorem unitriGL_mul_ne :
    unitriGL 1 0 0 * unitriGL 0 0 1 ≠ unitriGL 0 0 1 * unitriGL 1 0 0 := by
  intro h
  have h' := congrArg (fun g : GL (Fin 3) (ZMod 2) => (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) h
  revert h'
  decide

end CFSG.OddStandard.Harada75
end
