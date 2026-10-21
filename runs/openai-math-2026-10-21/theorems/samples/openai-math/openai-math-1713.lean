namespace OAI

namespace MaxCutGames.Foundations.Complexity.PoweringMachineInitialize

open Turing

open PoweringMachineLoop PoweringMasterState

@[simp] theorem final_vertices (max B vertices : Nat) (extra : ExtraTape max → List Bool) :
    mergeTapes (finalTapes B vertices []) extra (.inl .vertices) = encodeWord vertices := rfl

end MaxCutGames.Foundations.Complexity.PoweringMachineInitialize
end OAI
