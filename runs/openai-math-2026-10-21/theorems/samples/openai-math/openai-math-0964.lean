namespace OAI

namespace MinUncutGames.Foundations.PCP.RawInitialMachinePhases

open Turing Complexity RawInitialMachineModel

theorem loadSigns_step (base : Tape → List Bool) (a b c : Bool)
    (ha : base (.field 1) = encodeWord (if a then 1 else 0))
    (hb : base (.field 3) = encodeWord (if b then 1 else 0))
    (hc : base (.field 5) = encodeWord (if c then 1 else 0)) (state : State) :
    (TM2.step program) ⟨some .loadSigns, state, base⟩ =
      some ⟨some (.scan (.tailVariables 0)), ((a, b, c), none), base⟩ := by
  change some (TM2.stepAux (program .loadSigns) state base) = _
  simp only [program, TM2.stepAux, ha, hb, hc, bitWord_head, Option.getD_some]

end MinUncutGames.Foundations.PCP.RawInitialMachinePhases
end OAI
