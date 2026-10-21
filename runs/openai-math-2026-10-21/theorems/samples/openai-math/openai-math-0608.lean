namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily

open Turing MachineComposition

open MachineCloudPadding

theorem familyView_left (t : NativeTape) : familyView (familyTape t) = some t := by
  by_cases hi : t = inputNative
  · subst t; simp [familyTape, familyView]
  · by_cases ho : t = outputNative
    · subst t; simp [familyTape, familyView, hi]
    · simp [familyTape, familyView, hi, ho]

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily
end OAI
