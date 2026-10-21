namespace OAI

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

namespace DFVSGames.Foundations.Complexity.MachineRegularOwnerBody

open Turing MachineComposition PCP

open PreprocessingCloudIndex PreprocessingRegularTables

open MachineRegularTable PreprocessingRegularLoopWords

theorem vertexPlacement (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (n : Nat) (output output' fuel : List Bool) :
    MachineCloudPadding.Placement.tapes vertexView
      (MachineRegularOriginalBody.coreFrame (vertexData H t v n output'))
      (working (vertexData H t v n output) fuel []) =
      working (vertexData H t v n output') fuel [] := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => rfl
    | inr j => cases j with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr i => rfl

end DFVSGames.Foundations.Complexity.MachineRegularOwnerBody
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end OAI
