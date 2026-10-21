namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable

open Turing MachineComposition

open UniqueGamesTheorem.Foundations.PCP

namespace Top

@[simp] theorem update_frame_global (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) (replacement : List Bool) :
    Function.update (frame data header counters) (coreTape 1) replacement =
      frame { data with globalIndex := replacement } header counters := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j => cases j <;> rfl

end Top
end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable
end OAI
