namespace OAI

namespace Ostmann

open scoped Classical BigOperators

theorem scheduledFinalPerm_injective {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word}) :
    Function.Injective (scheduledFinalPerm role n m word) := by
  intro e f hef
  apply paritySlotPerm_injective
  apply Equiv.ext
  intro x
  have hx := congrArg (fun g => g (scheduledWordH role (n + 1)
    (parityPathValue x.1) (word x.2))) hef
  rw [scheduledFinalPerm_word, scheduledFinalPerm_word] at hx
  have he : (parityPathValue (paritySlotPerm e x).1, word (paritySlotPerm e x).2) =
      (parityPathValue (paritySlotPerm f x).1, word (paritySlotPerm f x).2) :=
    scheduledWordH_injective role (n + 1) hx
  exact Prod.ext (parityPathValue_injective n (congrArg Prod.fst he))
    (word.injective (congrArg Prod.snd he))

end Ostmann
end OAI
