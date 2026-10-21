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

namespace UniqueGames.Foundations.PCP.VerifierToCNF

open Target

theorem flatMap_pair_length {α β : Type*} (xs : List α) (f g : α → β) :
    (xs.flatMap (fun x => [f x, g x])).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil, ih]
    omega

end UniqueGames.Foundations.PCP.VerifierToCNF
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
