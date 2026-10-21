namespace OAI

section

namespace BinaryMatching.StackCode

open Polynomial

namespace Poly

variable {α β : Type} [Coding α] [Coding β]

@[fun_prop] theorem listTail : Poly (List.tail : List α → List α) := by
  exact listCases [] Prod.snd (by fun_prop)

end Poly
end BinaryMatching.StackCode
end
end OAI
