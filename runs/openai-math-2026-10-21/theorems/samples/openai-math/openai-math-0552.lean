namespace OAI

namespace Superstring.Computable

open BitCode

variable {α : Type} [Coded α]

variable [DecidableEq α] [Inhabited α]

@[fun_prop] theorem poly_downValue : Poly (fun q : List (List α) × List α => downValue q.1 q.2) := by
  unfold downValue
  fun_prop

end Superstring.Computable
end OAI
