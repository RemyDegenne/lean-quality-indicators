public section

open List (Vector)

open Encodable Denumerable Part

namespace Computable

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

theorem vector_head {n} : Computable (@List.Vector.head α n) :=
  Primrec.vector_head.to_comp

end Computable
end
