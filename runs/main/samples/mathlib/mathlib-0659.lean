@[expose] public section

universe u v w u'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

variable {α : Type u'}

open FirstOrder Cardinal

open Computability List Fin

namespace Term

theorem listEncode_injective :
    Function.Injective (listEncode : L.Term α → List (α ⊕ (Σ i, L.Functions i))) :=
  Term.encoding.encode_injective

end Term
end Language
end FirstOrder
end
