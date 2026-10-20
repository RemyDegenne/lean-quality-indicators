@[expose] public section

universe u v u' v' w w'

open Cardinal

namespace FirstOrder

namespace Language

variable (L : Language.{u, v})

variable {L} {L' : Language.{u', v'}}

variable (L) (M : Type w)

variable (N : Type w') [L.Structure M] [L.Structure N]

open Structure

@[inherit_doc]
scoped[FirstOrder] notation:25 A " →[" L "] " B => FirstOrder.Language.Hom L A B

@[inherit_doc]
scoped[FirstOrder] notation:25 A " ↪[" L "] " B => FirstOrder.Language.Embedding L A B

@[inherit_doc]
scoped[FirstOrder] notation:25 A " ≃[" L "] " B => FirstOrder.Language.Equiv L A B

variable {L M N} {P : Type*} [L.Structure P] {Q : Type*} [L.Structure Q]

namespace Embedding

/-- A first-order embedding is also a first-order homomorphism. -/
def toHom : (M ↪[L] N) → M →[L] N :=
  HomClass.toHom

end Embedding
end Language
end FirstOrder
end
