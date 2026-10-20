@[expose] public section

universe u v w u' v'

namespace FirstOrder

namespace Language

variable (L : Language.{u, v}) {L' : Language}

variable {M : Type w} {α : Type u'} {β : Type v'} {γ : Type*}

open FirstOrder

open Structure Fin

export Term (var func)

variable {L}

namespace Term

open Finset

/-- Relabels a term's variables along a bijection. -/
@[simps]
def relabelEquiv (g : α ≃ β) : L.Term α ≃ L.Term β :=
  ⟨relabel g, relabel g.symm, fun t => by simp, fun t => by simp⟩

end Term
end Language
end FirstOrder
end
