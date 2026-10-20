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

scoped[FirstOrder] prefix:arg "&" => FirstOrder.Language.Term.var ∘ Sum.inr

variable (L) (α)

variable {L} {α} {n : ℕ}

namespace BoundedFormula

open Finset

@[simp]
theorem relabel_imp (g : α → β ⊕ (Fin n)) {k} (φ ψ : L.BoundedFormula α k) :
    (φ.imp ψ).relabel g = (φ.relabel g).imp (ψ.relabel g) :=
  rfl

end BoundedFormula
end Language
end FirstOrder
end
