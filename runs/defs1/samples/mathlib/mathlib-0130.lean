@[expose] public section

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

open Function OrderDual Set

namespace LeftOrdContinuous

section SemilatticeSup

variable [SemilatticeSup α] [SemilatticeSup β] {f : α → β}

variable (f)

/-- Convert an injective left order continuous function to an order embedding. -/
@[to_dual
/-- Convert an injective right order continuous function to an order embedding. -/]
def toOrderEmbedding (hf : LeftOrdContinuous f) (h : Injective f) : α ↪o β :=
  ⟨⟨f, h⟩, hf.le_iff h⟩

end SemilatticeSup
end LeftOrdContinuous
end
