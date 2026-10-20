@[expose] public section

open Function

universe u v w

variable {α β γ δ : Type*} {r : α → α → Prop} {s : β → β → Prop}
  {t : γ → γ → Prop} {u : δ → δ → Prop}

infixl:25 " →r " => RelHom

infixl:25 " ↪r " => RelEmbedding

namespace RelEmbedding

/-- `Sum.inr` as a relation embedding into `Sum.Lex r s`. -/
@[simps]
def sumLexInr (r : α → α → Prop) (s : β → β → Prop) : s ↪r Sum.Lex r s where
  toFun := Sum.inr
  inj' := Sum.inr_injective
  map_rel_iff' := Sum.lex_inr_inr

end RelEmbedding
end
