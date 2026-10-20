@[expose] public section

open Denumerable Encodable Function

section Comp

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable σ]

lemma primrecPred_iff_primrec_decide {p : α → Prop} [DecidablePred p] :
    PrimrecPred p ↔ Primrec (fun a => decide (p a)) where
  mp := PrimrecPred.decide
  mpr := Primrec.primrecPred

end Comp
end
