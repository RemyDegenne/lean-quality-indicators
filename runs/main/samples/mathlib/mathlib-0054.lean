@[expose] public section

universe u v uA uB uA₁ uB₁ uA₂ uB₂ v₁ v₂ v₃

namespace PFunctor

variable (P : PFunctor.{uA, uB}) {α : Type v₁} {β : Type v₂} {γ : Type v₃}

section Obj

variable {P}

@[simp] theorem Obj.eta (x : P α) : .mk x.fst x.snd = x := rfl

end Obj
end PFunctor
end
