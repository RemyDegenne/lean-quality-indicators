@[expose] public section

noncomputable section

universe w w' v v₁ v₂ u u₁ u₂

open CategoryTheory Opposite

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

variable (C)

section

variable {C}

/-- An initial object in the opposite category is terminal in the original category. -/
@[to_dual /-- A terminal object in the opposite category is initial in the original category. -/]
def terminalUnopOfInitial {X : Cᵒᵖ} (t : IsInitial X) : IsTerminal X.unop where
  lift s := (t.to (Opposite.op s.pt)).unop
  uniq _ _ _ := Quiver.Hom.op_inj (t.hom_ext _ _)

end
end CategoryTheory.Limits
end
end
