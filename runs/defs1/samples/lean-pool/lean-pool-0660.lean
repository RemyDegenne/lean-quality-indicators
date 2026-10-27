public section

namespace NFChoice

universe u v

namespace Fol

variable (L : Language.{u})

variable {L}

prefix:max "&" => Fol.preterm.var

notation:90 t " ↑' " n " # " m => Fol.liftTermAt t n m

infixl:100 " ↑ " => Fol.liftTerm

variable
  (L)

variable {L}

notation "⊥'" => Fol.preformula.falsum

scoped infix:88 " ≃ " => Fol.preformula.equal

scoped infixr:62 " ⟹ " => Fol.preformula.imp

scoped prefix:110 "∀'" => Fol.preformula.all

scoped prefix:max "∼" => Fol.not'

scoped infixr:69 " ⊓' " => Fol.and'

scoped infixr:68 " ⊔' " => Fol.or'

scoped infix:61 " ⇔ " => Fol.biimp

/-- Flypitch construction `ex'`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def ex' (f : formula L) : formula L :=
  not' (preformula.all (not' f))

end Fol
end NFChoice
end
