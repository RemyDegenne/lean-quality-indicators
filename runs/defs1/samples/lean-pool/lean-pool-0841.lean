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

scoped prefix:110 "∃'" => Fol.ex'

notation:90 f " ↑f' " n " # " m => Fol.liftFormulaAt f n m

infixl:100 " ↑f " => Fol.liftFormula

notation:95 f " [" s " // " n "]f" => Fol.substFormula f s n

scoped infix:51 " ⊢ " => Fol.prf

scoped infix:51 " ⊢' " => Fol.provable

variable (L)

variable {L}

scoped infix:51 " ⊨ₛ " => Fol.satisfiedIn

scoped infix:51 " ⊨ " => Fol.satisfied

variable (L)

export BoundedPreterm (bd_var bd_func bd_app)

variable {L}

prefix:max "&ᵇ" => @bd_var _ _

namespace BoundedPreterm

/-- Flypitch construction `cast_eq`, retained by the first-order soundness and completeness
development.
-/
@[expose]
protected def castEq {n m l} (h : n = m) (t : BoundedPreterm L n l) :
    BoundedPreterm L m l :=
  t.cast (Nat.le_of_eq h)

end BoundedPreterm
end Fol
end NFChoice
end
