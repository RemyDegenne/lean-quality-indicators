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

notation:0 S "[" t ";;;" v "]" => @realizeBoundedTerm _ S _ v 0 t DVec.nil

notation:0 S "[" t ";;;" v ";;;" xs "]" => @realizeBoundedTerm _ S _ v _ t xs

notation:90 t " ↑ᵇ' " n " # " m => Fol.liftBoundedTermAt t n m

infixl:100 " ↑ᵇ " => Fol.liftBoundedTerm

/-- Substitute the variable at position `n` (within the bound `n
+ n' + 1`) with a bounded term `s`. -/
@[expose]
def substBoundedTerm {n n'} :
    ∀ {l} (_t : BoundedPreterm L (n + n' + 1) l) (_s : boundedTerm L n'),
      BoundedPreterm L (n + n') l
  | _, bd_var k, s =>
    if h : k.1 < n then bd_var ⟨k.1, Nat.lt_of_lt_of_le h (Nat.le_add_right n n')⟩
    else
      if h' : n < k.1 then bd_var ⟨k.1 - 1, by omega⟩
      else (s ↑ᵇ n).cast (Nat.le_of_eq (Nat.add_comm n' n))
  | _, bd_func f, _ => bd_func f
  | _, bd_app t₁ t₂, s => bd_app (substBoundedTerm t₁ s) (substBoundedTerm t₂ s)

end Fol
end NFChoice
end
