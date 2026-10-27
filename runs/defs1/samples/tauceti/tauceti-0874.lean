public section

universe u v u' uι

namespace FirstOrder

namespace Language

variable (L : Language.{u, v})

variable {L} {ι : Type uι} {α : Type u'} {n : ℕ}

namespace BoundedFormulaInf

/-- Places universal quantifiers on all bound-variable slots of an infinitary bounded formula,
as `BoundedFormula.alls` does for finitary formulas. -/
def alls : ∀ {n}, L.BoundedFormulaInf ι α n → L.FormulaInf ι α
  | 0, φ => φ
  | _ + 1, φ => φ.all.alls

end BoundedFormulaInf
end Language
end FirstOrder
end
