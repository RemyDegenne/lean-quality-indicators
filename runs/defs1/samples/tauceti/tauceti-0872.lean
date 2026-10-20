public section

universe u v uι uα uβ w

namespace TauCeti

open FirstOrder Language

namespace BoundedFormulaInf

variable {L : Language.{u, v}} {ι : Type uι} {α : Type uα} {β : Type uβ}

variable {m n : ℕ}

/-- Relabel free variables by free variables or new bound slots. The `m` new slots are placed
before the original `n` slots, and quantifiers continue to bind the last slot. -/
def relabel (g : α → β ⊕ Fin m) :
    ∀ {n}, L.BoundedFormulaInf ι α n → L.BoundedFormulaInf ι β (m + n)
  | _, .falsum => .falsum
  | n, .equal t₁ t₂ => .equal (t₁.relabel (BoundedFormula.relabelAux g n))
      (t₂.relabel (BoundedFormula.relabelAux g n))
  | n, .rel R ts => .rel R fun i => (ts i).relabel (BoundedFormula.relabelAux g n)
  | _, .imp φ ψ => (relabel g φ).imp (relabel g ψ)
  | _, .all φ => (relabel g φ).all
  | _, .iSup φs => .iSup fun i => relabel g (φs i)
  | _, .iInf φs => .iInf fun i => relabel g (φs i)

end BoundedFormulaInf
end TauCeti
end
