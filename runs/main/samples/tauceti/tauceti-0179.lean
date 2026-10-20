public section

universe u v u' uι

namespace FirstOrder

namespace Language

variable (L : Language.{u, v})

variable {L} {ι : Type uι} {α : Type u'} {n : ℕ}

namespace BoundedFormulaInf

theorem sup_def (φ ψ : L.BoundedFormulaInf ι α n) : φ ⊔ ψ = φ.not.imp ψ := (rfl)

end BoundedFormulaInf
end Language
end FirstOrder
end
