public section

universe u v u' uι w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {ι : Type uι} {α : Type u'}

namespace BoundedFormulaInf

@[simp]
theorem castLE_castLE {k m n : ℕ} (h₁ : k ≤ m) (h₂ : m ≤ n) (φ : L.BoundedFormulaInf ι α k) :
    castLE h₂ (castLE h₁ φ) = castLE (h₁.trans h₂) φ := by
  rw [castLE_def, castLE_def, castLE_def, mapBound_mapBound, Fin.castLE_comp_castLE]

end BoundedFormulaInf
end Language
end FirstOrder
end
