public section

namespace TauCeti.CurvedDuplex

open CategoryTheory CategoryTheory.Limits

open ZeroObject

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {R : Type w} [Semiring R] [Linear R C] {w₀ : R}

variable [HasZeroObject C]

@[simp] theorem zero_X₀ : (zero (C := C) (w₀ := w₀)).X₀ = 0 := (rfl)

end TauCeti.CurvedDuplex
end
