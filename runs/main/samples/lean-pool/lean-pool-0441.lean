@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory

universe v u

variable (A : Type u)

variable {A}

@[simp] theorem scalarUnitEquiv_apply
    [Category.{v} A] [Preadditive A] [CategoryTheory.Linear ℂ A]
    [MonoidalCategory A]
    (h : HasScalarUnit A) (c : ℂ) :
    scalarUnitEquiv h c = c • 𝟙 (𝟙_ A) := rfl

end RS
end
