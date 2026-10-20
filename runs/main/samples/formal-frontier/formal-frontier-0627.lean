@[expose] public section

universe v u

namespace CategoryTheory.ShortComplex.SnakeInput

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [Abelian C] (S : ShortComplex.SnakeInput C)

@[simp high]
theorem composableArrowsWithEndpoints_map_zero_one :
    S.composableArrowsWithEndpoints.map' 0 1 = S.kernelToL₀X₁ := rfl

end CategoryTheory.ShortComplex.SnakeInput
end
