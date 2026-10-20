@[expose] public section

universe w v v' u u'

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

variable (W : MorphismProperty C)

/-- A class of morphisms `W` has the two-out-of-three property if whenever two out
of three maps in `f`, `g`, `f ≫ g` are in `W`, then the third map is also in `W`. -/
class HasTwoOutOfThreeProperty (W : MorphismProperty C) : Prop
    extends W.IsStableUnderComposition, W.HasOfPostcompProperty W, W.HasOfPrecompProperty W where

end MorphismProperty
end CategoryTheory
end
