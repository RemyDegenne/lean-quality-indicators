@[expose] public section

universe v u

open CategoryTheory SimplexCategory Truncated

open Opposite Category Functor Limits

open scoped Simplicial

namespace SSet

namespace Truncated

/-- The identity natural transformation exhibits a simplicial set as a right extension of its
restriction along `(Truncated.inclusion (n := n)).op`. -/
@[simps! left right_as hom_app]
def rightExtensionInclusion (X : SSet.{u}) (n : ℕ) :
    RightExtension (Truncated.inclusion (n := n)).op
      ((Truncated.inclusion n).op ⋙ X) := RightExtension.mk _ (𝟙 _)

end Truncated
end SSet
end
