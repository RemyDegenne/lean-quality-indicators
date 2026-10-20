@[expose] public section

universe u

open CategoryTheory Simplicial SimplicialObject.Truncated

namespace SSet

variable {X Y : SSet.{u}}

open FundamentalGroupoid

@[simp]
lemma mapFundamentalGroupoid_obj_mk (f : X ⟶ Y) (x : X _⦋0⦌) :
    (mapFundamentalGroupoid f).obj (mk x) = mk (f.app _ x) := rfl

end SSet
end
