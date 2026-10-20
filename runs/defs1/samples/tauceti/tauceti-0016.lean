public section

namespace TauCeti.GradedLinearQuiver

universe u

variable {C : Type u}

/-- The objects of the **full subquiver** of `C` on the objects satisfying `P`: the induced quiver
along the inclusion of the objects satisfying `P`.  When `C` is a graded linear quiver, so is the
full subquiver, with the hom modules of `C`. -/
abbrev FullSubquiver (P : C → Prop) : Type u :=
  InducedQuiver C (Subtype.val : Subtype P → C)

end TauCeti.GradedLinearQuiver
end
