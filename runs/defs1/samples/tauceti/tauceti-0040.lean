public section

open scoped DirectSum

namespace TauCeti.GradedLinearQuiver

universe u u' v w

variable {D : Type u'} (C : Type u)

/-- The objects of the **quiver induced** along `F : D → C`: one object for each object of `D`.
When `C` is a graded linear quiver, so is `InducedQuiver C F`, with the hom module of `C` from
`F X.obj` to `F Y.obj` as its hom module from `X` to `Y`. -/
@[ext]
structure InducedQuiver (F : D → C) where
  /-- The underlying object of `D`. -/
  obj : D

end TauCeti.GradedLinearQuiver
end
