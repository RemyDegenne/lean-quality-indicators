@[expose] public section

variable {R : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]

namespace Convexity.ConvexSpace

namespace AffineMap

variable {X Y Z T : Type*} [ConvexSpace R X] [ConvexSpace R Y] [ConvexSpace R Z] [ConvexSpace R T]
  {f g : ConvexSpace.AffineMap R X Y}

variable (X) in
/-- The identity map, as a bundled affine map of convex spaces. -/
@[simps, implicit_reducible]
def id : ConvexSpace.AffineMap R X X where
  toFun := _root_.id

end AffineMap
end Convexity.ConvexSpace
end
