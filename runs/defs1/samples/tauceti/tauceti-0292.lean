public section

universe u v w

namespace TauCeti

/-- A directed network with finite lower and upper bounds on every arrow.

The arrow types may contain parallel arrows, arrows in both directions, and loops. Finiteness is
imposed by individual theorems rather than by the network carrier.
-/
structure Network (K : Type w) (V : Type u) [LE K] where
  /-- The type of arrows from one vertex to another. -/
  Hom : V → V → Type v
  /-- The lower bound on each arrow. -/
  lower : Assignment Hom K
  /-- The upper bound on each arrow. -/
  upper : Assignment Hom K
  /-- Every lower bound is at most the corresponding upper bound. -/
  lower_le_upper : ∀ {x y} (e : Hom x y), lower e ≤ upper e

end TauCeti
end
