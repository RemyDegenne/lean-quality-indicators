public section

open CategoryTheory Limits

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- **The functor of relative effective Cartier divisors** of `f : X ⟶ S`, as a subfunctor of
`baseChangeIdealSheafFunctor f`: at a scheme `T` over `S` it consists of the relative effective
Cartier divisors on `X_T = T ×_S X` over `T`. -/
def relativeEffectiveCartierSubfunctor : Subfunctor (baseChangeIdealSheafFunctor f) where
  obj T := {I | I.IsRelativeEffectiveCartier (pullback.fst T.unop.hom f)}
  map φ _ hI := hI.comap_of_isPullback (isPullback_over_pullback_map_left f φ.unop)

end
end AlgebraicGeometry
end TauCeti
end
