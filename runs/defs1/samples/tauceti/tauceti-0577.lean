public section

open CategoryTheory Limits

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S)

section Smooth

variable [IsProper f] [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f]

/-- For a smooth proper geometrically connected family of curves, `Pic⁰_{X/S}(T)` as a subgroup
of `Pic(X_T) / Pic(T)`: the classes of degree zero on every geometric fibre, that is the sections
of `relativePicardDegreeZeroSubfunctor` at `T`. -/
def relativePicardDegreeZeroSubgroup (T : (Over S)ᵒᵖ) :
    Subgroup ((relativePicardPresheaf f).obj T) where
  carrier := (relativePicardDegreeZeroSubfunctor f).obj T
  mul_mem' := mul_mem_relativePicardDegreeZeroSubfunctor_obj f
  one_mem' := one_mem_relativePicardDegreeZeroSubfunctor_obj f T
  inv_mem' := inv_mem_relativePicardDegreeZeroSubfunctor_obj f

end Smooth
end
end AlgebraicGeometry
end TauCeti
end
