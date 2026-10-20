public section

namespace AlgebraicGeometry

universe u

open CategoryTheory Scheme

@[reassoc]
lemma Scheme.reduction_map_comp_subschemeι {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.reduction.map f ≫ Y.nilradical.subschemeι =
      X.nilradical.subschemeι ≫ f := by
  rw [Scheme.reduction_map]
  exact Scheme.Hom.liftNilradicalSubscheme_fac _

end AlgebraicGeometry
end
