public section

namespace AlgebraicGeometry

universe u

open CategoryTheory Scheme

lemma Scheme.reduction_topologicalKrullDim (X : Scheme.{u}) :
    topologicalKrullDim (Scheme.reduction.obj X) = topologicalKrullDim X :=
  (Scheme.reductionι_isHomeomorph X).topologicalKrullDim_eq _

end AlgebraicGeometry
end
