@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory Polynomial

open scoped CategoryTheory.MonObj

universe u v w t

namespace AlgebraicGeometry

/-- The group-valued functor of points of `rootsOfUnityGroupScheme`, restricted
to affine test schemes. -/
abbrev rootsOfUnityPointsFunctor (K : Type u) [CommRing K] (n : ℕ) :
    CommAlgCat K ⥤ GrpCat :=
  (algSpec (.of K)).rightOp ⋙
    yonedaGrp.obj (rootsOfUnityGroupScheme K n)

end AlgebraicGeometry
end
end
