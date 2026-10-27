public section

open CategoryTheory Opposite

universe v₁ v₂ u₁ u₂ u

namespace AlgebraicGeometry

/-- The affine spectrum over a field, restricted to finitely generated algebras. -/
@[implicit_reducible] noncomputable def finiteAlgSpec
    (K : Type u) [Field K] : (FGAlgCat K)ᵒᵖ ⥤ Over (Spec (.of K)) :=
  (ObjectProperty.ι _).op ⋙ algSpec (.of K)

end AlgebraicGeometry
end
