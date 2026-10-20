@[expose] public section

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace IntegralDominantRationalSchemeOver

/-- Convert native dominant arrows back to the integral full subcategory. -/
noncomputable def toDenseOpen {S : Scheme.{u}} : IntegralDominantRationalSchemeOver S ⥤
    IntegralDenseOpenRationalSchemeOver S where
  obj := denseObject
  map := denseHom
  map_id _ := by
    apply ObjectProperty.hom_ext
    apply DenseOpenRationalSchemeOver.hom_ext
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply DenseOpenRationalSchemeOver.hom_ext
    exact (Scheme.RationalMap.compOfPullsDenseOpens_eq_comp
      f.toRationalMap ((Scheme.RationalMap.pullsDenseOpens_iff_isDominant _).mpr f.dominant)
      g.toRationalMap).symm

end IntegralDominantRationalSchemeOver
end AlgebraicGeometry
end
