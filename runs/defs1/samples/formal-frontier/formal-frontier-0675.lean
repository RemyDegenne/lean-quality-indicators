@[expose] public section

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace IntegralDenseOpenRationalScheme

/-- The dominant native arrow underlying an integral dense-open arrow. -/
def nativeHom {X Y : IntegralDenseOpenRationalScheme.{u}} (f : X ⟶ Y) :
    nativeObject X ⟶ nativeObject Y :=
  IntegralDominantRationalScheme.hom (toRationalMap f)
    ((Scheme.RationalMap.pullsDenseOpens_iff_isDominant _).mp f.hom.pullsDenseOpens)

end IntegralDenseOpenRationalScheme
end AlgebraicGeometry
end
