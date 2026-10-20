@[expose] public section

noncomputable section

open scoped Polynomial

open Module

namespace Polynomial

variable {F : Type*} [Field F] (p q : F[X])
  (E E' : Type*) [Field E] [Field E'] [Algebra F E] [Algebra F E']

namespace Gal

section RootsAction

/-- The function taking `rootSet p p.SplittingField` to `rootSet p E`. This is actually a bijection,
see `Polynomial.Gal.mapRoots_bijective`. -/
def mapRoots [Fact ((p.map (algebraMap F E)).Splits)] : rootSet p p.SplittingField → rootSet p E :=
  Set.MapsTo.restrict (IsScalarTower.toAlgHom F p.SplittingField E) _ _ <| rootSet_mapsTo _

end RootsAction
end Gal
end Polynomial
end
end
