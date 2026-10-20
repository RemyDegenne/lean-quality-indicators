public section

namespace TauCeti

open CategoryTheory AlgebraicGeometry Opposite

universe u

/-- The object property selecting semisimple affine group schemes of finite type over a field.

The property is transported through the finite-type affine Hopf/group-scheme anti-equivalence.
Thus its normal-subgroup condition is the coordinate-Hopf universal property used by
`semisimpleCommHopfAlgProperty`, presented on the scheme side. -/
def semisimpleAffineGroupSchemeProperty (k : Type u) [Field k] :
    ObjectProperty (FiniteTypeAffineGroupSchemeCat (CommRingCat.of k)) :=
  (semisimpleCommHopfAlgProperty k).op.inverseImage
    (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).inverse

end TauCeti
end
