public section

open CategoryTheory

namespace TauCeti.G2ShortRoot.PrimeField

open TauCeti.DynkinType

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

local macro "cross_entry_norm" : tactic =>
  `(tactic| (simp [Matrix.mul_apply, Fin.sum_univ_succ,
    ConstantMultiplication.imageStructureMatrix_def, crossOperator_def]; ring_nf; reduce_mod_char))

/-- **Each simple root space of the carrier is free of rank one**, with the scalar `1`
corresponding to the tangent vector of the numbered root subgroup. This is the form in which a
pinning records its simple root vectors. -/
def rootSpaceEquiv (k : Fin 2 ⊕ Fin 2) :
    ZMod 3 ≃ₗ[ZMod 3] Derivation.adjointWeightSpace weightTorusCoordinateMap.hom
      (SplitTorus.weightCharacter (G2.rootGeneratorWeight valid_G2 k)) :=
  (LinearEquiv.toSpanNonzeroSingleton (ZMod 3) _ (rootVector k) (rootVector_ne_zero k)).trans
    (LinearEquiv.ofEq _ _ (adjointWeightSpace_rootGeneratorWeight_eq_span k).symm)

end
end TauCeti.G2ShortRoot.PrimeField
end
