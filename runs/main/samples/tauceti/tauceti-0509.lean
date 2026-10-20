public section

universe v

namespace TauCeti.TypeBSpinCarrier

open AlgebraicGeometry CategoryTheory

open TauCeti.UniversalEnvelopingAlgebra

open scoped CategoryTheory.MonObj

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance high] Algebra.toModule

variable (n : ℕ)

theorem weightTorus_conj_rootSubgroup_root_simpleIndex
    (ht : (TauCeti.DynkinType.B (n + 1)).Valid) (i : Fin (n + 1))
    (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin (n + 1))).X)
    (u : A) :
    (s ≫ (weightTorus n).hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫ (rootSubgroup n (.inl i)).hom.hom) *
        (s ≫ (weightTorus n).hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter
              (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
              (((TauCeti.DynkinType.B (n + 1)).simplyConnectedRootDatum ht).root
                ((TauCeti.DynkinType.B (n + 1)).simpleIndex ht i)) : A) * u)) ≫
        (rootSubgroup n (.inl i)).hom.hom := by
  rw [← rootGeneratorWeight_inl_eq_root_simpleIndex n ht i]
  exact weightTorus_conj_rootSubgroup n (.inl i) A s u

end TauCeti.TypeBSpinCarrier
end
