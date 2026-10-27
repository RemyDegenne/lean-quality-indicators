public section

open CategoryTheory

namespace ContinuousGroupCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G]

/-- Finite-level negative deflation, natural in the coefficient
representation. In positive homological degree `n`, its components model Tate
deflation in degree `-n-1`. -/
noncomputable def finiteNegativeDeflationNatTrans
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (T.map (QuotientGroup.mk' S))] (n : ℕ) :
    Rep.quotientToInvariantsFunctor R S ⋙
        groupHomology.functor R (G ⧸ S) n ⟶
      Rep.quotientToInvariantsFunctor R T ⋙
        groupHomology.functor R (G ⧸ T) n :=
  Functor.whiskerLeft (Rep.quotientToInvariantsFunctor R S)
      (groupHomology.coinfNatTrans R
        (T.map (QuotientGroup.mk' S)) n) ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (Rep.quotientToInvariantsFunctor R S)
        (FiniteGroupTateCohomology.quotientNormNatTrans
          (R := R) (S := T.map (QuotientGroup.mk' S))))
      (groupHomology.functor R
        ((G ⧸ S) ⧸ T.map (QuotientGroup.mk' S)) n) ≫
    nestedQuotientInvariantsHomologyNatTrans S T hST n

end ContinuousGroupCohomology
end
