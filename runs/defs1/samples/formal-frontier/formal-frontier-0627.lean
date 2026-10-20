public section

open CategoryTheory CategoryTheory.Limits

namespace FiniteGroupTateCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

set_option backward.isDefEq.respectTransparency false in
/-- Degree `0` Tate cohomology is naturally isomorphic to the cokernel of the
norm from coinvariants to invariants. -/
noncomputable def tateCohomologyZeroNatIsoCokernelNorm :
    tateCohomologyFunctor (R := R) (G := G) 0 ≅
      normCokernelFunctor (R := R) (G := G) :=
  NatIso.ofComponents
    (fun M ↦ tateCohomologyZeroIsoCokernelNorm (R := R) (G := G) M) (by
    intro M N f
    change HomologicalComplex.homologyMap (tateComplex.map f) 0 ≫
        (tateCohomologyZeroIsoCokernelNorm N).hom =
      (tateCohomologyZeroIsoCokernelNorm M).hom ≫
        (normCokernelFunctor (R := R) (G := G)).map f
    apply (cancel_epi
      ((tateCyclesIsoZero M).inv ≫ (tateComplex M).homologyπ 0)).1
    calc
      ((tateCyclesIsoZero M).inv ≫ (tateComplex M).homologyπ 0) ≫
          (HomologicalComplex.homologyMap (tateComplex.map f) 0 ≫
            (tateCohomologyZeroIsoCokernelNorm N).hom) =
        (((tateCyclesIsoZero M).inv ≫ (tateComplex M).homologyπ 0) ≫
          HomologicalComplex.homologyMap (tateComplex.map f) 0) ≫
            (tateCohomologyZeroIsoCokernelNorm N).hom :=
              (Category.assoc _ _ _).symm
      _ = ((Rep.invariantsFunctor R G).map f ≫
          ((tateCyclesIsoZero N).inv ≫ (tateComplex N).homologyπ 0)) ≫
            (tateCohomologyZeroIsoCokernelNorm N).hom := by
              rw [normSequence_last_naturality]
      _ = (Rep.invariantsFunctor R G).map f ≫
          (((tateCyclesIsoZero N).inv ≫ (tateComplex N).homologyπ 0) ≫
            (tateCohomologyZeroIsoCokernelNorm N).hom) := Category.assoc _ _ _
      _ = (Rep.invariantsFunctor R G).map f ≫
          (Limits.coker.π (ModuleCat R)).app
            ((normArrowFunctor (R := R) (G := G)).obj N) := by
              rw [tateCohomologyZeroIsoCokernelNorm_π_hom_functor]
      _ = (Limits.coker.π (ModuleCat R)).app
          ((normArrowFunctor (R := R) (G := G)).obj M) ≫
          (normCokernelFunctor (R := R) (G := G)).map f := by
            rw [normCokernelFunctor_π_map]
      _ = (((tateCyclesIsoZero M).inv ≫ (tateComplex M).homologyπ 0) ≫
          (tateCohomologyZeroIsoCokernelNorm M).hom) ≫
            (normCokernelFunctor (R := R) (G := G)).map f := by
              rw [tateCohomologyZeroIsoCokernelNorm_π_hom_functor]
      _ = ((tateCyclesIsoZero M).inv ≫ (tateComplex M).homologyπ 0) ≫
          ((tateCohomologyZeroIsoCokernelNorm M).hom ≫
            (normCokernelFunctor (R := R) (G := G)).map f) :=
              Category.assoc _ _ _)

end FiniteGroupTateCohomology
end
