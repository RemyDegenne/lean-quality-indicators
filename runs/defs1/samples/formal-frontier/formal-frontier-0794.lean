public section

open CategoryTheory CategoryTheory.Limits

namespace FiniteGroupTateCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

set_option backward.isDefEq.respectTransparency false in
/-- Degree `-1` Tate cohomology is naturally isomorphic to the kernel of the
norm from coinvariants to invariants. -/
noncomputable def tateCohomologyNegOneNatIsoKernelNorm :
    tateCohomologyFunctor (R := R) (G := G) (-1) ≅
      normKernelFunctor (R := R) (G := G) :=
  NatIso.ofComponents
    (fun M ↦ tateCohomologyNegOneIsoKernelNorm (R := R) (G := G) M) (by
    intro M N f
    change HomologicalComplex.homologyMap (tateComplex.map f) (-1) ≫
        (tateCohomologyNegOneIsoKernelNorm N).hom =
      (tateCohomologyNegOneIsoKernelNorm M).hom ≫
        (normKernelFunctor (R := R) (G := G)).map f
    let _ : Mono ((Limits.ker.ι (ModuleCat R)).app
        ((normArrowFunctor (R := R) (G := G)).obj N)) := by
      dsimp [Limits.ker.ι, normArrowFunctor]
      infer_instance
    apply (cancel_mono ((Limits.ker.ι (ModuleCat R)).app
      ((normArrowFunctor (R := R) (G := G)).obj N))).1
    calc
      (HomologicalComplex.homologyMap (tateComplex.map f) (-1) ≫
          (tateCohomologyNegOneIsoKernelNorm N).hom) ≫
          (Limits.ker.ι (ModuleCat R)).app
            ((normArrowFunctor (R := R) (G := G)).obj N) =
        HomologicalComplex.homologyMap (tateComplex.map f) (-1) ≫
          ((tateCohomologyNegOneIsoKernelNorm N).hom ≫
            (Limits.ker.ι (ModuleCat R)).app
              ((normArrowFunctor (R := R) (G := G)).obj N)) := Category.assoc _ _ _
      _ = HomologicalComplex.homologyMap (tateComplex.map f) (-1) ≫
          ((tateComplex N).homologyι (-1) ≫
            (tateOpcyclesIsoNegOne N).hom) := by
              rw [tateCohomologyNegOneIsoKernelNorm_hom_ι_functor]
      _ = ((tateComplex M).homologyι (-1) ≫
          (tateOpcyclesIsoNegOne M).hom) ≫
          (Rep.coinvariantsFunctor R G).map f := normSequence_first_naturality f
      _ = ((tateCohomologyNegOneIsoKernelNorm M).hom ≫
          (Limits.ker.ι (ModuleCat R)).app
            ((normArrowFunctor (R := R) (G := G)).obj M)) ≫
          (Rep.coinvariantsFunctor R G).map f := by
              rw [tateCohomologyNegOneIsoKernelNorm_hom_ι_functor]
      _ = (tateCohomologyNegOneIsoKernelNorm M).hom ≫
          ((Limits.ker.ι (ModuleCat R)).app
              ((normArrowFunctor (R := R) (G := G)).obj M) ≫
            (Rep.coinvariantsFunctor R G).map f) := Category.assoc _ _ _
      _ = (tateCohomologyNegOneIsoKernelNorm M).hom ≫
          ((normKernelFunctor (R := R) (G := G)).map f ≫
            (Limits.ker.ι (ModuleCat R)).app
              ((normArrowFunctor (R := R) (G := G)).obj N)) := by
                rw [normKernelFunctor_map_ι]
      _ = ((tateCohomologyNegOneIsoKernelNorm M).hom ≫
          (normKernelFunctor (R := R) (G := G)).map f) ≫
          (Limits.ker.ι (ModuleCat R)).app
            ((normArrowFunctor (R := R) (G := G)).obj N) :=
              (Category.assoc _ _ _).symm)

end FiniteGroupTateCohomology
end
