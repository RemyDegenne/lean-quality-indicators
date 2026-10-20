@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace

open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicTopology

theorem twoOpenReducedMayerVietorisδZero_naturality {X Y : TopCat.{u}}
    (f : X ⟶ Y) (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V')
    (hUV : U ⊔ V = ⊤) (hU'V' : U' ⊔ V' = ⊤) :
    twoOpenReducedMayerVietorisδZero U V hUV ≫
        TopCat.reducedSingularHomologyMap
          (twoOpenIntersectionMap f U V U' V' hU hV) 0 =
      TopCat.reducedSingularHomologyMap f 1 ≫
        twoOpenReducedMayerVietorisδZero U' V' hU'V' := by
  apply (cancel_mono
    (TopCat.reducedSingularHomologyZeroToOrdinary
        ((Opens.toTopCat Y).obj (U' ⊓ V')) ≫
      (twoOpenIntersectionHomologyIso U' V' 0).hom)).1
  simp only [Category.assoc]
  rw [TopCat.reducedSingularHomologyZeroToOrdinary_naturality_assoc]
  rw [← twoOpenIntersectionHomologyIso_naturality]
  rw [twoOpenReducedMayerVietorisδZero_ordinary_assoc]
  rw [twoOpenMayerVietorisδ_naturality_induced]
  all_goals try rw [← TopCat.reducedSingularHomologyMap_isoOfNeZero_assoc]
  rw [twoOpenReducedMayerVietorisδZero_ordinary]

end AlgebraicTopology
end
end
