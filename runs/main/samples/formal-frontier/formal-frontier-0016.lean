@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace

open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicTopology

theorem twoOpenMayerVietorisδ_swap {X : TopCat.{u}} (U V : Opens X)
    (hUV : U ⊔ V = ⊤) (hVU : V ⊔ U = ⊤) (n : ℕ) :
    twoOpenMayerVietorisδ U V hUV n ≫
        HomologicalComplex.homologyMap
          (twoOpenIntersectionSwapChainIso U V).hom n =
      -(twoOpenMayerVietorisSwapSpaceMap U V hUV hVU (n + 1) ≫
        twoOpenMayerVietorisδ V U hVU n) := by
  have h := HomologicalComplex.HomologySequence.δ_naturality
    (twoOpenSmallShortComplexSwapIso U V).hom
    (twoOpenSmallShortExact U V) (twoOpenSmallShortExact V U)
    (n + 1) n (by simp)
  change (twoOpenSmallShortExact U V).δ (n + 1) n (by simp) ≫
      HomologicalComplex.homologyMap
        (twoOpenSmallShortComplexSwapIso U V).hom.τ₁ n =
    HomologicalComplex.homologyMap
        (twoOpenSmallShortComplexSwapIso U V).hom.τ₃ (n + 1) ≫
      (twoOpenSmallShortExact V U).δ (n + 1) n (by simp) at h
  change ((twoOpenSpaceHomologyIso U V hUV (n + 1)).inv ≫
      (twoOpenSmallShortExact U V).δ (n + 1) n (by simp)) ≫
      HomologicalComplex.homologyMap
        (-(twoOpenSmallShortComplexSwapIso U V).hom.τ₁) n =
    -(((twoOpenSpaceHomologyIso U V hUV (n + 1)).inv ≫
      HomologicalComplex.homologyMap
        (twoOpenSmallShortComplexSwapIso U V).hom.τ₃ (n + 1) ≫
      (twoOpenSpaceHomologyIso V U hVU (n + 1)).hom) ≫
      ((twoOpenSpaceHomologyIso V U hVU (n + 1)).inv ≫
        (twoOpenSmallShortExact V U).δ (n + 1) n (by simp)))
  simp only [HomologicalComplex.homologyMap_neg, Preadditive.comp_neg,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [h]

end AlgebraicTopology
end
end
