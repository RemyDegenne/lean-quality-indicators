@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace

open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicTopology

theorem twoOpenMayerVietoris_exact_space {X : TopCat.{u}}
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (ShortComplex.mk
      (twoOpenMayerVietorisToSpace U V hUV (n + 1))
      (twoOpenMayerVietorisδ U V hUV n)
      (by
        change (HomologicalComplex.homologyMap
            (twoOpenSmallShortComplex U V).g (n + 1) ≫
          (twoOpenSpaceHomologyIso U V hUV (n + 1)).hom) ≫
          ((twoOpenSpaceHomologyIso U V hUV (n + 1)).inv ≫
            (twoOpenSmallShortExact U V).δ (n + 1) n (by simp)) = 0
        rw [Category.assoc, Iso.hom_inv_id_assoc]
        exact (twoOpenSmallShortExact U V).comp_δ (n + 1) n (by simp))).Exact := by
  let hS := twoOpenSmallShortExact U V
  let e : (ShortComplex.mk
      (twoOpenMayerVietorisToSpace U V hUV (n + 1))
      (twoOpenMayerVietorisδ U V hUV n)
      (by
        change (HomologicalComplex.homologyMap
            (twoOpenSmallShortComplex U V).g (n + 1) ≫
          (twoOpenSpaceHomologyIso U V hUV (n + 1)).hom) ≫
          ((twoOpenSpaceHomologyIso U V hUV (n + 1)).inv ≫
            hS.δ (n + 1) n (by simp)) = 0
        rw [Category.assoc, Iso.hom_inv_id_assoc]
        exact hS.comp_δ (n + 1) n (by simp))) ≅
      (ShortComplex.mk
        (HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).g (n + 1))
        (hS.δ (n + 1) n (by simp))
        (hS.comp_δ (n + 1) n (by simp))) :=
    ShortComplex.isoMk (Iso.refl _)
      (twoOpenSpaceHomologyIso U V hUV (n + 1)).symm
      (Iso.refl _)
      (by simp [twoOpenMayerVietorisToSpace, Category.assoc])
      (by simp [twoOpenMayerVietorisδ])
  exact ShortComplex.exact_of_iso e.symm
    (hS.homology_exact₃ (n + 1) n (by simp))

end AlgebraicTopology
end
end
