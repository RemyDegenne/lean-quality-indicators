@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace

open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicTopology

theorem twoOpenReducedMayerVietoris_exact_biprodZero
    {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    (ShortComplex.mk
      (twoOpenReducedMayerVietorisFromIntersectionZero U V)
      (twoOpenReducedMayerVietorisFromBiprodZero U V)
      (twoOpenReducedMayerVietorisFromIntersectionZero_comp_fromBiprod U V)).Exact := by
  let S := ShortComplex.mk
    (twoOpenReducedMayerVietorisFromIntersectionZero U V)
    (twoOpenReducedMayerVietorisFromBiprodZero U V)
    (twoOpenReducedMayerVietorisFromIntersectionZero_comp_fromBiprod U V)
  apply (ShortComplex.moduleCat_exact_iff S).2
  intro x hx
  let j := biprod.map
    (TopCat.reducedSingularHomologyZeroToOrdinary ((Opens.toTopCat X).obj U))
    (TopCat.reducedSingularHomologyZeroToOrdinary ((Opens.toTopCat X).obj V))
  let T := ShortComplex.mk
    (twoOpenMayerVietorisFromIntersection U V 0)
    (twoOpenMayerVietorisFromBiprod U V hUV 0)
    (twoOpenMayerVietorisFromIntersection_comp_fromBiprod U V hUV 0)
  have hT : T.Exact := twoOpenMayerVietoris_exact_at_biprod U V hUV 0
  let π : S.X₂ ⟶ TopCat.reducedSingularHomology ((Opens.toTopCat X).obj U) 0 := biprod.fst
  let πOrd : T.X₂ ⟶ integralSingularHomology ((Opens.toTopCat X).obj U) 0 := biprod.fst
  have hxOrd : T.g (j x) = 0 := by
    have h := congrArg (fun q ↦ q x)
      (twoOpenReducedMayerVietorisFromBiprodZero_ordinary U V hUV)
    change TopCat.reducedSingularHomologyZeroToOrdinary X (S.g x) = T.g (j x) at h
    rw [hx, map_zero] at h
    exact h.symm
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff T).1 hT _ hxOrd
  let Q := (Opens.toTopCat X).obj (U ⊓ V)
  let e := twoOpenIntersectionHomologyIso U V 0
  let y₀ := e.inv y
  let l := HomologicalComplex.homologyMap
    (integralSingularChainMap (twoOpenIntersectionToLeft U V)) 0
  have hyLeft : l y₀ =
      TopCat.reducedSingularHomologyZeroToOrdinary
        ((Opens.toTopCat X).obj U) (π x) := by
    have h := congrArg (fun q ↦ q y)
      (twoOpenMayerVietorisFromIntersection_fst U V 0)
    change πOrd (T.f y) = l y₀ at h
    rw [hy] at h
    have hj := congrArg (fun q ↦ q x) (biprod.map_fst
      (TopCat.reducedSingularHomologyZeroToOrdinary ((Opens.toTopCat X).obj U))
      (TopCat.reducedSingularHomologyZeroToOrdinary ((Opens.toTopCat X).obj V)))
    change πOrd (j x) =
      TopCat.reducedSingularHomologyZeroToOrdinary
        ((Opens.toTopCat X).obj U) (π x) at hj
    exact h.symm.trans hj
  -- The first coordinate of the ordinary preimage forces its augmentation to vanish.
  have hyAug : Q.singularHomology₀ε TopCat.singularHomologyIntegerCoefficients y₀ = 0 := by
    have hAug := TopCat.singularHomologyZeroAugmentation_naturality
      (twoOpenIntersectionToLeft U V)
    rw [integralSingularHomologyFunctor_map] at hAug
    have h := congrArg (fun q ↦ q y₀) hAug
    change ((Opens.toTopCat X).obj U).singularHomology₀ε
        TopCat.singularHomologyIntegerCoefficients (l y₀) =
      Q.singularHomology₀ε TopCat.singularHomologyIntegerCoefficients y₀ at h
    rw [hyLeft] at h
    have hk := congrArg (fun q ↦ q (π x))
      (TopCat.reducedSingularHomologyZeroToOrdinary_augmentation
        ((Opens.toTopCat X).obj U))
    exact h.symm.trans hk
  let C := ShortComplex.mk (TopCat.reducedSingularHomologyZeroToOrdinary Q)
    (Q.singularHomology₀ε TopCat.singularHomologyIntegerCoefficients)
    (TopCat.reducedSingularHomologyZeroToOrdinary_augmentation Q)
  have hC : C.Exact := ShortComplex.exact_of_f_is_kernel C
    (TopCat.reducedSingularHomologyZeroToOrdinaryIsKernel Q)
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff C).1 hC _ hyAug
  refine ⟨z, ?_⟩
  apply (ModuleCat.mono_iff_injective j).1 inferInstance
  have h := congrArg (fun q ↦ q z)
    (twoOpenReducedMayerVietorisFromIntersectionZero_ordinary U V)
  change j (S.f z) = T.f (e.hom (C.f z)) at h
  rw [hz] at h
  have he : e.hom y₀ = y := Iso.inv_hom_id_apply e y
  rw [he] at h
  exact h.trans hy

end AlgebraicTopology
end
end
