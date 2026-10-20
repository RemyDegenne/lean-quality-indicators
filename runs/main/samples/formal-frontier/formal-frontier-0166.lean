set_option warningAsError true

set_option backward.isDefEq.respectTransparency.types false

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits TopRep

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (X : TopRep.{max v w} k G) [CompactSpace G] [DiscreteTopology X]

theorem exists_refinement_class_eq_of_inflation_eq (M : OpenNormalSubgroup G)
    (degree : ℕ)
    (a b : continuousCohomology degree (TopRep.quotientInvariants M.toSubgroup X))
    (hab : (map (openNormalQuotientHom M)
      (TopRep.quotientInvariantsIncl M.toSubgroup X) degree).hom a =
      (map (openNormalQuotientHom M)
        (TopRep.quotientInvariantsIncl M.toSubgroup X) degree).hom b) :
    ∃ (N : OpenNormalSubgroup G) (hNM : N ≤ M),
      (map (quotientTransitionHom N M hNM)
        (quotientTransitionIncl X hNM) degree).hom a =
      (map (quotientTransitionHom N M hNM)
        (quotientTransitionIncl X hNM) degree).hom b := by
  have hzero : (map (openNormalQuotientHom M)
      (TopRep.quotientInvariantsIncl M.toSubgroup X) degree).hom (a - b) = 0 := by
    let f := map (openNormalQuotientHom M)
      (TopRep.quotientInvariantsIncl M.toSubgroup X) degree
    change f.hom (a - b) = 0
    change f.hom a = f.hom b at hab
    rw [map_sub, sub_eq_zero]
    exact hab
  let diff := a - b
  have hvanish := exists_refinement_class_eq_zero X M degree diff hzero
  obtain ⟨N, hNM, hz⟩ := hvanish
  refine ⟨N, hNM, ?_⟩
  let f := map (quotientTransitionHom N M hNM) (quotientTransitionIncl X hNM) degree
  change f.hom (a - b) = 0 at hz
  change f.hom a = f.hom b
  simpa only [map_sub, sub_eq_zero] using hz

end ContinuousCohomology
end
