public section

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped Topology

universe u v

namespace CompletedGroupAlgebra

/-- The ring topology underlying the inverse-limit topology on a completed
group algebra. -/
@[expose] def ringTopology (R : Type u) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (G : ProfiniteGrp.{v}) :
    RingTopology (CompletedGroupAlgebra R G) where
  toTopologicalSpace := inverseLimitTopology R G
  continuous_add := by
    let _ : TopologicalSpace (CompletedGroupAlgebra R G) := inverseLimitTopology R G
    apply continuous_iInf_rng.mpr
    intro U
    apply continuous_induced_rng.mpr
    let _ : TopologicalSpace (MonoidAlgebra R (G ⧸ U.toSubgroup)) :=
      (finiteGroupAlgebraRingTopology R (G ⧸ U.toSubgroup)).toTopologicalSpace
    let _ : IsTopologicalRing (MonoidAlgebra R (G ⧸ U.toSubgroup)) :=
      (finiteGroupAlgebraRingTopology R (G ⧸ U.toSubgroup)).toIsTopologicalRing
    have hp : Continuous[inverseLimitTopology R G,
        (finiteGroupAlgebraRingTopology R
          (G ⧸ U.toSubgroup)).toTopologicalSpace] (proj R G U) :=
      continuous_iInf_dom continuous_induced_dom
    change Continuous fun z : CompletedGroupAlgebra R G × CompletedGroupAlgebra R G =>
      proj R G U (z.1 + z.2)
    rw [show (fun z : CompletedGroupAlgebra R G × CompletedGroupAlgebra R G =>
        proj R G U (z.1 + z.2)) =
        (fun z => proj R G U z.1 + proj R G U z.2) by
      funext z
      exact map_add (proj R G U) z.1 z.2]
    exact (hp.comp continuous_fst).add (hp.comp continuous_snd)
  continuous_mul := by
    let _ : TopologicalSpace (CompletedGroupAlgebra R G) := inverseLimitTopology R G
    apply continuous_iInf_rng.mpr
    intro U
    apply continuous_induced_rng.mpr
    let _ : TopologicalSpace (MonoidAlgebra R (G ⧸ U.toSubgroup)) :=
      (finiteGroupAlgebraRingTopology R (G ⧸ U.toSubgroup)).toTopologicalSpace
    let _ : IsTopologicalRing (MonoidAlgebra R (G ⧸ U.toSubgroup)) :=
      (finiteGroupAlgebraRingTopology R (G ⧸ U.toSubgroup)).toIsTopologicalRing
    have hp : Continuous[inverseLimitTopology R G,
        (finiteGroupAlgebraRingTopology R
          (G ⧸ U.toSubgroup)).toTopologicalSpace] (proj R G U) :=
      continuous_iInf_dom continuous_induced_dom
    change Continuous fun z : CompletedGroupAlgebra R G × CompletedGroupAlgebra R G =>
      proj R G U (z.1 * z.2)
    rw [show (fun z : CompletedGroupAlgebra R G × CompletedGroupAlgebra R G =>
        proj R G U (z.1 * z.2)) =
        (fun z => proj R G U z.1 * proj R G U z.2) by
      funext z
      exact map_mul (proj R G U) z.1 z.2]
    exact (hp.comp continuous_fst).mul (hp.comp continuous_snd)
  continuous_neg := by
    let _ : TopologicalSpace (CompletedGroupAlgebra R G) := inverseLimitTopology R G
    apply continuous_iInf_rng.mpr
    intro U
    apply continuous_induced_rng.mpr
    let _ : TopologicalSpace (MonoidAlgebra R (G ⧸ U.toSubgroup)) :=
      (finiteGroupAlgebraRingTopology R (G ⧸ U.toSubgroup)).toTopologicalSpace
    let _ : IsTopologicalRing (MonoidAlgebra R (G ⧸ U.toSubgroup)) :=
      (finiteGroupAlgebraRingTopology R (G ⧸ U.toSubgroup)).toIsTopologicalRing
    have hp : Continuous[inverseLimitTopology R G,
        (finiteGroupAlgebraRingTopology R
          (G ⧸ U.toSubgroup)).toTopologicalSpace] (proj R G U) :=
      continuous_iInf_dom continuous_induced_dom
    change Continuous fun z : CompletedGroupAlgebra R G => proj R G U (-z)
    rw [show (fun z : CompletedGroupAlgebra R G => proj R G U (-z)) =
        (fun z => -(proj R G U z)) by
      funext z
      exact map_neg (proj R G U) z]
    exact hp.neg

end CompletedGroupAlgebra
end
end
