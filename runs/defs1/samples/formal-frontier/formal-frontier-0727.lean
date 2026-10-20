set_option autoImplicit false

set_option relaxedAutoImplicit false

set_option warningAsError true

@[expose] public section

universe u v w

namespace TopRep

open CategoryTheory

variable {k : Type u} [Ring k] [TopologicalSpace k]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  (H : Subgroup G) [IsClosed (H : Set G)]

/-- The all-closed-subgroup specialization uses the continuous
representatives supplied by the profinite-group library. It realizes the
closed-subgroup restriction clause of Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, corrected second edition, Chapter I, §3,
Proposition 1.3.6(ii), for every closed subgroup of a compact Hausdorff
totally disconnected group, without a canonical choice of section. Discreteness
and joint continuity require separate coefficient hypotheses. -/
noncomputable def profiniteCoind₁RestrictionIso (B : TopRep.{w} k G) :
    res H.subtype (coind₁ B) ≅
      coind₁ (pointwiseContinuousMap (G ⧸ H) (res H.subtype B)) := by
  letI : CompactSpace H :=
    isCompact_iff_compactSpace.mp
      (IsClosed.isCompact (inferInstance : IsClosed (H : Set G)))
  exact coind₁RestrictionIso H B H.continuousCosetRepresentative
    H.continuousCosetRepresentative_rightInverse

end TopRep
end
