namespace OAI

namespace HarmonicArtin.ParabolicIntersections

open Simplicial CategoryTheory

attribute [local instance] Classical.decEq Classical.propDecidable

variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

lemma relativeEligibleProductFun_le_iff (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (A D:RelativeEligibleWithin M f U cutoff Ref (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x) ×
      RelativeEligibleWithin M f U cutoff Ref (sourceCoset M C (source_spherical_mono M Set.subset_union_right hT) x)) :
    relativeEligibleProductFun M f U cutoff Ref B C hT hd hc x A ≤ relativeEligibleProductFun M f U cutoff Ref B C hT hd hc x D ↔ A≤D :=
  sourceCosetProductFun_le_iff M B C hT hd hc x
    (⟨A.1.val,A.1.property.1⟩,⟨A.2.val,A.2.property.1⟩)
    (⟨D.1.val,D.1.property.1⟩,⟨D.2.val,D.2.property.1⟩)

end HarmonicArtin.ParabolicIntersections
end OAI
