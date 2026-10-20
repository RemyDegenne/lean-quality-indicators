@[expose] public section

open scoped Manifold

namespace LeanEval

namespace Topology

namespace ClassificationOfSurfaces

namespace Moise

open InvarianceOfDomain

attribute [instance] PartialTriangulation.vertexFintype

attribute [instance] PartialTriangulation.vertexDecidableEq

namespace PartialTriangulation

variable {S : Type*} [TopologicalSpace S]

attribute [instance] PolygonalReplacementSourceAtlas.tileDecidableEq

open LocallyFiniteTriangleComplex PolygonalReplacementSourceAtlas RelativeSynchronizedTarget

namespace PolygonalReplacementSourceAtlas

theorem range_tileFacesMeetingRelativeSourceEmbed
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) :
    Set.range (A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines) =
      ⋃ f : A.TileFacesMeeting C hC, Q.sourceFaceSet f.1 := by
  rw [A.sourceTileFacesMeeting_eq_coordinatePreimage C hC]
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  apply Set.Subset.antisymm
  · rintro x ⟨z, rfl⟩
    let q : Q.complex.support :=
      A.tileFacesMeetingRelativeOldCoordinateSupport C hC N extraLines z
    refine ⟨(Q.sourceHomeomorph.symm q).2, ?_⟩
    have hqClosed :
        q.1.1 ∈ PolygonalFamily.closedRegion
          (A.tileFacePolygonMeeting C hC) := by
      change M.coordinateEmbed z ∈
        PolygonalFamily.closedRegion (A.tileFacePolygonMeeting C hC)
      rw [← A.tileFacesMeetingRelativeOldMesh_support C hC N extraLines,
        ← M.range_coordinateEmbed]
      exact Set.mem_range_self z
    have harg :
        (⟨A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines z,
            (Q.sourceHomeomorph.symm q).2⟩ : U) =
          Q.sourceHomeomorph.symm q :=
      Subtype.ext rfl
    rw [harg, Q.sourceHomeomorph.apply_symm_apply]
    exact hqClosed
  · rintro x ⟨hxU, hxClosed⟩
    let q : Q.complex.support := Q.sourceHomeomorph ⟨x, hxU⟩
    have hqM : q.1.1 ∈ M.toPlaneComplex.support := by
      rw [A.tileFacesMeetingRelativeOldMesh_support C hC N extraLines]
      exact hxClosed
    rw [← M.range_coordinateEmbed] at hqM
    obtain ⟨z, hz⟩ := hqM
    refine ⟨z, ?_⟩
    change
      (Q.sourceHomeomorph.symm
        (A.tileFacesMeetingRelativeOldCoordinateSupport
          C hC N extraLines z)).1 = x
    have hsupportEq :
        A.tileFacesMeetingRelativeOldCoordinateSupport
          C hC N extraLines z = q := by
      apply Subtype.ext
      apply Subtype.ext
      exact hz
    rw [hsupportEq]
    exact congrArg Subtype.val
      (Q.sourceHomeomorph.symm_apply_apply ⟨x, hxU⟩)

end PolygonalReplacementSourceAtlas
end PartialTriangulation
end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end
