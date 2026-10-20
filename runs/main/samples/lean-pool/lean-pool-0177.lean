@[expose] public section

namespace LeanEval.Topology.ClassificationOfSurfaces

open Complex

open scoped ComplexConjugate

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace UnorientedPresentationIso

variable {P Q : FiniteCyclicPresentation}

theorem boundary_get_sideIndex
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (f : P.Face) (i : Fin (P.boundary f).length) :
    (Q.boundary (e.faceEquiv f)).get (e.sideIndex validQ f i) =
      if e.reverseFace f then
        (e.edgeRelabeling.mapDart ((P.boundary f).get i)).flip
      else
        e.edgeRelabeling.mapDart ((P.boundary f).get i) := by
  have horiented := e.orientedBoundary_get_orientedSideIndex validQ f i
  cases hreverse : e.reverseFace f
  · simpa [sideIndex, hreverse, orientedBoundary] using horiented
  · let target := inverseWord (Q.boundary (e.faceEquiv f))
    let mapped := (P.boundary f).map e.edgeRelabeling.mapDart
    have hrot : target.rotate (e.faceRotation f) = mapped := by
      simpa only [target, mapped, hreverse, orientedBoundary, ite_true] using
        e.rotate_target_orientedBoundary f
    have hlen : target.length = mapped.length := by
      rw [← hrot, List.length_rotate]
    have hiTarget : i.val < target.length := by
      rw [hlen]
      simpa only [mapped, List.length_map] using i.isLt
    let jTarget : Fin target.length :=
      ⟨(i.val + e.faceRotation f) % target.length,
        Nat.mod_lt _ (Nat.zero_lt_of_lt hiTarget)⟩
    have hpoint :
        (target.rotate (e.faceRotation f))[i.val]? = mapped[i.val]? :=
      congrArg (fun word => word[i.val]?) hrot
    rw [List.getElem?_rotate hiTarget] at hpoint
    have horiented' :
        target.get jTarget =
          e.edgeRelabeling.mapDart ((P.boundary f).get i) := by
      have htargetSome :
          target[jTarget.val]? = some (target.get jTarget) := by
        simp [jTarget.isLt]
      have hmappedSome :
          mapped[i.val]? =
            some (e.edgeRelabeling.mapDart ((P.boundary f).get i)) := by
        simp [mapped, i.isLt]
      rw [hmappedSome] at hpoint
      exact Option.some.inj (htargetSome.symm.trans hpoint)
    let j : Fin (Q.boundary (e.faceEquiv f)).length :=
      jTarget.cast (by simp only [target, inverseWord_length])
    have hinverse :=
      inverseWord_get_rev (Q.boundary (e.faceEquiv f)) j
    have hindex :
        (⟨j.val, by simpa only [inverseWord_length] using j.isLt⟩ :
            Fin (inverseWord (Q.boundary (e.faceEquiv f))).length) =
          jTarget := by
      apply Fin.ext
      rfl
    rw [hindex] at hinverse
    have hflipped :=
      congrArg SignedDart.flip (hinverse.symm.trans horiented')
    have hside : e.sideIndex validQ f i = j.rev := by
      apply Fin.ext
      simp [sideIndex, orientedSideIndex, hreverse, j, jTarget, target]
    rw [hside]
    simpa using hflipped

end UnorientedPresentationIso
end FiniteCyclicPresentation
end LeanEval.Topology.ClassificationOfSurfaces
end
