public section

open AbstractSimplicialComplex Metric Set Topology

open scoped RealInnerProductSpace

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K : AbstractSimplicialComplex ι} {v : ι} {n : ℕ}

theorem IsCombinatorialBall.exists_openPartialHomeomorph_openStar_halfBall
    (h : IsCombinatorialBall (link K.toPreAbstractSimplicialComplex {v}) n) :
    ∃ c : OpenPartialHomeomorph (Realization K) (EuclideanHalfSpace (n + 1)),
      c.source = openStarRealization K v ∧
      c.target = {z | ‖z.1‖ < 1} ∧
      c (vertex K v) = 0 ∧
      ∀ x : openStarRealization K v, ‖(c x.1).1‖ = 1 - x.1.1 v := by
  obtain ⟨e, he⟩ := h.exists_homeomorph_openStar_halfBall
  let U : Set (EuclideanHalfSpace (n + 1)) := {z | ‖z.1‖ < 1}
  have hU : IsOpen U := isOpen_lt continuous_subtype_val.norm continuous_const
  let : Nonempty U := ⟨⟨⟨0, by simp⟩, by simp [U]⟩⟩
  let j : OpenPartialHomeomorph U (EuclideanHalfSpace (n + 1)) :=
    hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
  let f := e.toOpenPartialHomeomorph.trans j
  let c := f.lift_openEmbedding (K.isOpen_openStarRealization v).isOpenEmbedding_subtypeVal
  have hradius (x : openStarRealization K v) : ‖(c x.1).1‖ = 1 - x.1.1 v := by
    calc
      ‖(c x.1).1‖ = ‖(f x).1‖ := by
        rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
      _ = ‖(e x).1.1‖ := by
        rw [OpenPartialHomeomorph.trans_apply,
          Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply,
          Homeomorph.toOpenPartialHomeomorph_apply]
      _ = 1 - x.1.1 v := he x
  refine ⟨c, ?_, ?_, ?_, hradius⟩
  · simp only [c, f, j, OpenPartialHomeomorph.lift_openEmbedding_source,
      OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source, preimage_univ, inter_self,
      Set.image_univ, Subtype.range_coe]
  · simp [c, f, j, U]
  · apply Subtype.ext
    apply norm_eq_zero.mp
    simpa using hradius ⟨vertex K v, by simp [mem_openStarRealization]⟩

end PreAbstractSimplicialComplex
end
