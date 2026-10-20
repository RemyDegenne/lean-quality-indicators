@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

namespace MovingSofa

open Set

theorem convexBoundaryArc_jordan (K : ConvexBody Point) (a b : ℝ)
    (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K a).1 ≠ (edgeVertices K b).2) :
    ∃ (A : RectifiableOrientedArc) (p : ArcBVParametrization A.val)
      (γ : RectifiablePathData) (pieces : Fin 3 → RectifiablePathData),
      RealizesConvexArc K a b A ∧
      IsSegmentTraversal (pieces 0) (edgeVertices K a).1 (supportingIntersection K a b) ∧
      IsSegmentTraversal (pieces 1) (supportingIntersection K a b) (edgeVertices K b).2 ∧
      IsReverseArcTraversal (pieces 2) p ∧ IsPathConcatenation γ pieces ∧
      IsOrientedJordanParametrization γ.ordered (Set.range γ.path.val) true γ.path.val ∧
      jordanInterior (Set.range γ.path.val) ⊆
        interior ((supportingLineHalfPlane K a).2 ∩ (supportingLineHalfPlane K b).2) ∧
      Disjoint (jordanInterior (Set.range γ.path.val))
        (⋂ t ∈ Set.Icc a b, (supportingLineHalfPlane K (t : Real.Angle)).2) := by
  obtain ⟨A, hA⟩ :=
    exists_rectifiableOrientedArc_convexBoundaryArc_jordan K a b hab hba hne
  let p : ArcBVParametrization A.val := Classical.choice A.property
  let P := (edgeVertices K (a : Real.Angle)).1
  let Q := (edgeVertices K (b : Real.Angle)).2
  let O := supportingIntersection K a b
  let p₀ := lineSegmentBVPath P O
  let p₁ := lineSegmentBVPath O Q
  obtain ⟨p₂, hp₂, hp₂rev⟩ := exists_reverseArcUnitPath p
  have h01 : p₀.val ⟨1, by norm_num⟩ = p₁.val ⟨0, by norm_num⟩ := by
    simp [p₀, p₁, lineSegmentBVPath]
  have h12 : p₁.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩ := by
    rw [hp₂]
    change p₁.val ⟨1, by norm_num⟩ =
      (reverseArcPath p).val (unitParam_jordan p.a p.b p.ordered ⟨0, by norm_num⟩)
    rw [show unitParam_jordan p.a p.b p.ordered ⟨0, by norm_num⟩ =
      ⟨p.a, le_rfl, p.ordered⟩ by exact Set.Icc.convexComb_zero _ _]
    rw [reverseArcPath_start]
    simpa [p₁, Q, lineSegmentBVPath, Path.segment_apply,
      AffineMap.lineMap_apply_module'] using hA.2.2.symm
  let γpath := concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12
  let γ : RectifiablePathData :=
    { a := 0, b := 2, ordered := by norm_num, path := γpath }
  let pieces : Fin 3 → RectifiablePathData :=
    ![{ a := 0, b := 1, ordered := by norm_num, path := p₀ },
      { a := 0, b := 1, ordered := by norm_num, path := p₁ },
      { a := 0, b := 1, ordered := by norm_num, path := p₂ }]
  have horient := concatThree_convexArc_oriented K hab hba hne A p hA p₂ hp₂ h01 h12
  have hrange : Set.range γ.path.val =
      Set.range (brokenSupportPath K a b) ∪ A.val.carrier := by
    change Set.range (concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12).val = _
    rw [range_concatThreeUnitPaths_jordan, range_reverseArcUnitPath p p₂ hp₂]
    rw [← Function.range_concatUnitIntervals p₀.val p₁.val h01]
    let q := concatUnitPaths_jordan p₀ p₁ h01
    have hrepr : Set.range (reparamTwoToUnit_jordan q).val = Set.range q.val :=
      range_comp_surjective q.val doubleParam_jordan surjective_doubleParam_jordan
    change Set.range q.val ∪ A.val.carrier = _
    rw [← hrepr, show (reparamTwoToUnit_jordan q).val = brokenSupportPath K a b by
      simpa [q, p₀, p₁, P, Q, O] using
        reparam_support_segments_eq_brokenSupportPath K a b h01]
  refine ⟨A, p, γ, pieces, hA, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [pieces, P, O, Matrix.cons_val_zero] using
      isSegmentTraversal_lineSegmentBVPath P O
  · simpa [pieces, Q, O, Matrix.cons_val_zero, Matrix.cons_val_one] using
      isSegmentTraversal_lineSegmentBVPath O Q
  · simpa [pieces, Matrix.cons_val_zero, Matrix.cons_val_one] using hp₂rev
  · simpa [γ, γpath, pieces] using
      isPathConcatenation_concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12
  · simpa [γ, γpath, p₀, p₁] using horient
  · rw [hrange]
    exact jordanInterior_boundaryLoop_subset_endpointHalfPlanes K hab hba hne A p hA
  · rw [hrange]
    exact jordanInterior_boundaryLoop_disjoint_supportIntersection K hab hba A hA

end MovingSofa
end
end
end
end
end
end
end
end
