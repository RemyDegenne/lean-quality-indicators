public section

open Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] {C D : Set X} [RelCWComplex C D] (n : ℕ)

variable [T2Space X]

/-- **The open `n`-cells form a topological disjoint union of open balls.**  This is a
homeomorphism from the disjoint union of one open unit ball for each `n`-cell onto the union of
the open `n`-cells, which by `TauCeti.skeletonLT_succ_diff_skeletonLT` is the difference of the
`n`-skeleton and the `(n-1)`-skeleton.  Its forward and inverse maps are described by
`TauCeti.iUnionOpenCellHomeomorph_apply` and `TauCeti.iUnionOpenCellHomeomorph_symm_apply`. -/
noncomputable def iUnionOpenCellHomeomorph :
    (Σ _ : cell C n, (ball (0 : Fin n → ℝ) 1)) ≃ₜ
      (⋃ k : cell C n, openCell (C := C) n k : Set X) :=
  -- The characteristic maps are jointly bijective: individual maps are injective on the open
  -- ball, distinct open cells are disjoint, and the open cells cover the target.
  (Equiv.ofBijective
    (fun p : Σ _ : cell C n, (ball (0 : Fin n → ℝ) 1) ↦
      (⟨map n p.1 p.2, mem_iUnion.2 ⟨p.1, p.2, p.2.2, rfl⟩⟩ :
        (⋃ k : cell C n, openCell (C := C) n k : Set X)))
    (by
      constructor
      · rintro ⟨i, y⟩ ⟨j, z⟩ h
        have h' : map n i (y : Fin n → ℝ) = map n j (z : Fin n → ℝ) := congrArg Subtype.val h
        obtain rfl : i = j := by
          by_contra hij
          have hmi : map n i (y : Fin n → ℝ) ∈ openCell (C := C) n i := ⟨y, y.2, rfl⟩
          have hmj : map n i (y : Fin n → ℝ) ∈ openCell (C := C) n j := ⟨z, z.2, h'.symm⟩
          exact (disjoint_openCell_of_ne fun hh ↦
            hij (eq_of_heq (Sigma.mk.inj_iff.1 hh).2)).notMem_of_mem_left hmi hmj
        exact congrArg (Sigma.mk i) (Subtype.ext
          ((map n i).injOn (by rw [source_eq]; exact y.2) (by rw [source_eq]; exact z.2) h'))
      · rintro ⟨x, hx⟩
        obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.1 hx
        exact ⟨⟨i, ⟨y, hy⟩⟩, rfl⟩)).toHomeomorphOfContinuousOpen
    -- Continuity holds on each summand by continuity of its characteristic map.
    (continuous_sigma fun i ↦ Continuous.subtype_mk
      ((continuousOn n i).mono ball_subset_closedBall).domRestrict _)
    -- Each summand embeds onto an open cell, so the assembled map is open.
    (isOpenMap_sigma.2 fun i ↦ by
      -- On the summand `i` the map is `openCellHomeomorph n i` followed by the inclusion of the
      -- open cell `i`, whose range is open in the union.
      have hemb : IsEmbedding fun y : ball (0 : Fin n → ℝ) 1 ↦
          (⟨map n i y, mem_iUnion.2 ⟨i, y, y.2, rfl⟩⟩ :
            (⋃ k : cell C n, openCell (C := C) n k : Set X)) :=
        (IsEmbedding.inclusion (subset_iUnion (fun k ↦ openCell (C := C) n k) i)).comp
          (openCellHomeomorph n i).isEmbedding
      have hrange : (range fun y : ball (0 : Fin n → ℝ) 1 ↦
          (⟨map n i y, mem_iUnion.2 ⟨i, y, y.2, rfl⟩⟩ :
            (⋃ k : cell C n, openCell (C := C) n k : Set X))) =
          Subtype.val ⁻¹' openCell (C := C) n i := by
        ext x
        exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ ⟨y, y.2, rfl⟩, fun ⟨y, hy, hxy⟩ ↦ ⟨⟨y, hy⟩, Subtype.ext hxy⟩⟩
      exact (IsOpenEmbedding.mk hemb (hrange ▸ isOpen_preimage_val_openCell n
        (iUnion_subset fun k ↦ openCell_subset_skeletonLT n k) i)).isOpenMap)

end TauCeti
end
