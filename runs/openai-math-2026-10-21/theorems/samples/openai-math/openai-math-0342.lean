namespace OAI

noncomputable section

open Set Metric Topology BigOperators

open Set Metric Topology

open Set Metric Topology

namespace GroupRingTopology.Attachment

universe u v w

variable {X : Type u} [TopologicalSpace X] {ι : Type v} {n : ℕ}

variable (a : ι → C(Sphere n,X))

lemma exists_interior_separator [T1Space X] (i : ι) (x : OpenDisk n) (z : Space a)
    (hxz : openCell a i x ≠ z) :
    ∃ F : C(Space a,ℝ), F (openCell a i x) = 1 ∧ F z = 0 := by
  classical
  let K : Set (Disk n) := Set.range (boundary n) ∪ cell a i ⁻¹' {z}
  have hKc : IsClosed K := by
    -- Only the part of the inverse image inside this disk is used; the point
    -- set is closed directly, without presupposing Hausdorffness of the adjunction.
    have hz : IsClosed (cell a i ⁻¹' {z}) := by
      cases z with
      | inl y =>
        have heq : ({Sum.inl y} : Set (Space a)) = base a '' {y} := by
          exact (Set.image_singleton (f := base a) (a := y)).symm
        erw [heq,cell_preimage_base_image]
        -- For base points this will follow from a T1 hypothesis below.
        exact (boundary_closedEmbedding n).isClosedMap _
          (isClosed_singleton.preimage (a i).continuous)
      | inr p =>
        have heq : ({Sum.inr p} : Set (Space a)) = openCell a p.1 '' {p.2} := by
          exact (Set.image_singleton (f := openCell a p.1) (a := p.2)).symm
        have hpre := quotient_preimage_openCell_image a p.1 ({p.2} : Set (OpenDisk n))
        have hclosed : IsClosed (quotient a ⁻¹' {Sum.inr p}) := by
          erw [heq,hpre]
          exact isClosedMap_inr _ (isClosedMap_sigmaMk _
            ((isCompact_singleton.image (continuous_interior n)).isClosed))
        exact hclosed.preimage (continuous_inr.comp continuous_sigmaMk)
    exact (boundary_closedEmbedding n).isClosed_range.union hz
  have hxK : interior n x ∉ K := by
    rintro (hx | hx)
    · obtain ⟨s,hs⟩ := hx
      have heq := congrArg (fun d : Disk n => d.1) hs
      exact sphere_disjoint_ball.notMem_of_mem_left s.2 (heq ▸ x.2)
    · apply hxz
      change cell a i (interior n x) = z at hx
      exact (cell_interior a i x).symm.trans hx
  obtain ⟨f,hf0,hf1,_⟩ := exists_continuous_zero_one_of_isClosed hKc
    (isClosed_singleton (x := interior n x)) (Set.disjoint_singleton_right.mpr hxK)
  let g : ι → C(Disk n,ℝ) := fun j => if j = i then f else ContinuousMap.const _ 0
  have hgb (j : ι) (s : Sphere n) : g j (boundary n s) = (0 : ℝ) := by
    dsimp [g]
    split_ifs with hji
    · exact hf0 (Set.mem_union_left _ (Set.mem_range_self s))
    · rfl
  let F : C(Space a,ℝ) := lift a (ContinuousMap.const _ 0) g hgb
  have hFcell (j : ι) (d : Disk n) : F (cell a j d) = g j d := lift_cell a _ _ _ j d
  refine ⟨F,?_,?_⟩
  · change F (Sum.inr ⟨i,x⟩) = 1
    rw [← cell_interior a i x,hFcell]
    simpa only [g,ite_eq_left rfl,Pi.one_apply] using hf1 (Set.mem_singleton _)
  · cases z with
    | inl y => exact lift_base a _ _ _ y
    | inr p =>
      rw [← cell_interior a p.1 p.2,hFcell]
      by_cases hpi : p.1 = i
      · have hm : interior n p.2 ∈ K := by
          right
          change cell a i (interior n p.2) = Sum.inr p
          rw [cell_interior]
          cases p with
          | mk j y =>
            dsimp only at hpi
            subst j
            rfl
        simpa only [g,ite_eq_left hpi,Pi.zero_apply] using hf0 hm
      · simp only [g,ite_eq_right hpi,ContinuousMap.const_apply]

end GroupRingTopology.Attachment
end
end OAI
