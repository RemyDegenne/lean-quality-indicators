public section

noncomputable section

open UpperHalfPlane

open scoped MatrixGroups Pointwise OnePoint

namespace TauCeti.UpperHalfPlane

open Matrix.ProjectiveSpecialLinearGroup (mk_smul_zero_eq_infty_iff mk_smul_infty_eq_infty_iff
  mk_smul_zero_eq_coe_iff mk_smul_infty_eq_coe_iff)

theorem mem_leftHalfPlane_of_mem_extGeodesicSegment {g k : PSL(2, ℝ)}
    {p q : ℍ ⊕ OnePoint ℝ} {z : ℍ} (hg : IsGeodesicFromTo g p q)
    (hp : p ∈ extClosedLeftHalfPlane k) (hq : q ∈ extClosedLeftHalfPlane k)
    (hne : Set.range (geodesicLine g) ≠ Set.range (geodesicLine k))
    (hz : z ∈ extGeodesicSegment p q) (hzp : p ≠ .inl z) (hzq : q ≠ .inl z) :
    z ∈ leftHalfPlane k := by
  -- Treat the two orientations of a ray together, then reduce each endpoint configuration
  -- to an interior parameter of an interval in the closed half-plane.
  have ray_case {w : ℍ} {ξ : OnePoint ℝ}
      (hw : w ∈ closure (leftHalfPlane k))
      (hξ : Sum.inr ξ ∈ extClosedLeftHalfPlane k)
      (hr : Set.range (geodesicLine (rayToward w (.inr ξ))) ≠
        Set.range (geodesicLine k))
      (hz : z ∈ geodesicLine (rayToward w (.inr ξ)) '' Set.Ici 0) (hwz : w ≠ z) :
      z ∈ leftHalfPlane k := by
    obtain ⟨t, ht, rfl⟩ := hz
    have htpos : 0 < t := lt_of_le_of_ne ht (by
      intro heq
      apply hwz
      rw [← heq, geodesicLine_rayToward_zero])
    have hstart : geodesicLine (rayToward w (.inr ξ)) 0 ∈ closure (leftHalfPlane k) := by
      rwa [geodesicLine_rayToward_zero]
    have hclosed := geodesicLine_image_Ici_subset_closure_leftHalfPlane hstart
      (by rwa [rayToward_inr_smul_infty])
    exact geodesicLine_mem_leftHalfPlane_of_mem_closure htpos (lt_add_one t)
      hstart (hclosed ⟨t + 1, Set.mem_Ici.2 (by linarith), rfl⟩) hr
  rcases p with v | ξ <;> rcases q with w | η
  · obtain ⟨s, t, hst, rfl, rfl⟩ := isGeodesicFromTo_inl_inl.1 hg
    rw [extGeodesicSegment_inl_inl, geodesicSegment_geodesicLine, Set.uIcc_of_le hst.le] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    have hsu : s < u := lt_of_le_of_ne hu.1 (fun heq ↦ hzp (by rw [heq]))
    have hut : u < t := lt_of_le_of_ne hu.2 (fun heq ↦ hzq (by rw [heq]))
    exact geodesicLine_mem_leftHalfPlane_of_mem_closure hsu hut
      (inl_mem_extClosedLeftHalfPlane_iff.1 hp) (inl_mem_extClosedLeftHalfPlane_iff.1 hq) hne
  · rw [extGeodesicSegment_inl_inr] at hz
    apply ray_case (inl_mem_extClosedLeftHalfPlane_iff.1 hp) hq
      (by rwa [← (isGeodesicFromTo_rayToward Sum.inl_ne_inr).range_geodesicLine_eq hg]) hz
    exact fun heq ↦ hzp (congrArg Sum.inl heq)
  · rw [extGeodesicSegment_inr_inl] at hz
    apply ray_case (inl_mem_extClosedLeftHalfPlane_iff.1 hq) hp
      (by rw [← (isGeodesicFromTo_rayToward Sum.inl_ne_inr).range_geodesicLine_eq
          (isGeodesicFromTo_mul_pslS_iff.2 hg), range_geodesicLine_mul_pslS]; exact hne) hz
    exact fun heq ↦ hzq (congrArg Sum.inl heq)
  · -- With two ideal endpoints, the piece is the whole line, so bracket the point by `t ± 1`.
    have hξη : ξ ≠ η := fun heq ↦ hg.ne (congrArg Sum.inr heq)
    have hpiece : extGeodesicSegment (.inr ξ) (.inr η) = Set.range (geodesicLine g) := by
      rw [extGeodesicSegment_inr_inr hξη]
      exact hg.range_geodesicLine_eq (isGeodesicFromTo_geodesicFromTo hg.ne)
    rw [hpiece] at hz
    obtain ⟨t, rfl⟩ := hz
    have hclosed := extGeodesicSegment_subset_closure_leftHalfPlane hp hq
    rw [hpiece] at hclosed
    exact geodesicLine_mem_leftHalfPlane_of_mem_closure (sub_one_lt t) (lt_add_one t)
      (hclosed ⟨t - 1, rfl⟩) (hclosed ⟨t + 1, rfl⟩) hne

end TauCeti.UpperHalfPlane
end
end
