@[expose] public section

open Metric Set unitInterval

open scoped Graph

namespace Schoenflies

open Plane

variable {c : Plane} {r : ℝ}

/-- **The boundary of the axis-parallel square of `ℓ^∞`-radius `r` about `c`, as a closed
polygon.**This is the presentation the overlay and parity machinery consume;
`Schoenflies.modelCurve` is the case `c = 0`, `r = 1` but only as a set. -/
def squarePolygon (c : Plane) {r : ℝ} (hr : 0 < r) : ClosedPolygon 1 where
  vertex := ![sqNE c r, sqNW c r, sqSW c r, sqSE c r]
  vertex_inj := by
    -- Any two of the four corners differ in a coordinate; `r > 0` is what makes them differ.
    have hfst : ∀ p q : Plane, p 0 ≠ q 0 → p ≠ q := fun _ _ h e => h (by rw [e])
    have hsnd : ∀ p q : Plane, p 1 ≠ q 1 → p ≠ q := fun _ _ h e => h (by rw [e])
    have h01 : sqNE c r ≠ sqNW c r := hfst _ _ (by simp; linarith)
    have h02 : sqNE c r ≠ sqSW c r := hfst _ _ (by simp; linarith)
    have h03 : sqNE c r ≠ sqSE c r := hsnd _ _ (by simp; linarith)
    have h12 : sqNW c r ≠ sqSW c r := hsnd _ _ (by simp; linarith)
    have h13 : sqNW c r ≠ sqSE c r := hfst _ _ (by simp; linarith)
    have h23 : sqSW c r ≠ sqSE c r := hfst _ _ (by simp; linarith)
    intro i j hij
    have hi : ∀ i : ZMod 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
    rcases hi i with rfl | rfl | rfl | rfl <;> rcases hi j with rfl | rfl | rfl | rfl
    · rfl
    · exact absurd hij h01
    · exact absurd hij h02
    · exact absurd hij h03
    · exact absurd hij.symm h01
    · rfl
    · exact absurd hij h12
    · exact absurd hij h13
    · exact absurd hij.symm h02
    · exact absurd hij.symm h12
    · rfl
    · exact absurd hij h23
    · exact absurd hij.symm h03
    · exact absurd hij.symm h13
    · exact absurd hij.symm h23
    · rfl
  edges_meet := by
    -- Consecutive sides are perpendicular, so they meet only at the corner they share.
    have mTL : segment ℝ (sqNE c r) (sqNW c r) ∩ segment ℝ (sqNW c r) (sqSW c r)
        ⊆ {sqNW c r} :=
      segment_inter_shared (by
        intro h; simp only [Plane.det, Plane.sub_apply, sqNE_zero, sqNE_one, sqNW_zero,
          sqNW_one, sqSW_zero, sqSW_one] at h; nlinarith)
    have mLB : segment ℝ (sqNW c r) (sqSW c r) ∩ segment ℝ (sqSW c r) (sqSE c r)
        ⊆ {sqSW c r} :=
      segment_inter_shared (by
        intro h; simp only [Plane.det, Plane.sub_apply, sqNW_zero, sqNW_one, sqSW_zero,
          sqSW_one, sqSE_zero, sqSE_one] at h; nlinarith)
    have mBR : segment ℝ (sqSW c r) (sqSE c r) ∩ segment ℝ (sqSE c r) (sqNE c r)
        ⊆ {sqSE c r} :=
      segment_inter_shared (by
        intro h; simp only [Plane.det, Plane.sub_apply, sqSW_zero, sqSW_one, sqSE_zero,
          sqSE_one, sqNE_zero, sqNE_one] at h; nlinarith)
    have mRT : segment ℝ (sqSE c r) (sqNE c r) ∩ segment ℝ (sqNE c r) (sqNW c r)
        ⊆ {sqNE c r} :=
      segment_inter_shared (by
        intro h; simp only [Plane.det, Plane.sub_apply, sqSE_zero, sqSE_one, sqNE_zero,
          sqNE_one, sqNW_zero, sqNW_one] at h; nlinarith)
    -- Opposite sides sit at different values of one coordinate, so they never meet.
    have mTB : ∀ z, z ∈ segment ℝ (sqNE c r) (sqNW c r) →
        z ∈ segment ℝ (sqSW c r) (sqSE c r) → False := by
      intro z h1 h2
      rw [mem_seg_top hr.le] at h1
      rw [mem_seg_bottom hr.le] at h2
      have := h1.1.symm.trans h2.1
      linarith
    have mLR : ∀ z, z ∈ segment ℝ (sqNW c r) (sqSW c r) →
        z ∈ segment ℝ (sqSE c r) (sqNE c r) → False := by
      intro z h1 h2
      rw [mem_seg_left hr.le] at h1
      rw [mem_seg_right hr.le] at h2
      have := h1.1.symm.trans h2.1
      linarith
    intro i j hij
    have hi : ∀ i : ZMod 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
    rcases hi i with rfl | rfl | rfl | rfl <;> rcases hi j with rfl | rfl | rfl | rfl
    · exact absurd rfl hij
    · change segment ℝ (sqNE c r) (sqNW c r) ∩ segment ℝ (sqNW c r) (sqSW c r) ⊆
        {sqNE c r, sqNW c r}
      exact subset_trans mTL (by simp)
    · change segment ℝ (sqNE c r) (sqNW c r) ∩ segment ℝ (sqSW c r) (sqSE c r) ⊆
        {sqNE c r, sqNW c r}
      exact fun z hz => absurd hz.2 (fun h => mTB z hz.1 h)
    · change segment ℝ (sqNE c r) (sqNW c r) ∩ segment ℝ (sqSE c r) (sqNE c r) ⊆
        {sqNE c r, sqNW c r}
      rw [Set.inter_comm]
      exact subset_trans mRT (by simp)
    · change segment ℝ (sqNW c r) (sqSW c r) ∩ segment ℝ (sqNE c r) (sqNW c r) ⊆
        {sqNW c r, sqSW c r}
      rw [Set.inter_comm]
      exact subset_trans mTL (by simp)
    · exact absurd rfl hij
    · change segment ℝ (sqNW c r) (sqSW c r) ∩ segment ℝ (sqSW c r) (sqSE c r) ⊆
        {sqNW c r, sqSW c r}
      exact subset_trans mLB (by simp)
    · change segment ℝ (sqNW c r) (sqSW c r) ∩ segment ℝ (sqSE c r) (sqNE c r) ⊆
        {sqNW c r, sqSW c r}
      exact fun z hz => absurd hz.2 (fun h => mLR z hz.1 h)
    · change segment ℝ (sqSW c r) (sqSE c r) ∩ segment ℝ (sqNE c r) (sqNW c r) ⊆
        {sqSW c r, sqSE c r}
      exact fun z hz => absurd hz.1 (fun h => mTB z hz.2 h)
    · change segment ℝ (sqSW c r) (sqSE c r) ∩ segment ℝ (sqNW c r) (sqSW c r) ⊆
        {sqSW c r, sqSE c r}
      rw [Set.inter_comm]
      exact subset_trans mLB (by simp)
    · exact absurd rfl hij
    · change segment ℝ (sqSW c r) (sqSE c r) ∩ segment ℝ (sqSE c r) (sqNE c r) ⊆
        {sqSW c r, sqSE c r}
      exact subset_trans mBR (by simp)
    · change segment ℝ (sqSE c r) (sqNE c r) ∩ segment ℝ (sqNE c r) (sqNW c r) ⊆
        {sqSE c r, sqNE c r}
      exact subset_trans mRT (by simp)
    · change segment ℝ (sqSE c r) (sqNE c r) ∩ segment ℝ (sqNW c r) (sqSW c r) ⊆
        {sqSE c r, sqNE c r}
      exact fun z hz => absurd hz.1 (fun h => mLR z hz.2 h)
    · change segment ℝ (sqSE c r) (sqNE c r) ∩ segment ℝ (sqSW c r) (sqSE c r) ⊆
        {sqSE c r, sqNE c r}
      rw [Set.inter_comm]
      exact subset_trans mBR (by simp)
    · exact absurd rfl hij
  corner := by
    intro i
    -- The two edges at a corner are perpendicular, so the orientation form is `±4r²`.
    have hi : ∀ i : ZMod 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
    rcases hi i with rfl | rfl | rfl | rfl
    · change det (sqSE c r - sqNE c r) (sqNW c r - sqNE c r) ≠ 0
      intro h
      simp only [Plane.det, Plane.sub_apply, sqNE_zero, sqNE_one, sqNW_zero, sqNW_one,
        sqSE_zero, sqSE_one] at h
      nlinarith
    · change det (sqNE c r - sqNW c r) (sqSW c r - sqNW c r) ≠ 0
      intro h
      simp only [Plane.det, Plane.sub_apply, sqNE_zero, sqNE_one, sqNW_zero, sqNW_one,
        sqSW_zero, sqSW_one] at h
      nlinarith
    · change det (sqNW c r - sqSW c r) (sqSE c r - sqSW c r) ≠ 0
      intro h
      simp only [Plane.det, Plane.sub_apply, sqNW_zero, sqNW_one, sqSW_zero, sqSW_one,
        sqSE_zero, sqSE_one] at h
      nlinarith
    · change det (sqSW c r - sqSE c r) (sqNE c r - sqSE c r) ≠ 0
      intro h
      simp only [Plane.det, Plane.sub_apply, sqSW_zero, sqSW_one, sqSE_zero, sqSE_one,
        sqNE_zero, sqNE_one] at h
      nlinarith

end Schoenflies
end
