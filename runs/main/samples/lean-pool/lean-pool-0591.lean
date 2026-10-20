@[expose] public section

open Set

open scoped Graph

namespace Schoenflies

open _root_.Graph

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}
  {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}

theorem gridHEdge_interior_snd {xc yc : ℕ → ℝ} {i j : ℕ} {z : Plane}
    (hz : z ∈ (gridHEdge xc yc i j).interior) : z 1 = yc j := by
  change z ∈ openSegment ℝ (gridPt xc yc i j) (gridPt xc yc (i + 1) j) at hz
  rw [openSegment_eq_image_lineMap] at hz
  obtain ⟨t, -, rfl⟩ := hz
  simp [AffineMap.lineMap_apply, gridPt]

end Schoenflies
end
