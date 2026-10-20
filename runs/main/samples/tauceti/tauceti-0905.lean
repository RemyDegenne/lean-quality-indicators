public section

open Set UpperHalfPlane

open scoped OnePoint

namespace TauCeti

variable {ι : Type*} [Fintype ι]

theorem image_schwarzChristoffelPrimitive_eq_connectedComponentIn (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i)
    (hinfty : ∑ i, e i < -1)
    (hinj : Function.Injective (schwarzChristoffelCompactifiedBoundary a e z₀)) :
    schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet =
      connectedComponentIn (range (schwarzChristoffelCompactifiedBoundary a e z₀))ᶜ
        (schwarzChristoffelPrimitive a e z₀ z₀) := by
  have hdisj := disjoint_image_schwarzChristoffelPrimitive_range a e z₀ hfinite hinfty hinj
  refine image_schwarzChristoffelPrimitive_eq_of_subset a e z₀ hfinite hinfty
    isPreconnected_connectedComponentIn
    (disjoint_left.mpr fun w hw => connectedComponentIn_subset _ _ hw) ?_
  exact ((convex_halfSpace_im_gt 0).isPreconnected.image _
    (differentiableOn_schwarzChristoffelPrimitive a e z₀).continuousOn).subset_connectedComponentIn
    (mem_image_of_mem _ z₀.im_pos) (subset_compl_iff_disjoint_right.mpr hdisj)

end TauCeti
end
