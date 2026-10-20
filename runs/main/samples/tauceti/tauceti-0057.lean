public section

noncomputable section

open Complex Set UpperHalfPlane

namespace TauCeti

variable {n : ℕ}

theorem schwarzChristoffelCompactifiedBoundary_injective_iff_edge_intersections
    (a e : Fin (n + 2) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (hfinite : ∀ k, -1 < ∑ l with a l = a k, e l)
    (hsum : ∑ k, e k = -2) :
    Function.Injective (schwarzChristoffelCompactifiedBoundary a e z₀) ↔
      (∀ (i j : Fin (n + 1)), i < j →
        ∀ z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc,
          z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ j.castSucc.castSucc →
            j.val = i.val + 1 ∧ z = schwarzChristoffelVertex a e z₀ i.succ) ∧
      (∀ (i : Fin (n + 1)) (z : ℂ),
        z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc →
        z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ (Fin.last (n + 2)) →
          z = schwarzChristoffelVertex a e z₀ 0) ∧
      (∀ (i : Fin (n + 1)) (z : ℂ),
        z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc →
        z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ
          (Fin.last (n + 1)).castSucc →
          z = schwarzChristoffelVertex a e z₀ (Fin.last (n + 1))) := by
  have hinfty : ∑ k, e k < -1 := by rw [hsum]; norm_num
  constructor
  · intro hinj
    have hB := ((schwarzChristoffelCompactifiedBoundary_injective_iff a e z₀).mp hinj).1
    exact ⟨fun i j hij z hzi hzj =>
      schwarzChristoffelPolygon_bounded_edges_adjacent_and_eq_vertex_of_injOn
        a e z₀ ha hfinite hB.injOn
        i j hij z hzi hzj,
      fun i z hzi hzleft =>
        schwarzChristoffelPolygon_bounded_edgeSet_last_eq_first_vertex_of_injective
          a e z₀ ha hfinite
          hinfty hinj i z hzi hzleft,
      fun i z hzi hzright =>
        schwarzChristoffelPolygon_bounded_edgeSet_last_prevertex_eq_last_vertex_of_injective
          a e z₀ ha hfinite
          hinfty hinj i z hzi hzright⟩
  · rintro ⟨hbounded, hleft, hright⟩
    exact schwarzChristoffelCompactifiedBoundary_injective_of_edge_intersections
      a e z₀ ha hfinite hsum hbounded hleft hright

end TauCeti
end
end
