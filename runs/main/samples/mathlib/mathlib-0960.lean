public section

open Filter Set

open scoped Filter Topology Pointwise

variable {a b : ℝ} {l : Filter ℝ} {f f' g g' : ℝ → ℝ}

namespace deriv

theorem lhopital_zero_left_on_Ioo (hab : a < b) (hdf : DifferentiableOn ℝ f (Ioo a b))
    (hg' : ∀ x ∈ Ioo a b, (deriv g) x ≠ 0) (hfb : Tendsto f (𝓝[<] b) (𝓝 0))
    (hgb : Tendsto g (𝓝[<] b) (𝓝 0))
    (hdiv : Tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝[<] b) l) :
    Tendsto (fun x => f x / g x) (𝓝[<] b) l := by
  have hdf : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x := fun x hx =>
    (hdf x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)
  have hdg : ∀ x ∈ Ioo a b, DifferentiableAt ℝ g x := fun x hx =>
    by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiableAt h)
  exact HasDerivAt.lhopital_zero_left_on_Ioo hab (fun x hx => (hdf x hx).hasDerivAt)
    (fun x hx => (hdg x hx).hasDerivAt) hg' hfb hgb hdiv

end deriv
end
