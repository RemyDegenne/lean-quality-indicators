open Complex MeasureTheory ProbabilityTheory Filter Set

open scoped Topology

@[expose] public noncomputable section

namespace DirichletTransform.TwoVariable

theorem regCarlsonLSlit_pair_three_term (t u v : ℂ) {x y : ℂ}
    (hz : pair x y ∈ carlsonRSlitDomain) :
    (u + v + t) * regCarlsonLSlit (t + 1) (pair u v) (pair x y) -
      ((u + t) * x + (v + t) * y) * regCarlsonLSlit t (pair u v) (pair x y) +
      t * x * y * regCarlsonLSlit (t - 1) (pair u v) (pair x y) =
      -regCarlsonRSlit (t + 1) (pair u v) (pair x y) +
        (x + y) * regCarlsonRSlit t (pair u v) (pair x y) -
        x * y * regCarlsonRSlit (t - 1) (pair u v) (pair x y) := by
  have hplus := (hasDerivAt_regCarlsonRSlit_L (t + 1) (pair u v) hz).comp_of_eq t
    ((hasDerivAt_id t).add_const 1) rfl
  have h₀ := hasDerivAt_regCarlsonRSlit_L t (pair u v) hz
  have hminus := (hasDerivAt_regCarlsonRSlit_L (t - 1) (pair u v) hz).comp_of_eq t
    ((hasDerivAt_id t).sub_const 1) rfl
  have h := (((hasDerivAt_id t).const_add (u + v)).mul hplus |>.sub
    ((((hasDerivAt_id t).const_add u).mul_const x |>.add
      (((hasDerivAt_id t).const_add v).mul_const y)).mul h₀)).add
    ((((hasDerivAt_id t).mul_const x).mul_const y).mul hminus)
  change HasDerivAt (fun s =>
    (u + v + s) * regCarlsonRSlit (s + 1) (pair u v) (pair x y) -
      ((u + s) * x + (v + s) * y) * regCarlsonRSlit s (pair u v) (pair x y) +
      s * x * y * regCarlsonRSlit (s - 1) (pair u v) (pair x y)) _ t at h
  have heq : (fun s =>
    (u + v + s) * regCarlsonRSlit (s + 1) (pair u v) (pair x y) -
      ((u + s) * x + (v + s) * y) * regCarlsonRSlit s (pair u v) (pair x y) +
      s * x * y * regCarlsonRSlit (s - 1) (pair u v) (pair x y)) = (fun _ : ℂ => 0) :=
    funext fun s => regCarlsonRSlit_pair_three_term s u v hz
  rw [heq] at h
  have H := h.unique (hasDerivAt_const t 0)
  dsimp only [Function.comp_def, id_eq, Pi.add_apply, Pi.mul_apply] at H
  linear_combination H

end DirichletTransform.TwoVariable
end
