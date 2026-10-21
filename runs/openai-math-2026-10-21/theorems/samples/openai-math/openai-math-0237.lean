namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset

open scoped ENNReal NNReal BoundedContinuousFunction

open Finset MeasureTheory Filter Topology

open scoped BigOperators

open Finset Matrix

open scoped Matrix.Norms.L2Operator

open Matrix

namespace SmoothObstruction.EuclideanSplitting

open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

lemma groupSpace_forward (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1) (lam : Fin d → ℝ)
    (S : Finset (Fin d)) {K c : ℝ} {s t : ℕ} (hst : s≤t)
    (hU : ‖U t‖≤Real.exp K) (hV : ‖V s‖≤Real.exp K)
    (hc : ∀ j∈S,lam j≤c) (x : groupSpace (U s) (V s) (hUV s) (hVU s) S) :
    ‖Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t) x‖ ≤
      Real.exp (c*((t:ℝ)-s)+2*K)*‖x‖ := by
  have hx := (groupSpace_fixed (U s) (V s) (hUV s) (hVU s) S x).mp x.property
  have hb := norm_transition_projection U V hVU lam S s t hst hU hV hc
  have hn := (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)
    (transition U V lam s t*projection U V S s)).le_opNorm (x:EuclideanSpace ℝ (Fin d))
  rw [Matrix.l2_opNorm_toEuclideanCLM,map_mul,mul_apply_eq_comp] at hn
  change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V S s) x=x at hx
  rw [hx] at hn
  exact hn.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

end SmoothObstruction.EuclideanSplitting
end
end OAI
