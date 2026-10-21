namespace OAI

noncomputable section

namespace CuntzPureness

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem boundedOperators_tendsto_of_dense_span {ι : Type*} (v : ι → E)
    (hd : Dense (Submodule.span ℂ (Set.range v) : Set E))
    (F : ℕ → E →L[ℂ] E) (C : ℝ) (hC : ∀ n x, ‖F n x‖ ≤ C * ‖x‖)
    (hv : ∀ i, Tendsto (fun n => F n (v i)) atTop (nhds (v i))) (x : E) :
    Tendsto (fun n => F n x) atTop (nhds x) := by
  have hs : Submodule.span ℂ (Set.range v) ≤ boundedOperatorConvergenceSubmodule F :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hv i)
  exact closure_minimal hs (boundedOperatorConvergenceSubmodule_closed F C hC) (hd x)

end CuntzPureness
end
end OAI
