namespace OAI

open Complex

open scoped Topology

namespace Mahler

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [FiniteDimensional ℂ E] in
lemma homogeneous_dcLinear_rotation [FiniteDimensional ℂ E] {f : ι → E → ℂ} {x : E} {m : ℕ}
    (hf : ∀ j, Differentiable ℂ (f j)) (ht : 0 < tau f x)
    (hh : ∀ j (y : E) (c : ℂ), f j (c • y) = c^m * f j y)
    {c : ℂ} (hc : normSq c = 1) (v : E) :
    dcLinear (logTau f) (c • x) (c • v) = dcLinear (logTau f) x v := by
  apply dcLinear_rotation
  · apply differentiable_logTau (fun j => (hf j).differentiableAt)
    simpa [tau_homogeneous (fun j c => hh j x c), hc] using ht
  · intro y
    exact logTau_circle_invariant (fun j c => hh j y c) hc

end Mahler
end OAI
