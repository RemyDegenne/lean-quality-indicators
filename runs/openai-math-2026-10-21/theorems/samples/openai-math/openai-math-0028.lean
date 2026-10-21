namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped NNReal ProbabilityTheory

namespace Problem336.FinitePosterior

theorem brownian_finset_endpoint_law
    {Ω I : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {C : I → ℝ≥0 → Ω → ℝ} (hC : ∀ i, IsPreBrownianReal (C i) P)
    (hind : iIndepFun (fun i ω s => C i s ω) P)
    (S : Finset I) (t : ℝ≥0) :
    P.map (fun ω (i : S) => C i t ω) =
      Measure.pi (fun _ : S => gaussianReal 0 t) := by
  classical
  have hi : iIndepFun (fun (i : S) ω => C i t ω) P :=
    (hind.precomp Subtype.val_injective).comp
      (fun _ f => f t) (fun _ => measurable_pi_apply t)
  rw [hi.map_fun_eq_pi_map (fun (i : S) => (hC i).aemeasurable t)]
  congr 1
  funext i
  exact ((hC i).hasLaw_eval t).map_eq

end Problem336.FinitePosterior
end
end OAI
