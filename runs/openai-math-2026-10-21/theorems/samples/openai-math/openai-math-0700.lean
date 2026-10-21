namespace OAI

noncomputable section

namespace PoissonSupport.DeGiorgi

open MeasureTheory

open scoped ENNReal

open Filter Topology

lemma coordDeriv_translate {n : ℕ} {f : Space n → ℝ}
    (hf : Differentiable ℝ f) (a : Space n) (i : Fin n) (x : Space n) :
    coordDeriv (fun z => f (a + z)) i x = coordDeriv f i (a + x) := by
  dsimp [coordDeriv]
  have hd : HasFDerivAt (fun z => f (a + z)) (fderiv ℝ f (a + x)) x := by
    simpa only [Function.comp_def, zero_add, ContinuousLinearMap.comp_id, id_eq] using (hf (a + x)).hasFDerivAt.comp x
      ((hasFDerivAt_const a x).fun_add (hasFDerivAt_id x))
  rw [hd.fderiv]

end PoissonSupport.DeGiorgi
end
end OAI
