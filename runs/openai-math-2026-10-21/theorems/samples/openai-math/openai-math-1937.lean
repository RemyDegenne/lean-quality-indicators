namespace OAI

namespace Yau.Geometry

open Yau.Jets Set Metric

open scoped ContDiff

noncomputable section

lemma realPart_fderiv (f : Coord → ℂ) (x : Coord) (hf : DifferentiableAt ℝ f x) (v : Coord) :
    fderiv ℝ (fun z ↦ (f z).re) x v = (fderiv ℝ f x v).re := by
  change fderiv ℝ (Complex.reCLM ∘ f) x v = _
  rw [(Complex.reCLM.hasFDerivAt.comp x hf.hasFDerivAt).fderiv]
  rfl

end
end Yau.Geometry
end OAI
