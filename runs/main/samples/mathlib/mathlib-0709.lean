public section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f f₁ f₂ : E → F}
  {x : E} {s : Set E} {c : ℝ}

open Laplacian Metric

namespace InnerProductSpace

namespace HarmonicContOnCl

@[to_fun] theorem const_smul (hf : HarmonicContOnCl f s) (c : ℝ) :
    HarmonicContOnCl (c • f) s := ⟨hf.1.const_smul, hf.2.const_smul c⟩

end HarmonicContOnCl
end InnerProductSpace
end
