public section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f f₁ f₂ : E → F}
  {x : E} {s : Set E} {c : ℝ}

open Laplacian Metric

namespace InnerProductSpace

namespace HarmonicContOnCl

@[to_fun] theorem add (hf₁ : HarmonicContOnCl f₁ s) (hf₂ : HarmonicContOnCl f₂ s) :
    HarmonicContOnCl (f₁ + f₂) s := ⟨hf₁.1.add hf₂.1, hf₁.2.add hf₂.2⟩

end HarmonicContOnCl
end InnerProductSpace
end
