public section

noncomputable section

open Filter MeasureTheory Set Topology

open scoped ENNReal NNReal

namespace TauCeti

namespace IsStieltjesFunction

variable {f g : ℝ → ℝ}

lemma add (hf : IsStieltjesFunction f) (hg : IsStieltjesFunction g) :
    IsStieltjesFunction (f + g) := by
  obtain ⟨a, b, μ, hμ⟩ := hf
  obtain ⟨c, d, ν, hν⟩ := hg
  exact ⟨a + c, b + d, μ + ν, hμ.add hν⟩

end IsStieltjesFunction
end TauCeti
end
end
