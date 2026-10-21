namespace OAI

noncomputable section

open scoped BigOperators Topology ENNReal

open Complex MeasureTheory

namespace AtomicTriangular

lemma schwartzLP_integral {α : ℝ} (p : GaussianPair α) :
    (∫ z, schwartzLP p.first z)=(p.second 0:ℂ) := by
  rw [←TriangularUniversal.fourier_zero_eq_integral,schwartzLP_fourier,p.fourier_first]

end AtomicTriangular
end
end OAI
