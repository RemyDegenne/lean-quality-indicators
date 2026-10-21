namespace OAI

section

section

noncomputable section

namespace LogConcaveSampling

open Set MeasureTheory ProbabilityTheory

open scoped Classical BigOperators NNReal

lemma meanPathJet_eq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T t : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (ht : t∈Icc 0 T) (n : ℕ) (z : Point d) :
    meanPathJet hF x hr hl T n t z=
      meanMaterialVector F x r n (t,fullProbabilityFlow hF x hr hl t z) := by
  simp only [meanPathJet,probabilityTimeClamp_eq ht]

end LogConcaveSampling
end
end
end
end OAI
