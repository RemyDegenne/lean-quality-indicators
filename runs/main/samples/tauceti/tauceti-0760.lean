public section

open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E H M : Type*}

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

lemma isClosed_constSmooth (omegaForm : SymplecticForm V) : omegaForm.constSmooth.IsClosed :=
  SmoothTwoForm.isClosed_const _

end SymplecticForm
end TauCeti
end
end
