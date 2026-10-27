public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace

open scoped Distributions InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]

variable {mu : Measure E} {Omega : Opens E} {p : ENNReal}

variable [InnerProductSpace ℝ E] [Fact (1 <= p)]

variable [OpensMeasurableSpace E] [mu.IsAddHaarMeasure]

section WeakDerivIdentification

variable [FiniteDimensional ℝ E]

/-- Construct a Sobolev function from its `Lᵖ` value and weak-gradient components. -/
def W1p.mk (u : Lp ℝ p (mu.restrict Omega)) (g : Lp E p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega u (fun x => innerSL ℝ (g x))) : W1p mu Omega p :=
  ⟨assembleSobolev1JetLp u g, (mem_w1pSubmodule_iff_hasWeakFDerivOn _).mpr (by
    rw [value_assembleSobolev1JetLp]
    convert h using 1
    funext x
    rw [Sobolev1JetLp.candidateWeakFDeriv, gradient_assembleSobolev1JetLp])⟩

end WeakDerivIdentification
end TauCeti
end
end
