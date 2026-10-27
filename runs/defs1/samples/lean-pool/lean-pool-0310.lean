@[expose] public section

open MeasureTheory Real Set

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] --[MeasurableSingletonClass S]
  [MeasurableSpace T] --[MeasurableSingletonClass T]
  [MeasurableSpace U]

section measureEntropy

variable {μ : Measure S}

@[inherit_doc measureEntropy] notation:100 "Hm[" μ "]" => measureEntropy μ

/--
TODO: replace FiniteSupport hypotheses ∈ these files with FiniteEntropy hypotheses.
-/
noncomputable def FiniteEntropy (μ : Measure S := by volume_tac) : Prop :=
  Summable (fun s ↦ negMulLog (((μ Set.univ)⁻¹ • μ) {s}).toReal) ∧
  ∃ A : Set S, Countable A ∧ μ Aᶜ = 0

end measureEntropy
end ProbabilityTheory
end
