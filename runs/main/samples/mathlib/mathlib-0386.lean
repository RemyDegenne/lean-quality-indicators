@[expose] public section

open Set Function Filter MeasureTheory MeasureTheory.Measure TopologicalSpace

open ContinuousLinearMap Metric Topology

open scoped Pointwise NNReal Filter

universe u𝕜 uG uE uE' uE'' uF uF' uF'' uP

variable {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {E'' : Type uE''} {F : Type uF}
  {F' : Type uF'} {F'' : Type uF''} {P : Type uP}

variable [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedAddCommGroup E'']
  [NormedAddCommGroup F] {f f' : G → E} {g g' : G → E'} {x x' : G} {y : E}

namespace MeasureTheory

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜]

variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 E''] [NormedSpace 𝕜 F]

variable (L : E →L[𝕜] E' →L[𝕜] F)

section Measurability

variable [MeasurableSpace G] {μ ν : Measure G}

section ConvolutionExists

section CommGroup

variable [AddCommGroup G]

section MeasurableGroup

variable [MeasurableNeg G] [IsAddLeftInvariant μ]

variable {L} [MeasurableAdd G] [IsNegInvariant μ]

theorem convolutionExistsAt_iff_integrable_swap :
    ConvolutionExistsAt f g x L μ ↔ Integrable (fun t => L (f (x - t)) (g t)) μ :=
  convolutionExistsAt_flip.symm

end MeasurableGroup
end CommGroup
end ConvolutionExists
end Measurability
end NontriviallyNormedField
end MeasureTheory
end
