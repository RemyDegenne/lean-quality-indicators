namespace P2MW.S_MvFormalGroup_exists_hopfAlgebra_presentation_comul_eq_of_cocycle_of_powerDefect

attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

set_option maxHeartbeats 800000

set_option synthInstance.maxHeartbeats 80000

set_option Elab.async false

set_option linter.unusedSectionVars false

open scoped TensorProduct

open MvPowerSeries Function

universe u v w

noncomputable section

namespace S42LevelHopf

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]

section BaseChange

variable (𝓞) {σ : Type w} (E : Type v) [CommRing E] [Algebra 𝓞 E]

variable [Module.Free 𝓞 E] [Module.Finite 𝓞 E]

def coordSeries (k : Module.Free.ChooseBasisIndex 𝓞 E) : MvPowerSeries σ E →ₗ[𝓞] MvPowerSeries σ 𝓞 :=
  LinearMap.pi fun m : σ →₀ ℕ =>
    (Finsupp.lapply k).comp ((Module.Free.chooseBasis 𝓞 E).repr.toLinearMap.comp
      ((MvPowerSeries.coeff m).restrictScalars 𝓞))

end BaseChange
end S42LevelHopf
end
end P2MW.S_MvFormalGroup_exists_hopfAlgebra_presentation_comul_eq_of_cocycle_of_powerDefect
