public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

open scoped NNReal

variable {K : Type*} [NontriviallyNormedField K] [NonarchimedeanRing K]

local notation "𝒯" => weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K))
  isWeightFamily_one_weight

local notation "T" => weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0

local notation "C" => weightedC (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight

variable (K) in
/-- **The smallest ring of integral elements of `K⟨T⟩` containing `K°`**: the integral closure of
`K° + K⟨T⟩°°` (Wedhorn, Remark 7.15 and Example 7.57). It lies in `K⟨T⟩°` but does not contain
`T` (`TauCeti.ValuationSpectrum.weightedX_notMem_closedDiscMinimalPlus`). -/
noncomputable def closedDiscMinimalPlus : Subring 𝒯 :=
  plusClosure (C '' Metric.closedBall 0 1)

end TauCeti.ValuationSpectrum
end
