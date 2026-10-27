@[expose] public section

open TauCeti.DavisKahan.Sylvester

namespace TauCeti

namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open Set

open scoped InnerProductSpace unitInterval

universe v

section SpectralContinuation

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

namespace SpectralContinuationWitness

variable {A V : H →L[ℂ] H} {s : Set ℝ}

/-- The endpoint separation witness at the perturbed operator. -/
noncomputable def targetSeparatingContour
    (C : SpectralContinuationWitness A V s) :
    SpectralSeparatingContour (A + V) s := by
  let ht : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  let Γ := C.separating 1 ht
  refine
    { geometric := C.contour
      selfAdjoint := ?_
      measurable_selected := Γ.measurable_selected
      spectralMargin := Γ.spectralMargin
      spectralMargin_pos := Γ.spectralMargin_pos
      spectrum_separated := ?_
      winding_selected := ?_
      winding_complement := ?_ }
  · simpa only [operatorPath_one] using Γ.selfAdjoint
  · intro t lam hlam
    rw [← C.geometric_eq 1 ht]
    exact Γ.spectrum_separated t lam (by simpa only [operatorPath_one] using hlam)
  · intro lam hlam hls
    rw [← C.geometric_eq 1 ht]
    exact Γ.winding_selected lam (by simpa only [operatorPath_one] using hlam) hls
  · intro lam hlam hls
    rw [← C.geometric_eq 1 ht]
    exact Γ.winding_complement lam (by simpa only [operatorPath_one] using hlam) hls

end SpectralContinuationWitness
end SpectralContinuation
end DavisKahanExt
end TauCeti
end
