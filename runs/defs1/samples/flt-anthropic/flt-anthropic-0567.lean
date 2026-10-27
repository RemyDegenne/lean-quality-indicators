set_option autoImplicit false

namespace NumberField.AdelicTrace

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicBox
  Topology Filter Set

open scoped nonZeroDivisors

variable (F : Type) [Field F] [NumberField F]

variable {F}

noncomputable section

section Trace

open Topology Filter

variable (F : Type) [Field F] [NumberField F]

def traceInt : (Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F)
    →+ (Π w : HeightOneSpectrum (𝓞 ℚ), w.adicCompletionIntegers ℚ) where
  toFun := (di F).extend (f₀ F)
  map_zero' := by
    have := (di F).extend_eq (continuous_f₀ F) (0 : S F)
    simpa using this
  map_add' := by
    have hc : Continuous ((di F).extend (f₀ F)) := (di F).continuous_extend (tendsto_f₀ F)
    intro x y
    refine DenseRange.induction_on₂ (p := fun x y => (di F).extend (f₀ F) (x + y)
        = (di F).extend (f₀ F) x + (di F).extend (f₀ F) y) (dense_S F).denseRange_val ?_ ?_ x y
    · exact isClosed_eq (hc.comp (continuous_fst.add continuous_snd))
        ((hc.comp continuous_fst).add (hc.comp continuous_snd))
    · intro s t
      rw [← AddSubgroup.coe_add, (di F).extend_eq (continuous_f₀ F), (di F).extend_eq (continuous_f₀ F),
        (di F).extend_eq (continuous_f₀ F), map_add]

end Trace
end
end NumberField.AdelicTrace
