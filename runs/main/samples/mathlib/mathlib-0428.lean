public section

open MeasureTheory Measure ProbabilityTheory

namespace ProbabilityTheory

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓧 : ι → Type*} {m𝓧 : ∀ i, MeasurableSpace (𝓧 i)} {X : Π i, Ω → 𝓧 i}

lemma iIndepFun.map_fun_eq_infinitePi_map₀' [Countable ι] (mX : ∀ i, AEMeasurable (X i) P)
    (h : iIndepFun X P) :
    P.map (fun ω i ↦ X i ω) = infinitePi (fun i ↦ P.map (X i)) :=
  h.map_fun_eq_infinitePi_map₀ <| aemeasurable_pi_iff.2 mX

end ProbabilityTheory
end
