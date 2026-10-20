public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {T α : Type*} [MeasurableSpace T] [MeasurableSpace α]

variable {π : Measure T} {P : T → ProbabilityMeasure α}

theorem pathLaw_iidMixtureLaw (hP : Measurable P) :
    pathLaw (iidMixtureLaw π P) (fun n ω => ω.2 n)
      = (π.map P).bind fun Q => Measure.infinitePi fun _ : ℕ => (Q : Measure α) := by
  rw [pathLaw_def, iidMixtureLaw_def, TauCeti.MeasureTheory.map_bind
    (TauCeti.MeasureTheory.measurable_dirac_prod_infinitePi_const P hP).aemeasurable
    measurable_snd]
  simp only [Measure.map_snd_prod, measure_univ, one_smul]
  exact (TauCeti.MeasureTheory.bind_map hP.aemeasurable
    TauCeti.MeasureTheory.measurable_infinitePi_const.aemeasurable).symm

end Probability
end TauCeti
end
end
