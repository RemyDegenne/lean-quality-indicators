namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma ramifiedPart_norm_le (ν : EisensteinIdealExponent) :
    idealExponentNorm (ramifiedPart ν) ≤ idealExponentNorm ν := by
  simpa only [idealExponentNorm,normNat_cast] using
    norm_le_of_dvd (idealExponentGenerator_ne_zero ν)
      (idealExponentGenerator_dvd_of_le (ramifiedPart_le ν))

end CubicFirstMoment
end
end OAI
