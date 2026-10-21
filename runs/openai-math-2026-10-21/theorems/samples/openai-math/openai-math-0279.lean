namespace OAI

noncomputable section

open MeasureTheory Complex SchwartzMap

open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

namespace ElasticityBessel

lemma norm2_nonneg (f : S) : 0 ≤ norm2 f := norm_nonneg _

end ElasticityBessel
end
end OAI
