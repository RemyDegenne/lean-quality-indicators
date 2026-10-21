namespace OAI

open MeasureTheory Set

open scoped ENNReal BigOperators

open MeasureTheory Set Filter

open scoped ENNReal Topology Classical

namespace StandardMapEntropy

lemma sampleLaw_dilate (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 0<n) :
    (sampleLaw k hk n hn).map arrayDilate=sampleLaw k hk (n+n) (by omega) := by
  unfold sampleLaw
  rw [Measure.map_map continuous_arrayDilate.measurable (continuous_sampleArray k hk n hn).measurable]
  congr 1
  funext z
  exact sampleArray_dilate k hk z n hn

end StandardMapEntropy
end OAI
