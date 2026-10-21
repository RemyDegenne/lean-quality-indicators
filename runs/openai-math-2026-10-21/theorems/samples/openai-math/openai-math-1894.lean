namespace OAI

namespace SharpPlanar.IntegerCompact

open IntegerIntervals

lemma weight54_contains : weight54.Contains (fejerWeight 54) := by
  have he : weightBoxCalc 54 = weight54 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 54

end SharpPlanar.IntegerCompact
end OAI
