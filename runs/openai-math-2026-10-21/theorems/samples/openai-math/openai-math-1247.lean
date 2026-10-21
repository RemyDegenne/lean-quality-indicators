namespace OAI

namespace SharpPlanar

namespace IntegerRoots

open IntegerIntervals

lemma root1001_contains : root1001.Contains (rootPhase 1001) := by
  have hh := CBox.mul_contains mid1001_contains root1_contains (c:=root1001) (by decide +kernel)
  simpa only [← rootPhase_add] using hh

end IntegerRoots
end SharpPlanar
end OAI
