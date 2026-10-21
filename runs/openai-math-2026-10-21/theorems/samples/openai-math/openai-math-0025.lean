namespace OAI

namespace SharpPlanar.Bernstein37

open IntegerIntervals IntegerBasis Numerical CachedData

namespace N1_left

lemma t4_contains : t4.Contains (sourcePower true 37 (-1/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale (RBox.contains_add hm37_1_0_6.realContains tr4_contains) (1) 16 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]

end N1_left
end SharpPlanar.Bernstein37
end OAI
