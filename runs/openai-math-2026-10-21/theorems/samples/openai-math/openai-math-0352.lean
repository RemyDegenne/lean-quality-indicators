namespace OAI

namespace SharpPlanar.Bernstein31

open IntegerIntervals IntegerBasis Numerical CachedData

namespace N1_left

lemma t9_contains : t9.Contains (sourcePower true 31 (-3/2) 2 9) := by
  rw [← t9_checked]
  convert RBox.contains_scale (RBox.contains_add hm31_1_0_11.realContains tr9_contains) (-19683) 512 (by norm_num) using 1
  norm_num [sourcePower,normalizedH]

end N1_left
end SharpPlanar.Bernstein31
end OAI
