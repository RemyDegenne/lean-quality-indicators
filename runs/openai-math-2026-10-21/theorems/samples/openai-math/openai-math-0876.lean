namespace OAI

namespace SharpPlanar.Bernstein36

open IntegerIntervals IntegerBasis Numerical CachedData

namespace N1_right

lemma t24_contains : t24.Contains (sourcePower true 36 (1/2) 2 24) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 36 (1/2) 2 24 coarse_36_26) <;> norm_num [t24,precision]

end N1_right
end SharpPlanar.Bernstein36
end OAI
