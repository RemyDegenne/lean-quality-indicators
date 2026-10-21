namespace OAI

namespace SharpPlanar.Bernstein31

open IntegerIntervals IntegerBasis Numerical CachedData

namespace N1_right

lemma t27_contains : t27.Contains (sourcePower true 31 (1/1) 2 27) := by
  apply RBox.contains_of_abs (sourcePower_of_cap true 31 (1/1) 2 27 coarse_31_29) <;> norm_num [t27,precision]

end N1_right
end SharpPlanar.Bernstein31
end OAI
