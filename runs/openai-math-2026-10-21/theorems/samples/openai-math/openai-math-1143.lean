namespace OAI

namespace SharpPlanar.Bernstein36

open IntegerIntervals IntegerBasis Numerical CachedData

namespace N1_left

lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)

end N1_left
end SharpPlanar.Bernstein36
end OAI
