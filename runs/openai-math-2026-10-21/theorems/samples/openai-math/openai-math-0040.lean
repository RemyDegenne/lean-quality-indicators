namespace OAI

namespace SharpPlanar.Bernstein7

open IntegerIntervals IntegerBasis Numerical CachedData

namespace N0_left

lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 7 (-3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)

end N0_left
end SharpPlanar.Bernstein7
end OAI
