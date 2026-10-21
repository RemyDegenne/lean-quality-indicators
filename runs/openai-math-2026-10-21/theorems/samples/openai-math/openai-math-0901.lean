namespace OAI

namespace SharpPlanar.Bernstein21

open IntegerIntervals IntegerBasis Numerical CachedData

namespace N0_right

lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 21 (3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)

end N0_right
end SharpPlanar.Bernstein21
end OAI
