namespace OAI

namespace SharpPlanar.Bernstein24

open IntegerIntervals IntegerBasis Numerical CachedData

namespace N1_right

lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 24 (1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt (u := 9) (v := 1000) (bernsteinBox_contains ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)

end N1_right
end SharpPlanar.Bernstein24
end OAI
