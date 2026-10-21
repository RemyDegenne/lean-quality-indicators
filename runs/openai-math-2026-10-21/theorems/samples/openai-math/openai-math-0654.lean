namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid Numerical

lemma ha25_0_30_eq (j : Fin 7) : ha25_0_30 j = ((ha25_0_29 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 30 := by fin_cases j <;> decide +kernel

end SharpPlanar.CachedData
end OAI
