namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid

lemma mpower0_5_eq (j : Fin 6) (i k : Fin 16) : mpower0_5Expr j i k = mpower0_5 j i k := by
  fin_cases j
  · exact mpower0_5_r0_eq i k
  · exact mpower0_5_r1_eq i k
  · exact mpower0_5_r2_eq i k
  · exact mpower0_5_r3_eq i k
  · exact mpower0_5_r4_eq i k
  · exact mpower0_5_r5_eq i k

end SharpPlanar.CachedData
end OAI
