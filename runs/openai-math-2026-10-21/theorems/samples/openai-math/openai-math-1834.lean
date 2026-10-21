namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma trans93_r3_eq (i k : Fin 16) : trans93Expr 3 i k = trans93_r3 i k := by
  fin_cases i
  · exact trans93_r3_0_eq k
  · exact trans93_r3_1_eq k
  · exact trans93_r3_2_eq k
  · exact trans93_r3_3_eq k
  · exact trans93_r3_4_eq k
  · exact trans93_r3_5_eq k
  · exact trans93_r3_6_eq k
  · exact trans93_r3_7_eq k
  · exact trans93_r3_8_eq k
  · exact trans93_r3_9_eq k
  · exact trans93_r3_10_eq k
  · exact trans93_r3_11_eq k
  · exact trans93_r3_12_eq k
  · exact trans93_r3_13_eq k
  · exact trans93_r3_14_eq k
  · exact trans93_r3_15_eq k

end SharpPlanar.CachedData
end OAI
