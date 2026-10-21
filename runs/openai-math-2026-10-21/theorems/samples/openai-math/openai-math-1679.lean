namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid

lemma mpower0_21_r5_7_eq : ∀ k : Fin 16, mpower0_21Expr 5 7 k = mpower0_21_r5_7 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
