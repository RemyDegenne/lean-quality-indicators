namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid

lemma mpower0_15_r0_13_eq : ∀ k : Fin 16, mpower0_15Expr 0 13 k = mpower0_15_r0_13 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
