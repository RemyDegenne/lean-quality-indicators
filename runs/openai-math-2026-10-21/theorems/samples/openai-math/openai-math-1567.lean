namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid

lemma mpower0_8_r2_15_eq : ∀ k : Fin 16, mpower0_8Expr 2 15 k = mpower0_8_r2_15 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
