namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid

lemma mpower0_4_r5_10_eq : ∀ k : Fin 16, mpower0_4Expr 5 10 k = mpower0_4_r5_10 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
