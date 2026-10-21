namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid

lemma mpower0_17_r2_5_eq : ∀ k : Fin 16, mpower0_17Expr 2 5 k = mpower0_17_r2_5 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
