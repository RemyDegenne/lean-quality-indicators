namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma power89_r5_15_eq : ∀ k : Fin 16, power89Expr 5 15 k = power89_r5_15 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
