namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma kernel97_1_r5_15_eq : ∀ k : Fin 16, kernel97_1Expr 5 15 k = kernel97_1_r5_15 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
