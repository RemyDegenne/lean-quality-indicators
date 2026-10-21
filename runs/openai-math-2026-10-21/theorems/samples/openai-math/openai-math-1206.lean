namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma kernel33_1_r5_0_eq : ∀ k : Fin 16, kernel33_1Expr 5 0 k = kernel33_1_r5_0 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
