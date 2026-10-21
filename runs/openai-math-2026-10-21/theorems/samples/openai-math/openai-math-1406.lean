namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma kernel16_1_r5_12_eq : ∀ k : Fin 16, kernel16_1Expr 5 12 k = kernel16_1_r5_12 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
