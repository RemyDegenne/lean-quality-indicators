namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma kernel81_1_r3_8_eq : ∀ k : Fin 16, kernel81_1Expr 3 8 k = kernel81_1_r3_8 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
