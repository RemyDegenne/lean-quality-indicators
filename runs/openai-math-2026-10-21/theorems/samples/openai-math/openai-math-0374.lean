namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma kernel60_1_r3_13_eq : ∀ k : Fin 16, kernel60_1Expr 3 13 k = kernel60_1_r3_13 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
