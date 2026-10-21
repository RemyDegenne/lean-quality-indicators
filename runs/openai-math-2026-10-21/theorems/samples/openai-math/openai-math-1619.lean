namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma kernel45_1_r4_11_eq : ∀ k : Fin 16, kernel45_1Expr 4 11 k = kernel45_1_r4_11 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
