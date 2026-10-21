namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma kernel91_1_r4_2_eq : ∀ k : Fin 16, kernel91_1Expr 4 2 k = kernel91_1_r4_2 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
