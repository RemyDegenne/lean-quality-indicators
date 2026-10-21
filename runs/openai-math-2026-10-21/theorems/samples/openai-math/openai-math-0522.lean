namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma kernel100_0_r0_10_eq : ∀ k : Fin 16, kernel100_0Expr 0 10 k = kernel100_0_r0_10 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
