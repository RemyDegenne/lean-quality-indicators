namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma kernel64_1_r3_0_eq : ∀ k : Fin 16, kernel64_1Expr 3 0 k = kernel64_1_r3_0 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
