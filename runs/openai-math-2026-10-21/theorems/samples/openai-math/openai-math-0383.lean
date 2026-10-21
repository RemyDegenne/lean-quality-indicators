namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma power90_r0_15_eq : ∀ k : Fin 16, power90Expr 0 15 k = power90_r0_15 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
