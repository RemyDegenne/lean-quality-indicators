namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma power64_r3_13_eq : ∀ k : Fin 16, power64Expr 3 13 k = power64_r3_13 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
