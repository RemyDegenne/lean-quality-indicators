namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma power76_r2_2_eq : ∀ k : Fin 16, power76Expr 2 2 k = power76_r2_2 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
