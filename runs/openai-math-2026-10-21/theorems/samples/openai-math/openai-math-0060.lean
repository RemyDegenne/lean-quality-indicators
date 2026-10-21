namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma power73_r2_9_eq : ∀ k : Fin 16, power73Expr 2 9 k = power73_r2_9 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
