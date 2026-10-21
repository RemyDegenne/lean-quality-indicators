namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma power26_r1_9_eq : ∀ k : Fin 16, power26Expr 1 9 k = power26_r1_9 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
