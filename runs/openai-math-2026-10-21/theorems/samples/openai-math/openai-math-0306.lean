namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma power23_r3_9_eq : ∀ k : Fin 16, power23Expr 3 9 k = power23_r3_9 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
