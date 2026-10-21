namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma power59_r5_0_eq : ∀ k : Fin 16, power59Expr 5 0 k = power59_r5_0 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
