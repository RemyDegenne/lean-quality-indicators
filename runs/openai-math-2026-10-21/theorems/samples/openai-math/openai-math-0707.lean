namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma power93_r3_0_eq : ∀ k : Fin 16, power93Expr 3 0 k = power93_r3_0 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
