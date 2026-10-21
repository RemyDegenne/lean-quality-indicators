namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma power15_r0_8_eq : ∀ k : Fin 16, power15Expr 0 8 k = power15_r0_8 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
