namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma trans25_r0_8_eq : ∀ k : Fin 16, trans25Expr 0 8 k = trans25_r0_8 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
