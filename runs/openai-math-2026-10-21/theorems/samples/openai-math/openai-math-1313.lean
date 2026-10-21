namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma trans22_r3_8_eq : ∀ k : Fin 16, trans22Expr 3 8 k = trans22_r3_8 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
