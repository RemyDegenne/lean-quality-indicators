namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma trans22_r1_1_eq : ∀ k : Fin 16, trans22Expr 1 1 k = trans22_r1_1 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
