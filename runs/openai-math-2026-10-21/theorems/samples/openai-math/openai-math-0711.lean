namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma trans15_r1_13_eq : ∀ k : Fin 16, trans15Expr 1 13 k = trans15_r1_13 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
