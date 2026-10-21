namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma trans1_r1_8_eq : ∀ k : Fin 16, trans1Expr 1 8 k = trans1_r1_8 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
