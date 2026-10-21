namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma column81_1_r0_5_eq : ∀ k : Fin 16, column81_1Expr 0 5 k = column81_1_r0_5 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
