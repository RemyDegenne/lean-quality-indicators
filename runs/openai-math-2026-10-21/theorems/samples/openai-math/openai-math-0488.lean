namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma column4_0_r2_10_eq : ∀ k : Fin 16, column4_0Expr 2 10 k = column4_0_r2_10 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
