namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma column25_1_r1_3_eq : ∀ k : Fin 16, column25_1Expr 1 3 k = column25_1_r1_3 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
