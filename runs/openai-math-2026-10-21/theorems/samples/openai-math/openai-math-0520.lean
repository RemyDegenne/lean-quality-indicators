namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma column7_1_r5_1_eq : ∀ k : Fin 16, column7_1Expr 5 1 k = column7_1_r5_1 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
