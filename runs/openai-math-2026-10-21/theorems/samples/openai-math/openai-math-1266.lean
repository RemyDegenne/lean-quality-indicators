namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma column21_1_r3_11_eq : ∀ k : Fin 16, column21_1Expr 3 11 k = column21_1_r3_11 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
