namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma column21_0_r5_7_eq : ∀ k : Fin 16, column21_0Expr 5 7 k = column21_0_r5_7 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
