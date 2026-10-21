namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma column13_0_r0_5_eq : ∀ k : Fin 16, column13_0Expr 0 5 k = column13_0_r0_5 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
