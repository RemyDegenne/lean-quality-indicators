namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma kernel96_1_r0_3_eq : ∀ k : Fin 16, kernel96_1Expr 0 3 k = kernel96_1_r0_3 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
