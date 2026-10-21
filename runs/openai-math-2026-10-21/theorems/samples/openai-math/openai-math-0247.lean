namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma trans89_r2_0_eq : ∀ k : Fin 16, trans89Expr 2 0 k = trans89_r2_0 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
