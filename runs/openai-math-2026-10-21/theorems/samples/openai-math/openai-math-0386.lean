namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma trans2_r2_0_eq : ∀ k : Fin 16, trans2Expr 2 0 k = trans2_r2_0 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
