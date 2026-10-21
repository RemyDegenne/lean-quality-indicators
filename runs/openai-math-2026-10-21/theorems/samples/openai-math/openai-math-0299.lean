namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma power26_r4_0_eq : ∀ k : Fin 16, power26Expr 4 0 k = power26_r4_0 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
