namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma power48_r4_10_eq : ∀ k : Fin 16, power48Expr 4 10 k = power48_r4_10 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
