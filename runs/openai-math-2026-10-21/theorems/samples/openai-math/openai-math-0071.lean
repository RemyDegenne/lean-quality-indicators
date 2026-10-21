namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma power98_r0_4_eq : ∀ k : Fin 16, power98Expr 0 4 k = power98_r0_4 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
