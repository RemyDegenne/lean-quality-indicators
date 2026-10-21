namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma trans12_r1_9_eq : ∀ k : Fin 16, trans12Expr 1 9 k = trans12_r1_9 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
