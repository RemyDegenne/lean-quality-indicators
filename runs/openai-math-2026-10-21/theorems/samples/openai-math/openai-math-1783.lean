namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma trans13_r4_1_eq : ∀ k : Fin 16, trans13Expr 4 1 k = trans13_r4_1 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
