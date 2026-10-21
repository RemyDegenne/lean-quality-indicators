namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma trans21_r1_4_eq : ∀ k : Fin 16, trans21Expr 1 4 k = trans21_r1_4 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
