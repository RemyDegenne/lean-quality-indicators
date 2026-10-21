namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma power57_r3_15_eq : ∀ k : Fin 16, power57Expr 3 15 k = power57_r3_15 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
