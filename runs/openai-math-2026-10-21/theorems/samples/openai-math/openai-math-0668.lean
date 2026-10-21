namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma trans17_r5_3_eq : ∀ k : Fin 16, trans17Expr 5 3 k = trans17_r5_3 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
