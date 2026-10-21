namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid

lemma mpower1_15_r2_6_eq : ∀ k : Fin 16, mpower1_15Expr 2 6 k = mpower1_15_r2_6 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
