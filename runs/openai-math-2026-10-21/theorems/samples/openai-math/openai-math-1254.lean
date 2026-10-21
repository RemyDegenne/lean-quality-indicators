namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid

lemma mpower1_5_r3_3_eq : ∀ k : Fin 16, mpower1_5Expr 3 3 k = mpower1_5_r3_3 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
