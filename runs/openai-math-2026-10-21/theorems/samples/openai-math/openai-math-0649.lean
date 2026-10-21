namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid

lemma mpower1_14_r1_10_eq : ∀ k : Fin 16, mpower1_14Expr 1 10 k = mpower1_14_r1_10 k := by decide +kernel

end SharpPlanar.CachedData
end OAI
