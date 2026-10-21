namespace OAI

namespace SharpPlanar.Numerical.U43

open IntegerIntervals IntegerBasis IntegerGrid CachedData

lemma wuminus_contains (i : Fin 6) (j : Fin 2) : (wuminusBox i j).Contains ((Wminus*umat) i j) := matrixMulBox_contains WminusBox_contains entries_contains i j

end SharpPlanar.Numerical.U43
end OAI
