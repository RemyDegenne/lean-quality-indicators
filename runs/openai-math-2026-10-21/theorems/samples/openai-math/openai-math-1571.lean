namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid Numerical

lemma hk19_0_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_25 j i k).Contains (fullFactor false 19 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 25 (power19_contains j i k) (mpower0_25_contains j i k)

end SharpPlanar.CachedData
end OAI
