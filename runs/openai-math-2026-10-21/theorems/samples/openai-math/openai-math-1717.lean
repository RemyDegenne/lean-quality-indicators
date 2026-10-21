namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid Numerical

lemma ha24_1_18_contains (j : Fin 7) : (ha24_1_18 j).Contains (fullFactor true 24 18 ((j.val:ℝ)/6)) := by
  rw [ha24_1_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_17 j) true 24 17 j (ha24_1_17_contains j)

end SharpPlanar.CachedData
end OAI
