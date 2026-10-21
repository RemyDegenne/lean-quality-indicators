namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact

lemma trans12_contains (j : Fin 6) (i k : Fin 16) :
    (trans12 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(12:ℕ))) := by
  rw [← trans12_eq]
  unfold trans12Expr
  convert exp_transformed_step (trans11_contains j i k) (transStep_contains j i k) using 1; norm_num

end SharpPlanar.CachedData
end OAI
