namespace OAI

namespace SharpPlanar

open IntegerIntervals IntegerBasis

lemma coarse_12_19 : sharpTaylor 19 12/((Nat.factorial 19):ℝ)≤(385754412457415570392073:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]

end SharpPlanar
end OAI
