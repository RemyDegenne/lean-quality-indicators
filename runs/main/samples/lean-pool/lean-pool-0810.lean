@[expose] public section

open CategoryTheory AlgebraicTopology Limits TopologicalSpace

open SphereOddDegree.AffineBarycentricSubdivision

noncomputable section

namespace SphereOddDegree

theorem circF_comp_fst :
    (mvShortComplex ℤ circU circV circUV_top).f ≫ biprod.fst
      = mvInclUVU ℤ circU circV := by
  simp [mvShortComplex, mvLeftChainMap]

end SphereOddDegree
end
end
