@[expose] public section

open Complex Set Metric Filter Topology

namespace RectHomotopyProof

lemma continuousOn_arg_w :
    ContinuousOn (fun t => Complex.arg (fdPolygon t - refP₀))
      (Icc 0 5 \ {tL refP₀}) :=
  ContinuousOn.comp Complex.continuousOn_arg continuous_w.continuousOn
    (fun t ht => fdPolygon_sub_ref_p₀_mem_slitPlane t ht.1 (Set.notMem_singleton_iff.mp ht.2))

end RectHomotopyProof
end
