@[expose] public section

open Set

open scoped ENNReal Pointwise

universe u v w

variable (M : Type u) (G : Type v) (X : Type w)

export IsIsometricSMul (isometry_smul)

export IsIsometricVAdd (isometry_vadd)

variable {M G X}

@[to_additive (attr := simp)]
theorem diam_smul [PseudoMetricSpace X] [SMul M X] [IsIsometricSMul M X] (c : M) (s : Set X) :
    Metric.diam (c • s) = Metric.diam s :=
  (isometry_smul _ _).diam_image s

end
