@[expose] public section

open Real Set Filter Bornology NNReal ENNReal

open scoped Uniformity

noncomputable section

variable (p : ℝ≥0∞) (𝕜 α β : Type*)

namespace WithLp

section Aux

variable [hp : Fact (1 ≤ p)]

attribute [local instance] WithLp.prodPseudoEMetricAux

variable {α β}

variable (α β)

/-- Endowing the space `WithLp p (α × β)` with the `L^p` pseudometric structure. This definition is
not satisfactory, as it does not register the fact that the topology, the uniform structure, and the
bornology coincide with the product ones. Therefore, we do not register it as an instance. Using
this as a temporary pseudoemetric space instance, we will show that the uniform structure is equal
(but not defeq) to the product one, and then register an instance in which we replace the uniform
structure and the bornology by the product ones using this pseudometric space,
`PseudoMetricSpace.replaceUniformity`, and `PseudoMetricSpace.replaceBornology`.

See note [reducible non-instances] -/
abbrev prodPseudoMetricAux [PseudoMetricSpace α] [PseudoMetricSpace β] :
    PseudoMetricSpace (WithLp p (α × β)) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist
    (fun f g => by
      rcases p.dichotomy with (rfl | h)
      · simp [prod_dist_eq_sup]
      · simp only [dist, one_div, dite_eq_ite]
        split_ifs with hp' <;> positivity)
    fun f g => by
    rcases p.dichotomy with (rfl | h)
    · refine ENNReal.eq_of_forall_le_nnreal_iff fun r ↦ ?_
      simp [prod_edist_eq_sup, prod_dist_eq_sup]
    · have : 0 < p.toReal := by rw [ENNReal.toReal_pos_iff_ne_top]; rintro rfl; norm_num at h
      simp only [prod_edist_eq_add, edist_dist, one_div, prod_dist_eq_add, this]
      rw [← ENNReal.ofReal_rpow_of_nonneg, ENNReal.ofReal_add, ← ENNReal.ofReal_rpow_of_nonneg,
        ← ENNReal.ofReal_rpow_of_nonneg] <;> simp [Real.rpow_nonneg, add_nonneg]

end Aux
end WithLp
end
end
