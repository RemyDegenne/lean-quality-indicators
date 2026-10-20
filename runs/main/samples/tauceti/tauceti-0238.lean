public section

noncomputable section

open Complex Set

namespace TauCeti

variable {n : ℕ}

section FiniteLinearOrder

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

variable [LocallyFiniteOrder ι]

theorem schwarzChristoffelEdgeAngle_comp_strictMono (a e : ι → ℝ)
    (ha : StrictMono a) (he : ∀ i, e i < 0) :
    StrictMono (fun i ↦ schwarzChristoffelEdgeAngle a e (a i)) := by
  intro i j hij
  have hdiff := schwarzChristoffelEdgeAngle_sub_eq_neg_pi_mul_sum_Ioc a e ha hij.le
  have hsum : ∑ k ∈ Finset.Ioc i j, e k < 0 := by
    apply Finset.sum_neg
    · exact fun k _ ↦ he k
    · exact ⟨j, Finset.mem_Ioc.mpr ⟨hij, le_rfl⟩⟩
  nlinarith [Real.pi_pos]

end FiniteLinearOrder
end TauCeti
end
end
