public section

open TauCeti

namespace WeierstrassCurve.Affine

variable {F K : Type*} [Field F] [Field K] [Algebra F K] (W : Affine F) (w : Place F K)

variable [DecidableEq K] [W.IsElliptic]

variable [DecidableEq F]

variable {w} (hw : w.degree = 1)

/-- **The reduction of points at a place of degree one**: each point of `W` over `K` goes to the
unique point of `W` over `F` it is congruent to modulo the kernel of reduction. It is additive
because that kernel is a subgroup. -/
noncomputable def reductionOfDegreeEqOne : (W⁄K).toAffine.Point →+ (W⁄F).toAffine.Point where
  toFun A := (exists_sub_mem_polePoints W w hw A).choose
  map_zero' := eq_of_sub_mem_polePoints W w (exists_sub_mem_polePoints W w hw 0).choose_spec
    (by rw [map_zero, sub_zero]; exact zero_mem _)
  map_add' A B := by
    refine eq_of_sub_mem_polePoints W w (exists_sub_mem_polePoints W w hw (A + B)).choose_spec ?_
    rw [map_add, add_sub_add_comm]
    exact add_mem (exists_sub_mem_polePoints W w hw A).choose_spec
      (exists_sub_mem_polePoints W w hw B).choose_spec

end WeierstrassCurve.Affine
end
