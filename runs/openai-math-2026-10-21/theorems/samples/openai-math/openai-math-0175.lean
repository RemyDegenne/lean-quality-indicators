namespace OAI

universe u1 u2

namespace QuadricCounterexample

open MvPolynomial

noncomputable section

lemma affineLinear_regular_variable (a b : ℂ) : (1 : Fin 2) ∉ (affineLinear a b).vars := by
  intro h
  have hf := vars_add_subset (C a*X (0 : Fin 2)) (C b)
  have hg := vars_mul (C a : BPoly) (X 0)
  simp only [vars_C,vars_X,Finset.empty_union] at hg
  simp only [vars_C,Finset.union_empty] at hf
  have : (1 : Fin 2) ∈ ({0} : Finset (Fin 2)) := hg (hf h)
  norm_num at this

end
end QuadricCounterexample
end OAI
