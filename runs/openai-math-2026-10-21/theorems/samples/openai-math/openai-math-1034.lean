namespace OAI

section

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace SKRatio.Fields

open Real Matrix TwoSpin

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

lemma heatBathLinear_const (g : Disorder n) (h : Fin n→ℝ) (c : ℝ) :
    heatBathLinear g h (fun _=>c)=0 := by
  funext x
  simp only [heatBathLinear,heatBathGenerator,LinearMap.coe_mk,AddHom.coe_mk,
    conditionalExpectation_const,sub_self,Finset.sum_const_zero,Pi.zero_apply]

end SKRatio.Fields
end
end
end OAI
