public section

open LinearMap Module

namespace CFSG.HardMathSupport.GuralnickMalle

variable {K E : Type*} [Field K] [CharP K 2] [AddCommGroup E] [Module K E]

@[simp] theorem siegelEquiv_apply (Qf : QuadraticForm K E) (a b : E)
    (ha : Qf a = 0) (hb : Qf b = 0) (hab : QuadraticMap.polarBilin Qf a b = 0)
    (c : K) (x : E) : siegelEquiv Qf a b ha hb hab c x = siegelLin Qf a b c x :=
  rfl

end CFSG.HardMathSupport.GuralnickMalle
end
