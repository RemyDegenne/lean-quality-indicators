@[expose] public section

universe u v w w₁

namespace Subcoalgebra

variable {K : Type u} {C : Type v} {C' : Type w}

variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

variable [AddCommGroup C'] [Module K C'] [Coalgebra K C']

theorem equivMapOfInjOn_symm_apply_eq (f : C →ₗc[K] C') (D : Subcoalgebra K C)
    (hf : Set.InjOn f (D : Set C)) (y : map f D) (x : D)
    (hxy : f (x : C) = (y : C')) :
    (equivMapOfInjOn f D hf).symm y = x := by
  apply Subtype.ext
  apply hf ((equivMapOfInjOn f D hf).symm y).property x.property
  exact (map_equivMapOfInjOn_symm_apply f D hf y).trans hxy.symm

end Subcoalgebra
end
