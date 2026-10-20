@[expose] public section

open scoped WithZero

universe u v w z

namespace MvPolynomial

variable {σ : Type u} {τ : Type v}

variable {k : Type w} {l : Type z} [Field k] [Field l]

local notation3 "ratio[" F "," U "," pivot "](" j ")" =>
  (algebraMap (MvPolynomial (WeightOneCoefficientVariables U pivot) F)
    (WeightOneCoefficientField F U pivot) (X (Sum.inr j)))

local notation3 "unweighted[" F "," U "," pivot "](" j ")" =>
  (algebraMap (MvPolynomial (WeightOneCoefficientVariables U pivot) F)
    (WeightOneCoefficientField F U pivot) (X (Sum.inl j)))

@[simp] theorem weightOneZeroCoefficientFieldMap_C (g : k →+* l) (e : σ ↪ τ)
    (T : Set τ) (h : ∀ j : σ, e j ∉ T) (t : T) (a : k) :
    weightOneZeroCoefficientFieldMap g e T h t
      (algebraMap (MvPolynomial σ k) (FractionRing (MvPolynomial σ k)) (C a)) =
      algebraMap (MvPolynomial (WeightOneCoefficientVariables T t) l)
        (WeightOneCoefficientField l T t) (C (g a)) := by
  simp [weightOneZeroCoefficientFieldMap]

end MvPolynomial
end
