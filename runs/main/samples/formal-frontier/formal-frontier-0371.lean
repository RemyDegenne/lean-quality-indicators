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

@[simp] theorem weightOneCoefficientChangePivot_C (T : Set τ) (t t' : T) (a : l) :
    weightOneCoefficientChangePivot (l := l) T t t'
      (algebraMap (MvPolynomial (WeightOneCoefficientVariables T t) l)
        (WeightOneCoefficientField l T t) (C a)) =
      algebraMap (MvPolynomial (WeightOneCoefficientVariables T t') l)
        (WeightOneCoefficientField l T t') (C a) := by
  apply weightOneCoefficientChangePivot_of_sections
  rw [weightOneCoefficientSection_C_val, weightOneCoefficientSection_C_val]

end MvPolynomial
end
