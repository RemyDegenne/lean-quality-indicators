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

/-- Each source variable maps to an unweighted target coefficient variable. -/
def weightOneZeroCoefficientEmbedding (e : σ ↪ τ) (T : Set τ)
    (h : ∀ j : σ, e j ∉ T) (t : T) :
    σ ↪ WeightOneCoefficientVariables T t where
  toFun j := Sum.inl ⟨e j, h j⟩
  inj' := by
    intro a b hab
    exact e.injective (congrArg Subtype.val (Sum.inl.inj hab))

end MvPolynomial
end
