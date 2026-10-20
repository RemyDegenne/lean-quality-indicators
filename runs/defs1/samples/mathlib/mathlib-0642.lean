@[expose] public section

open CategoryTheory Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace CochainComplex

variable (R : Type*) [Ring R] (K L : CochainComplex C ℤ) (n m p : ℤ)

namespace HomComplex

/-- `CohomologyClass K L m` identifies to the cohomology of the
complex `linearHomComplex R K L` in degree `m`. -/
@[simps!, implicit_reducible]
noncomputable def linearLeftHomologyData [Linear R C] :
    ((linearHomComplex R K L).sc n).LeftHomologyData :=
  linearLeftHomologyData' R K L _ n _ (by simp) (by simp)

end HomComplex
end CochainComplex
end
