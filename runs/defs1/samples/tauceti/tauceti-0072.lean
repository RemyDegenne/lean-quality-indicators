public section

namespace TauCeti

open AddMonoidAlgebra CategoryTheory CategoryTheory.Abelian

universe w v uk uA u v' t

section Bigraded

variable {C : Type u} [Category.{v'} C] [Abelian C]
  {k : Type t} [Field k] [Linear k C] [HasExt.{w} C] {e : C ≌ C} {X Y : C} {I : Type*}

variable (S : I → C) in
/-- The **full bigraded Ext Poincaré matrix** of a family, truncated below a common
cohomological degree `b`. Its `(i,j)` entry records all dimensions
`dim_k Ext^n(S_i,S_j{p})`, not only the diagonal terms `n = p`. -/
noncomputable def bigradedExtPoincareMatrix
    (h : ∀ i j, IsGradedExtInternallyFinite.{w} k e (S i) (S j))
    (b : ℕ) : Matrix I I Bigraded.Series :=
  fun i j ↦ bigradedExtPoincareSeries.{w} k e (h i j) b

end Bigraded
end TauCeti
end
