@[expose] public section

open CategoryTheory Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

namespace CochainComplex.HomComplex

namespace Cochain

variable (γ γ₁ γ₂ : Cochain K L n)

variable (K L)

variable (n)

variable {K L n}

@[simp]
lemma leftUnshift_neg {n' a : ℤ} (γ : Cochain (K⟦a⟧) L n') (n : ℤ) (hn : n + a = n') :
    (-γ).leftUnshift n hn = -γ.leftUnshift n hn := by
  change (leftShiftAddEquiv K L n a n' hn).symm (-γ) = _
  apply map_neg

end Cochain
end CochainComplex.HomComplex
end
