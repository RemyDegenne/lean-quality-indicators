public section

universe v u

namespace TauCeti

open CategoryTheory

namespace PeriodicComplex

open HomologicalComplex

variable (C : Type u) [Category.{v} C] [Preadditive C] (n : ℕ)

@[expose] public section

attribute [local simp] XIsoOfEq_hom_naturality

/-- The compatibility of the shift functors with the addition of integers. -/
@[implicit_reducible, simps!]
def shiftFunctorAdd' (k₁ k₂ k₁₂ : ℤ) (h : k₁ + k₂ = k₁₂) :
    shiftFunctor C n k₁₂ ≅ shiftFunctor C n k₁ ⋙ shiftFunctor C n k₂ :=
  NatIso.ofComponents (fun K => Hom.isoOfComponents
    (fun i => shiftFunctorObjXIso K k₁₂ i (i + k₂ + k₁) (by subst h; push_cast; ring))
    (fun _ _ _ => by subst h; simp [Int.negOnePow_add, smul_smul, mul_comm k₁.negOnePow]))
    (fun _ ↦ by ext; simp)

end
end PeriodicComplex
end TauCeti
end
