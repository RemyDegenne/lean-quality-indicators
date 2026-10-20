@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits SimplexCategory
  SimplicialObject Opposite CategoryTheory.Idempotents

open scoped Simplicial DoldKan

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category* C] [Preadditive C] (K K' : ChainComplex C ℕ) (f : K ⟶ K')
  {Δ Δ' Δ'' : SimplexCategory}

namespace Γ₀

namespace Obj

/-- In the definition of `(Γ₀.obj K).obj Δ` as a direct sum indexed by `A : Splitting.IndexSet Δ`,
the summand `summand K Δ A` is `K.X A.1.len`. -/
def summand (Δ : SimplexCategoryᵒᵖ) (A : Splitting.IndexSet Δ) : C :=
  K.X A.1.unop.len

end Obj
end Γ₀
end DoldKan
end AlgebraicTopology
end
end
