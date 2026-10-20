@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory

open HomologicalComplex HomologySequence

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}
  (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)

namespace ShortComplex

namespace ShortExact

/-- The connecting homomorphism `S.X₃.homology i ⟶ S.X₁.homology j` for a short exact
short complex `S`. -/
noncomputable def δ : S.X₃.homology i ⟶ S.X₁.homology j := (snakeInput hS i j hij).δ

end ShortExact
end ShortComplex
end CategoryTheory
end
