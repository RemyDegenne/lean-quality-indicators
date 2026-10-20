@[expose] public section

open Opposite

open CategoryTheory

open CategoryTheory.Limits CategoryTheory.Functor

universe v u v' u'

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

namespace SimplicialObject

set_option quotPrecheck false in
scoped[Simplicial]
  notation3:1000 X " _⦋" n "⦌" =>
      (X : CategoryTheory.SimplicialObject _).obj (Opposite.op (SimplexCategory.mk n))

open Simplicial

variable {C}

variable (X : SimplicialObject C)

@[reassoc]
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ Fin.castSucc j) :
    X.σ j.succ ≫ X.δ (Fin.castSucc i) = X.δ i ≫ X.σ j := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_le H]

end SimplicialObject
end CategoryTheory
end
