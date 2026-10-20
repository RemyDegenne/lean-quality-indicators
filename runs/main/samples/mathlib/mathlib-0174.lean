@[expose] public section

universe u

open CategoryTheory

open scoped Simplicial

namespace SSet

lemma δ_opObjEquiv (X : SSet.{u}) {n : ℕ} (i : Fin (n + 2)) (x : X.op _⦋n + 1⦌) :
    X.δ i (opObjEquiv x) = opObjEquiv (X.op.δ i.rev x) := by
  simp

end SSet
end
