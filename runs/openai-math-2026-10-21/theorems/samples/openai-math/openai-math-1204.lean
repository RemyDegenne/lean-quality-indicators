namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder

open Matrix

namespace BinaryCoordinateSweeps.Signed

open Density Irrep Representation

variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

lemma actionMatrix_mul (p : A → Bool) (g h : Equiv.Perm (Fin n)) :
    actionMatrix p (g*h)=actionMatrix p g*actionMatrix p h := by
  change LinearMap.toMatrix' ((tensorRep p n) (g*h))=_
  rw [map_mul]
  exact LinearMap.toMatrix'_comp _ _

end BinaryCoordinateSweeps.Signed
end
end
end OAI
