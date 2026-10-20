@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Subobject

open CategoryTheory.Preadditive CategoryTheory.Category CategoryTheory.Idempotents

open Opposite

open scoped Simplicial

noncomputable section

namespace AlgebraicTopology

namespace AlternatingFaceMapComplex

variable {C : Type*} [Category* C] [Preadditive C]

variable (X : SimplicialObject C)

variable (Y : SimplicialObject C)

variable {X} {Y}

/-- The alternating face map complex, on morphisms -/
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
  ChainComplex.ofHom (fun n => f.app (op ⦋n⦌)) fun n => by
    simp only [obj, ChainComplex.of_d, objD, Int.reduceNeg]
    rw [comp_sum, sum_comp]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [comp_zsmul, zsmul_comp]
    congr 1
    symm
    apply f.naturality

end AlternatingFaceMapComplex
end AlgebraicTopology
end
end
