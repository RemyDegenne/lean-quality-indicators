@[expose] public section

namespace Stafford38.WeylSymplectic

open Stafford

open AlgebraicAnalysis

noncomputable section

universe u

variable (k : Type u) [Field k]

@[simp]
theorem standardSymplecticAlgHom_generator {n : ℕ}
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k)
    (hM : M * standardForm k n * Matrix.transpose M = standardForm k n)
    (i : Fin n ⊕ Fin n) :
    standardSymplecticAlgHom k M hM
        (freeWeylGenerator (standardForm k n) i) =
      freeWeylLinearCombination M (freeWeylGenerator (standardForm k n)) i :=
  freeWeylSymplecticAlgHom_generator M (standardForm k n)
    (standardSymplecticHpres k M hM) i

end
end Stafford38.WeylSymplectic
end
