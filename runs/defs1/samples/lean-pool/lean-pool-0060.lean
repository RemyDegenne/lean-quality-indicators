@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits ZeroObject

open scoped MonObj

universe v u w

section Cokernels

variable {D : Type u}

/-- The module structure on the cokernel of the underlying
morphism. -/
@[implicit_reducible]
noncomputable def cokerModObj
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasCokernels D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (f : M ⟶ N) :
    ModObj A (cokernel f.hom) where
  smul := cokerAct A f
  one_smul := cokerAct_one A f
  mul_smul := cokerAct_mul A f

end Cokernels
end RS
end
