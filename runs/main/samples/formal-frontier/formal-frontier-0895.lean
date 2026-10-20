@[expose] public section

universe u v

namespace CategoryTheory.Functor

open CategoryTheory.Limits

variable {A : Type u} {B : Type v}

theorem map_inf_of_preservesFiniteLimits [SemilatticeInf A]
    [SemilatticeInf B] (F : A ⥤ B) [PreservesFiniteLimits F]
    (a b : A) : F.obj (a ⊓ b) = F.obj a ⊓ F.obj b := by
  exact ((mapIsLimitOfPreservesOfIsLimit F _ _
    (Preorder.isLimitBinaryFan a b)).conePointUniqueUpToIso
      (Preorder.isLimitBinaryFan (F.obj a) (F.obj b))).to_eq

end CategoryTheory.Functor
end
