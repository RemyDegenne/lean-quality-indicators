@[expose] public section

namespace CategoryTheory.Functor

open Limits Triangulated Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

/-- A triangulated functor `F` is left `t`-exact if `X ≥ n` implies `F.obj X ≥ n`.
(It suffices to test this for `n := 0`, see `LeftExact.mk`.) -/
class LeftTExact (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (t₁ : TStructure C) (t₂ : TStructure D) : Prop where private mk' ::
  isGE_obj (F t₁ t₂) (X : C) (n : ℤ) [t₁.IsGE X n] : t₂.IsGE (F.obj X) n

end CategoryTheory.Functor
end
