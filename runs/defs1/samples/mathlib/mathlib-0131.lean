@[expose] public section

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject Preadditive

variable {C D A : Type*} [Category* C] [HasShift C ℤ]
  [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
  [Category* A]

namespace Functor

variable (F : C ⥤ A)

section

/-- The connecting homomorphism in the long exact sequence attached to a homological
functor and a distinguished triangle. -/
noncomputable def homologySequenceδ
    [F.ShiftSequence ℤ] (T : Triangle C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (F.shift n₀).obj T.obj₃ ⟶ (F.shift n₁).obj T.obj₁ :=
  F.shiftMap T.mor₃ n₀ n₁ (by rw [add_comm 1, h])

end
end Functor
end CategoryTheory
end
