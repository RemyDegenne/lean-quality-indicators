@[expose] public section

noncomputable section

open CategoryTheory

variable {C : Type*} [Category* C]

namespace CategoryTheory.Limits

variable [HasZeroObject C] [HasZeroMorphisms C]

open ZeroObject

@[simp]
theorem inr_pushoutZeroZeroIso_hom (X Y : C) [HasBinaryCoproduct X Y] :
    pushout.inr _ _ ≫ (pushoutZeroZeroIso X Y).hom = coprod.inr := by
  dsimp [pushoutZeroZeroIso]
  simp

end CategoryTheory.Limits
end
end
