@[expose] public section

universe u v w

noncomputable section

open CategoryTheory

variable {C : Type*} [Category* C]

namespace CategoryTheory.Limits

variable {X Y : C} (f g : X ⟶ Y)

variable [HasWeakEqualizer f g]

set_option backward.defeqAttrib.useBackward true in
/-- The weak equalizer built from `weakEqualizer.ι f g` is weakly limiting. -/
def weakEqualizerIsWeakEqualizer : IsWeakLimit (Fork.ofι (weakEqualizer.ι f g)
    (weakEqualizer.condition f g)) :=
  IsWeakLimit.ofIsoWeakLimit (weakLimit.isWeakLimit _) (Fork.ext (Iso.refl _) (by simp))

end CategoryTheory.Limits
end
end
