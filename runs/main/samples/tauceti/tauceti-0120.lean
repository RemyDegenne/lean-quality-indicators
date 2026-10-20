public section

noncomputable section

namespace TauCeti

variable {X Y : Type*}

variable {c d : X × Y → EReal} {φ : X → EReal} {ψ : Y → EReal} {a : EReal}
  {x : X} {y : Y}

@[simp]
theorem cTransformSymmExtended_of_isEmpty [IsEmpty Y] (c : X × Y → EReal)
    (ψ : Y → EReal) (x : X) : cTransformSymmExtended c ψ x = ⊤ := by
  simp [cTransformSymmExtended_apply]

end TauCeti
end
end
