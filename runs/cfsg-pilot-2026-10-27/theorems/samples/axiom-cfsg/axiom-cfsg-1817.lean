public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly CFSG.StandardType CFSG.StandardType.Line63 CFSG.StandardType.Line63.H5

section Ext

variable {L' R : Type} [Group L'] [Finite L'] [Group R] {ψ : L' →* R}

theorem qLift_surjective (h : zTwo L' ≤ ψ.ker) (hψ : Function.Surjective ψ) :
    Function.Surjective (qLift ψ h) := fun r => by
  obtain ⟨l, rfl⟩ := hψ r
  exact ⟨qmk L' l, qLift_mk h l⟩

end Ext
end CFSG.StandardType.USixTwo
end
