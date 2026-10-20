@[expose] public section

noncomputable section

universe u v

namespace exteriorPower

variable (R : Type u) [CommRing R]

variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The determinant scalar obtained from the induced action on an invertible
exterior power. -/
noncomputable def determinant (n : ℕ) [Module.Invertible R (⋀[R]^n M)] :
    Module.End R M →* R :=
  (Module.Invertible.toModuleEndRingEquiv R (⋀[R]^n M)).symm.toMonoidHom.comp
    (mapEndomorphismMonoidHom R M n)

end exteriorPower
end
end
