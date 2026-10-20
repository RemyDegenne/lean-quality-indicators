@[expose] public section

universe uR uS uT uM

open CategoryTheory CategoryTheory.Limits

open ModuleCat (FiniteProjective)

namespace KTheory

variable {R : Type uR} {S : Type uS} {T : Type uT}

variable [Ring R] [Ring S] [Ring T]

namespace ProjectiveClass

theorem map_comp (φ : R →+* S) (ψ : S →+* T) :
    map (ψ.comp φ) = (map ψ).comp (map φ) := by
  apply addHom_ext R
  intro X
  simp only [AddMonoidHom.comp_apply, map_of]
  exact (of_eq_of_equiv T _ (ModuleCat.RightExtension.compLinearEquiv φ ψ X)).symm

end ProjectiveClass
end KTheory
end
