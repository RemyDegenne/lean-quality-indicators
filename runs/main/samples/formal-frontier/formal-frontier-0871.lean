@[expose] public section

universe uR uS uT uM

open CategoryTheory CategoryTheory.Limits

open ModuleCat (FiniteProjective)

namespace KTheory

variable {R : Type uR} {S : Type uS} {T : Type uT}

variable [Ring R] [Ring S] [Ring T]

namespace ProjectiveClass

variable (R) in
theorem map_id : map (RingHom.id R) = AddMonoidHom.id (ProjectiveClass R) := by
  apply addHom_ext R
  intro X
  simpa only [map_of, AddMonoidHom.id_apply] using
    (of_eq_of_equiv R _ (ModuleCat.RightExtension.idLinearEquiv R X))

end ProjectiveClass
end KTheory
end
