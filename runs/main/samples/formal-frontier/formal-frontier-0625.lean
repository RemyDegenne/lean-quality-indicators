@[expose] public section

universe uR uS uT uM

open CategoryTheory CategoryTheory.Limits

open ModuleCat (FiniteProjective)

namespace KTheory

variable {R : Type uR} {S : Type uS} {T : Type uT}

variable [Ring R] [Ring S] [Ring T]

namespace K0

variable (R) in
theorem map_id : map (RingHom.id R) = AddMonoidHom.id (K0 R) := by
  apply hom_ext_ofClass R
  intro a
  simp only [map_ofClass, ProjectiveClass.map_id, AddMonoidHom.id_apply]

end K0
end KTheory
end
