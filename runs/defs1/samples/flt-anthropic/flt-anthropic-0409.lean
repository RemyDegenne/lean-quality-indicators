set_option autoImplicit false

open Function

universe u v w

namespace Deformation

section Colimit

variable (R : Type u) [CommRing R] (p : ℕ) [hp : Fact p.Prime]

variable (A : Type v) [CommRing A] [Bialgebra R A]

namespace DieudonneModule

variable {R p A}

variable {n m : ℕ}

variable (R p A) in

noncomputable def verschiebung : DieudonneModule R p A →+ DieudonneModule R p A :=
  lift R p A (fun n => (of R p A n).comp (wittHomVerschiebung R p n A)) fun n x => by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← wittHomShift_verschiebung, of_shift]

end DieudonneModule
end Colimit
end Deformation
