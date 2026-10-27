@[expose] public section

universe uR uS uM

open CategoryTheory

namespace ModuleCat

variable {R : Type uR} {S : Type uS}

section RingHom

variable [Ring R] [Ring S] (φ : R →+* S)

namespace FiniteProjective

variable (hC : isFiniteProjective R
  ((ModuleCat.restrictScalars.{uS} φ).obj (ModuleCat.of S S)))

/-- Restrict finite projective modules along a ring homomorphism whose
canonical restricted regular scalar module is finite projective. -/
noncomputable def restrictScalars :
    FiniteProjective.{uS, uM} S ⥤ FiniteProjective.{uR, uM} R :=
  (isFiniteProjective R).lift
    ((isFiniteProjective S).ι ⋙ ModuleCat.restrictScalars.{uM} φ)
    (fun M ↦ finiteProjective_restrictScalars φ hC M.obj M.property)

end FiniteProjective
end RingHom
end ModuleCat
end
