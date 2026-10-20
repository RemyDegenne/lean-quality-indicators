@[expose] public section

universe uR uS uM

open CategoryTheory

namespace ModuleCat

variable {R : Type uR} {S : Type uS}

section Algebra

variable [CommRing R] [Ring S] [Algebra R S]

theorem restrictScalars.algebraMap_isModule (M : ModuleCat.{uM} S) :
    ((ModuleCat.restrictScalars (algebraMap R S)).obj M).isModule =
      Module.restrictScalars R S M := rfl

end Algebra
end ModuleCat
end
