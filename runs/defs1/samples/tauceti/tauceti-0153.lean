public noncomputable section

namespace TauCeti.Iwasawa

open Submodule

variable {G R : Type*} [Monoid G] [CommRing R] (δ : G →* R) (Q : Type*) [CommRing Q] [Algebra R Q]

variable {δ Q}

variable (δ Q)

/-- The integral pseudo-measures: the inclusion of `R` into the pseudo-measures. -/
def integral : R →ₗ[R] pseudomeasures δ Q :=
  (Algebra.linearMap R Q).codRestrict _ algebraMap_mem_pseudomeasures

end TauCeti.Iwasawa
end
