public noncomputable section

namespace TauCeti.Iwasawa

open Submodule

variable {G R : Type*} [Monoid G] [CommRing R] (δ : G →* R) (Q : Type*) [CommRing Q] [Algebra R Q]

variable {δ Q}

theorem algebraMap_mem_pseudomeasures (r : R) : algebraMap R Q r ∈ pseudomeasures δ Q :=
  mem_pseudomeasures_iff.2 fun g => ⟨(δ g - 1) * r, map_mul _ _ _⟩

end TauCeti.Iwasawa
end
