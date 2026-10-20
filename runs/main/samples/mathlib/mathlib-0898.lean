@[expose] public section

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

namespace LieAlgebra

open Module LieModule Set

open Submodule renaming span → span

open Submodule renaming subset_span → subset_span

namespace IsKilling

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K L H}

variable [IsTriangularizable K H L]

section CharZero

variable [CharZero K]

omit [CharZero K] in
lemma neg_root_eq {i : H.root} : -i = ⟨-i, by aesop⟩ := rfl

end CharZero
end IsKilling
end LieAlgebra
end
