@[expose] public section

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {M : Type w} {N P : Type*}

variable [L.Structure M] [L.Structure N] [L.Structure P]

open FirstOrder Cardinal

open Structure

variable (L) (M)

variable {L} {M}

variable {S : L.Substructure M}

namespace Substructure

variable (L)

variable {L} {s : Set M}

open Set

variable (L)

variable {L} (S)

variable (L) (M)

variable {L} {M}

@[simp]
theorem closure_univ : closure L (univ : Set M) = ⊤ :=
  @coe_top L M _ ▸ closure_eq ⊤

end Substructure
end Language
end FirstOrder
end
