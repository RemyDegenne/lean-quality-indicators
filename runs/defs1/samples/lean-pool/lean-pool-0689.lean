@[expose] public section

namespace BGS.HasseWeil

open Submodule

noncomputable section

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The canonical map `A' / A → V / (A ⊔ B)` used in the Cech argument. -/
def cechRelativeQuotientMap (A A' B : Submodule K V) :
    (A' ⧸ relativeSubmodule A A') →ₗ[K] V ⧸ (A ⊔ B) :=
  (relativeSubmodule A A').mapQ (A ⊔ B) A'.subtype
    (comap_mono le_sup_left)

end
end BGS.HasseWeil
end
