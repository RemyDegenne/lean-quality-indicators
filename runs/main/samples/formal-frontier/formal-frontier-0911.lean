@[expose] public section

universe u v w

open CategoryTheory

namespace ModuleCat

variable (R : Type u) [Ring R]

namespace FiniteProjective

@[simp]
theorem reprZeroIso_hom_apply (Z : Type v) [AddCommGroup Z] [Module R Z]
    [Subsingleton Z] (x : repr R Z) :
    homLinearEquiv R _ _ (reprZeroIso R Z).hom x = PUnit.unit := rfl

end FiniteProjective
end ModuleCat
end
