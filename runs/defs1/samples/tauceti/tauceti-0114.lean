public section

open CategoryTheory MonoidalCategory

namespace TauCeti

universe u

variable (R : Type u) [CommRing R]

namespace FiniteProjectiveModules

/-- The linear dual of a finite projective module is finite projective. -/
@[expose] def dual (M : (finiteProjectiveModules R).FullSubcategory) :
    (finiteProjectiveModules R).FullSubcategory :=
  ⟨ModuleCat.of R (Module.Dual R M.obj),
    finiteProjectiveModules_iff.mpr ⟨inferInstance, inferInstance⟩⟩

end FiniteProjectiveModules
end TauCeti
end
