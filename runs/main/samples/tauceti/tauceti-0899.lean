public section

namespace TauCeti

section FDRepBaseChange

open CategoryTheory MonoidalCategory TensorProduct

universe u v

variable {k : Type u} (k' : Type u) [CommRing k] [CommRing k'] [Algebra k k']
  {G : Type v} [Monoid G]

theorem baseChangeFDRepHom_add {V W : FDRep k G} (φ ψ : V ⟶ W) :
    baseChangeFDRepHom k' (φ + ψ) = baseChangeFDRepHom k' φ + baseChangeFDRepHom k' ψ :=
  Action.hom_ext _ _ <| FGModuleCat.hom_ext <| by simp [LinearMap.baseChange_add]

end FDRepBaseChange
end TauCeti
end
