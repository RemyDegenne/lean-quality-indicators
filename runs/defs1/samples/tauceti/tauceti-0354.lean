public section

universe v v₁ u₁ u

open CategoryTheory Opposite

variable {C : Type u₁} [Category.{v₁} C]

namespace TauCeti

namespace SheafOfModules

variable {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {M P : _root_.SheafOfModules.{v} R}

noncomputable section

/-- A morphism of sheaves of modules all of whose sections lie in a submodule `N` of the target
factors through the sheaf of modules attached to `N`. -/
def liftToSubmodule (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.val.obj U), φ.val.app U s ∈ N.toSubmodule.obj U) :
    P ⟶ N.toSheafOfModules :=
  ⟨PresheafOfModules.liftToSubmodule N.toSubmodule φ.val hφ⟩

end
end SheafOfModules
end TauCeti
end
