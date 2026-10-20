public section

namespace TauCeti.Hodge

universe u

variable {W : Type u} [AddCommGroup W] [Module ℂ W]

namespace HodgeStructure

variable {V : Type*} {Vℂ : Type*} [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]

variable {ιℂ : V →ₗ[ℤ] Vℂ} [Module.Free ℤ V] [Module.Finite ℤ V] {hℂ : IsBaseChange ℂ ιℂ}

variable {n : ℤ}

variable (hs : HodgeStructure hℂ n)

namespace Hom

variable {V₁ V₂ : Type*} {W₁ W₂ : Type*} [AddCommGroup V₁] [AddCommGroup V₂]

variable [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]

variable {ι₁ : V₁ →ₗ[ℤ] W₁} {ι₂ : V₂ →ₗ[ℤ] W₂} {h₁ : IsBaseChange ℂ ι₁} {h₂ : IsBaseChange ℂ ι₂}

variable [Module.Free ℤ V₁] [Module.Finite ℤ V₁] [Module.Free ℤ V₂] [Module.Finite ℤ V₂]

variable {source : HodgeStructure h₁ n} {target : HodgeStructure h₂ n}

@[simp]
theorem dualMap_toIntLinearMap (f : Hom source target) :
    f.dualMap.toIntLinearMap = f.toIntLinearMap.dualMap :=
  (rfl)

end Hom
end HodgeStructure
end TauCeti.Hodge
end
