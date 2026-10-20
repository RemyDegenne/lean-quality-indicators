public section

namespace TauCeti.Hodge

open scoped TensorProduct

universe u v w u' v' w' u'' v'' w''

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}

variable {V'ℤ : Type u'} {V'ℚ : Type v'} {V'ℂ : Type w'}

variable [AddCommGroup Vℤ] [AddCommGroup Vℚ] [Module ℚ Vℚ] [AddCommGroup Vℂ] [Module ℂ Vℂ]

variable [AddCommGroup V'ℤ] [AddCommGroup V'ℚ] [Module ℚ V'ℚ] [AddCommGroup V'ℂ] [Module ℂ V'ℂ]

variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ} {ι'ℚ : V'ℤ →ₗ[ℤ] V'ℚ} {ι'ℂ : V'ℤ →ₗ[ℤ] V'ℂ}

variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}

variable {h'ℚ : IsBaseChange ℚ ι'ℚ} {h'ℂ : IsBaseChange ℂ ι'ℂ}

namespace MixedHodgeStructure

namespace Hom

variable {source : MixedHodgeStructure hℚ hℂ} {target : MixedHodgeStructure h'ℚ h'ℂ}

variable {V''ℤ : Type u''} {V''ℚ : Type v''} {V''ℂ : Type w''}

variable [AddCommGroup V''ℤ] [AddCommGroup V''ℚ] [Module ℚ V''ℚ]

variable [AddCommGroup V''ℂ] [Module ℂ V''ℂ]

variable {ι''ℚ : V''ℤ →ₗ[ℤ] V''ℚ} {ι''ℂ : V''ℤ →ₗ[ℤ] V''ℂ}

variable {h''ℚ : IsBaseChange ℚ ι''ℚ} {h''ℂ : IsBaseChange ℂ ι''ℂ}

variable {third : MixedHodgeStructure h''ℚ h''ℂ}

theorem toLinearMap_def (f : Hom source target) :
    f.toLinearMap = rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f.toRatLinearMap :=
  (rfl)

end Hom
end MixedHodgeStructure
end TauCeti.Hodge
end
