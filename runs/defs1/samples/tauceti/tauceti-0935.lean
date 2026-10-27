public section

namespace TauCeti.Hodge

open IsBaseChange

universe u v w

section Polarization

variable {V : Type u} {V' : Type v} {Vℂ : Type w} {V'ℂ : Type*}

variable [AddCommGroup V] [AddCommGroup V'] [AddCommGroup Vℂ] [Module ℂ Vℂ]

variable [AddCommGroup V'ℂ] [Module ℂ V'ℂ]

variable {ιℂ : V →ₗ[ℤ] Vℂ} {ι'ℂ : V' →ₗ[ℤ] V'ℂ}

variable {hℂ : IsBaseChange ℂ ιℂ} {h'ℂ : IsBaseChange ℂ ι'ℂ} {n : ℤ}

variable {hs : HodgeStructure hℂ n} {hs' : HodgeStructure h'ℂ n}

open scoped ComplexOrder

/-- The direct sum of two polarizations of pure Hodge structures of the same weight. -/
noncomputable def Polarization.prod (P : Polarization hℂ hs) (P' : Polarization h'ℂ hs') :
    Polarization (IsBaseChange.prodMap ιℂ ι'ℂ hℂ h'ℂ)
      (hs.prod hs' (latticeConjugation_prodMap_toEquiv_apply hℂ h'ℂ)) where
  Qint := P.Qint.prod P'.Qint
  isPolarization := P.isPolarization.prod P'.isPolarization

end Polarization
end TauCeti.Hodge
end
