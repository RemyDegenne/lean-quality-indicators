noncomputable section

namespace LanglandsTunnell

open Complex NumberField

namespace Converse

variable (K : Type) [Field K]

variable [NumberField K]

theorem twistedGammaC_archOfParam_dual_const (P : RealArchParam) (u : ℂ) (a : ZMod 2) (u' : ℂ)
    (k' : ℤ) :
    twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
        (fun w hw => (archOfParamC K P w hw).dual) (fun _ _ => -u) (fun _ _ => a) (fun _ _ => -u')
        (fun _ _ => -k') =
      InfinitePlace.nrRealPlaces K • (P.dual.twist (-u) a).gammaC +
        InfinitePlace.nrComplexPlaces K • (P.dual.baseChange.twist (-u') (-k')).gammaC := by
  simp [twistedGammaC, archOfParamR, archOfParamC, Finset.sum_const, Finset.card_univ,
    RealArchParam.gammaC_baseChange_dual_twist]

end Converse
end LanglandsTunnell
end
