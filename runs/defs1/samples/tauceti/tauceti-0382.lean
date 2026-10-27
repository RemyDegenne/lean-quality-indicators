public noncomputable section

open NumberField NumberField.InfinitePlace TauCeti

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K]

/-- **The class formation at a real place.** Its invariant on the unique nontrivial layer is the
archimedean Brauer invariant after inflation, and it is zero on every trivial layer. -/
noncomputable def infiniteClassFormationOfIsReal (w : InfinitePlace K) (hw : w.IsReal) :
    ClassFormation (unitsFormation w.Completion) where
  subsingleton_h1 := subsingleton_h1_unitsFormation
  inv := realLayerInv w hw
  inv_injective := realLayerInv_injective w hw
  range_inv := range_realLayerInv w hw
  inv_restrict := realLayerInv_cohomologyRes w hw
  inv_infl := realLayerInv_cohomologyInfl w hw
  inv_conj := realLayerInv_conjugateCohomologyIso w hw

end TauCeti.ClassFieldTheory
end
