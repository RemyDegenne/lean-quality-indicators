@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.PairStabilizerNative

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley

open CFSG.SeitzReduction CFSG.LieType.AlgebraicGroups WithConv

open scoped CFSG.ConvolutionPoints

open CFSG.LieType.Steinberg.Adjoint

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

open CFSG.StandardType.RootCentExc

open CFSG.StandardType.F4ExplicitPos.BruhatNo117 CFSG.StandardType.F4ExplicitPos.PositiveNo117

open CFSG.StandardType.F4ExplicitPos.PairNormalizerNo117

open scoped Pointwise

variable {K : Type} [Field K]

theorem f4_parabolicSubgroup_eq_mul_parabolic
    (J : Set (Fin Tag.F4.rank)) :
    (parabolicSubgroup Tag.F4 K J : Set (ModGL Tag.F4 K)) =
      (parabolicRadical Tag.F4 K J : Set (ModGL Tag.F4 K)) *
        (parabolicLevi Tag.F4 K J : Set (ModGL Tag.F4 K)) := by
  have hMN : parabolicLevi Tag.F4 K J ≤
      Subgroup.normalizer (parabolicRadical Tag.F4 K J : Set (ModGL Tag.F4 K)) :=
    le_trans (parabolicLevi_le_parabolicSubgroup J)
      (f4_parabolicSubgroup_le_normalizer_parabolicRadical J)
  rw [← f4_parabolicRadical_sup_parabolicLevi J,
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hMN]

end CFSG.StandardType.F4ExplicitPos.PairStabilizerNative
end
end
