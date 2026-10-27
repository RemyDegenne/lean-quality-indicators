public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm3Quot

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A

open scoped commutatorElement

section Members

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)} {N : Subgroup Y} [N.Normal]

theorem thm3RowsG_omegaGen_aStar_of_quot (hQ : Thm3RGroupQuotG Y) (hΦ : TypeRHyp Φ)
    {K : Subgroup Y} (hK : K ∈ Φ) (hA : ¬ AEmpty Φ K) :
    Thm3RowsG Φ (omegaGen (aStar Φ K)) ∧
      Thm3RowsG Φ (classicalInvolutionOddCore Y ⊔ omegaGen (aStar Φ K)) :=
  thm3RowsG_omegaGen_aStar hΦ (CFSG.ComponentClassification.OddCore.odd_card Y) hK hA
    (hQ Φ hΦ K hK hA)

end Members
end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm3Quot
end
