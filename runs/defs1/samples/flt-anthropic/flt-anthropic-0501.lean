namespace P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed

namespace J1ThirteenPlaneModel end J1ThirteenPlaneModel

namespace J1ThirteenPicZeroFibreDiamond end J1ThirteenPicZeroFibreDiamond

namespace J1ThirteenPicZeroLiteralChordChain end J1ThirteenPicZeroLiteralChordChain

namespace J1ThirteenPicZeroPlaceDictionary end J1ThirteenPicZeroPlaceDictionary

namespace J1ThirteenPicZeroPlaceDictionary.PlaceConstruction end J1ThirteenPicZeroPlaceDictionary.PlaceConstruction

namespace J1ThirteenPicZeroLitPic0Comparison end J1ThirteenPicZeroLitPic0Comparison

namespace J1ThirteenX113RiemannRochRows end J1ThirteenX113RiemannRochRows

namespace MazurTate1973Mt31b end MazurTate1973Mt31b

namespace J1ThirteenX113PackageHeldRowOne end J1ThirteenX113PackageHeldRowOne

namespace MilneAvAg9bRd9DictionaryHeld3Closure end MilneAvAg9bRd9DictionaryHeld3Closure

namespace J1ThirteenX113OrdRowWellDefinedReduction end J1ThirteenX113OrdRowWellDefinedReduction

namespace MilneAvAg9bRd10EllKFinUpperRow end MilneAvAg9bRd10EllKFinUpperRow

namespace MilneAvAg9bRd11X113TowerPowerBasis end MilneAvAg9bRd11X113TowerPowerBasis

namespace Ag9b11bX113HwdUnitDischarge end Ag9b11bX113HwdUnitDischarge

namespace MilneAvAg9bRd11DictionaryBinderShrink end MilneAvAg9bRd11DictionaryBinderShrink

namespace MilneAvAg9bRd12X113AssemblyRetirement end MilneAvAg9bRd12X113AssemblyRetirement

namespace MilneAvAg9bRd12T1P1InftyResidue end MilneAvAg9bRd12T1P1InftyResidue

namespace MilneAvAg9bRd12X113LocalDatumMint end MilneAvAg9bRd12X113LocalDatumMint

namespace MilneAvAg9bRd12X113FiveRowUpgrade end MilneAvAg9bRd12X113FiveRowUpgrade

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 6400000

set_option maxHeartbeats 12800000

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

section

noncomputable section

p2m_open

namespace AlgebraicCurve

p2m_open

p2m_open_scoped

p2m_open

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]

variable (K)

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section UnitFinite

variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

variable [HasPrincipalDivisors K (RatFunc K)]

def P1DifferentialCoeffUnitFinite {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ v : Place K (RatFunc K), v ≠ placeInfty K → v.ord (v.differentialCoeff ω₀) = 0

end UnitFinite
end AlgebraicCurve
end
end
end
end
end
end MilneAvAg9bRd12X113FiveRowUpgrade
end MilneAvAg9bRd12X113LocalDatumMint
end MilneAvAg9bRd12T1P1InftyResidue
end MilneAvAg9bRd12X113AssemblyRetirement
end MilneAvAg9bRd11DictionaryBinderShrink
end Ag9b11bX113HwdUnitDischarge
end MilneAvAg9bRd11X113TowerPowerBasis
end MilneAvAg9bRd10EllKFinUpperRow
end J1ThirteenX113OrdRowWellDefinedReduction
end MilneAvAg9bRd9DictionaryHeld3Closure
end J1ThirteenX113PackageHeldRowOne
end MazurTate1973Mt31b
end J1ThirteenX113RiemannRochRows
end J1ThirteenPicZeroLitPic0Comparison
end J1ThirteenPicZeroPlaceDictionary.PlaceConstruction
end J1ThirteenPicZeroPlaceDictionary
end J1ThirteenPicZeroLiteralChordChain
end J1ThirteenPicZeroFibreDiamond
end J1ThirteenPlaneModel
end P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed
