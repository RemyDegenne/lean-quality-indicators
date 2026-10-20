namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_moduliPackage_isZariskiSheaf_eta_iff_isIsomorphic_and_natural_and_cover

attribute [-instance] MvFormalGroup.CartierModule.instAddCommGroup MvFormalGroup.CartierModule.instNeg MvFormalGroup.CartierModule.instAdd MvFormalGroup.CartierModule.instZero MvFormalGroup.WittLaw.instTendstoCofiniteProdMk MvFormalGroup.CartierModule.instModuleWittVector instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup CerednikDrinfeld.LubinTate.instIsCommMap CerednikDrinfeld.LubinTate.instFintypeGaloisFieldTwo CerednikDrinfeld.LubinTate.sigma_isComm CerednikDrinfeld.LubinTate.sigmaBar_isComm CerednikDrinfeld.BoxBasisLemma.instDecidableInBox CerednikDrinfeld.Standard.law_isComm

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

universe u v

set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace KcR4S211

namespace Sheafify

variable {p : ℕ} [Fact p.Prime] {O : Type v} [CommRing O]

section BasePoint

variable (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
  (ι : Zp2 p →+* WittVector p k)
  (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))

theorem T0_spec (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4) :
    (T0 k ι Φ hΦ hΦ4).X = (X0 p).map ((WittVector.constantCoeff : WittVector p k →+* k).comp ι) ∧
      (T0 k ι Φ hΦ hΦ4).IsAdmissible ι (WittVector.constantCoeff : WittVector p k →+* k) :=
  (exists_fieldTriple k ι Φ hΦ hΦ4).choose_spec

end BasePoint
end Sheafify
end KcR4S211
end
end P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_moduliPackage_isZariskiSheaf_eta_iff_isIsomorphic_and_natural_and_cover
