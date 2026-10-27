public section

namespace CFSG.HardMathSupport.Dickson.KD

open CFSG.Open CFSG.LieType.BorelTits CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.GH74.GLS.Stage2.OddAut CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.LieType.Ree (ReeTag)

theorem kdCharPAt_reeG2 (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeG2 m).Valid) {p : ℕ}
    (hp3 : p = 3) : KDCharPAt p (TauCeti.CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group := by
  subst hp3
  have hm1 : 1 ≤ m :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField 3 (2 * m + 1)) = 3 ^ (2 * m + 1) :=
    GaloisField.card 3 (2 * m + 1) (by omega)
  have : CharP (GaloisField 3 (2 * m + 1)) ReeTag.G2.prime :=
    (inferInstance : CharP (GaloisField 3 (2 * m + 1)) 3)
  obtain ⟨b⟩ := CFSG.TauCetiBridge.reeG2Bridge m hv (GaloisField 3 (2 * m + 1)) hK
  have e1 : DerivedCentralQuotient (reeFixedGroup .G2 (GaloisField 3 (2 * m + 1)) reeG2Perm
      fun i => if i ∈ reeG2Long then 3 ^ m else 3 ^ (m + 1)) ≃*
        DerivedCentralQuotient (ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m) := by
    rw [ReeTag.reeGamma_eq_reeFixedGroup]
    exact MulEquiv.refl _
  obtain ⟨E⟩ := ReeTag.nonempty_derivedCentralQuotient_mulEquiv_reeGamma_G2
    (K := GaloisField 3 (2 * m + 1)) hm1 hK
  let e : TauCeti.ValidLieTypeIndex.Group ⟨.reeG2 m, hv⟩ ≃*
      ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m :=
    (b.symm.trans e1).trans E
  have : Finite (ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m) :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.finite_reeGamma
  have hcen : Subgroup.center (ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m) = ⊥ :=
    ReeTag.center_reeGamma_G2_eq_bot hK
  exact kdCharPAt_of_model e CFSG.GH74.GLS.Stage2.Bender.Thm1.ree_holds hcen
    (CFSG.GH74.GLS.Stage2.Bender.Thm1.ree_pCharData hm1 hK)

end CFSG.HardMathSupport.Dickson.KD
end
