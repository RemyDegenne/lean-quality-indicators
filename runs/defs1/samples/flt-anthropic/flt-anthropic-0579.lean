set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace CerednikDrinfeld

namespace SpecialFormal

namespace Rigidified

open FormalODModule FormalOmega MvFormalGroup MvFormalGroup.CartierModule GradedCartierModuleData

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

variable {Φ : FormalODModule p (O ⧸ pIdeal p O)} {B : Type} [CommRing B]

section Over

variable {S : Type} [CommRing S]

def rigidNum (ι : Zp2 p →+* O)
    (hcΦ : IsCompl (Φ.gradedPiece (jbar ι) 0) (Φ.gradedPiece (jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (jbar ι) hcΦ).NMod) (ψ : O →+* B)
    (t : Rigidified p Φ B) (hOD : IsODHom (t.Φbar ψ) t.Xbar t.ρ) (g : B →+* S)
    (hcb : t.IsGradedSbar ι ψ g) (hcΦg : IsGradedPhiS (Φ := Φ) ι ψ g) :
    (Fin 2 → ℤ_[p]) →+ ((t.XbarS g).toGradedCartierModuleData (jSbar ι ψ g) hcb).NMod :=
  (((PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (jPhiS ι ψ g) hcΦg).nMap
      ((t.XbarS g).toGradedCartierModuleData (jSbar ι ψ g) hcb)
      (rhoC ψ t hOD.1 g) (rhoC_verschiebungInt ψ t hOD.1 g) (rhoC_endAct_varpiEnd ψ t hOD g)).comp
    (((Φ.toGradedCartierModuleData (jbar ι) hcΦ).nMap
        ((PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (jPhiS ι ψ g) hcΦg)
        (bcPhi (Φ := Φ) ψ g) (bcPhi_verschiebungInt (Φ := Φ) ψ g)
        (bcPhi_endAct_varpiEnd (Φ := Φ) ψ g)).comp rΦ)

end Over
end Rigidified
end SpecialFormal
end CerednikDrinfeld
end
