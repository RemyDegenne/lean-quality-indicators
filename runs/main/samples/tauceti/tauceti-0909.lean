public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] (p : ℕ) [ExpChar F p] (W : WeierstrassCurve.Affine F)
  [W.IsElliptic]

theorem eq_verschiebungIsogeny_iff_comp_eq {χ : Isogeny (W.map (frobenius F p)) W} :
    χ = verschiebungIsogeny p W ↔ χ.comp (relativeFrobeniusIsogeny p W) =
      mulByIntIsogenyOfNeZero W (n := p) (mod_cast expChar_ne_zero F p) :=
  ⟨fun h ↦ h ▸ verschiebungIsogeny_comp_relativeFrobeniusIsogeny p W, fun h ↦
    comp_right_injective _ (h.trans (verschiebungIsogeny_comp_relativeFrobeniusIsogeny p W).symm)⟩

end TauCeti.Isogeny
end
