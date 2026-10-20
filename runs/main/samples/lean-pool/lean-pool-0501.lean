@[expose] public section

open MulOpposite Set DoubleCoset Subgroup Subgroup.Commensurable

open scoped Pointwise

namespace HeckeRing

variable {G : Type*} [Group G] (H : Subgroup G) (Δ : Submonoid G)
  (h₀ : H.toSubmonoid ≤ Δ) (h₁ : (Δ ≤ (commensurator H).toSubmonoid))

namespace HeckeCoset

variable {P : HeckePair G}

lemma ext_toSet {D₁ D₂ : HeckeCoset P} (h : HeckeCoset.toSet D₁ = HeckeCoset.toSet D₂) :
    D₁ = D₂ := Quotient.ind₂ (fun g₁ g₂ => by intro h; exact Quotient.sound h) D₁ D₂ h

end HeckeCoset
end HeckeRing
end
