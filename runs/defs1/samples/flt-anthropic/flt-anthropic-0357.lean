set_option autoImplicit false

noncomputable section

open scoped MatrixGroups

namespace CuspForm.TWLevel

variable (N r : ℕ) {t : ℕ} (qv : Fin t → ℕ) (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
  (H : Subgroup (ZMod (level N r qv))ˣ) [NeZero N] [NeZero r] [∀ i, NeZero (qv i)]
  (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
  (α : Fin t → IsLocalRing.ResidueField 𝒪)
  (hc : OpComm N r qv S 𝒪 H) (hdc : DiaComm N r qv S 𝒪 H)

namespace HeckeRing

def act : HeckeRing N r qv S 𝒪 H θ α hc hdc →ₐ[𝒪] Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc) :=
  (heckeSubalgebra N r qv S 𝒪 H θ α hc hdc).val

end HeckeRing
end CuspForm.TWLevel
end
