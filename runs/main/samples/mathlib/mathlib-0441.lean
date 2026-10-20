@[expose] public section

open Subgroup Subgroup.Commensurable

open scoped Pointwise

variable {G : Type*} [Group G]

@[inherit_doc]
scoped[HeckeCosetModule] notation "𝕋" => HeckeRing

namespace HeckeCosetModule

variable (Δ : Submonoid G) (H₁ H₂ : Subgroup G) (Z : Type*)

@[simp]
lemma of_apply {Δ : Submonoid G} {H₁ H₂ : Subgroup G} {Z : Type*} [Zero Z]
    (f : HeckeCoset Δ H₁ H₂ →₀ Z) (D : HeckeCoset Δ H₁ H₂) : of f D = f D :=
  rfl

end HeckeCosetModule
end
