public section

open UniversalEnvelopingAlgebra

universe u v w x

namespace TauCeti.UniversalEnvelopingAlgebra

variable (R : Type u) (L : Type v) (M : Type w) (N : Type x)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

attribute [local instance 100] LieRing.ofAssociativeRing

section Dictionary

variable {R L M N}

variable [Module (_root_.UniversalEnvelopingAlgebra R L) M]

variable [IsScalarTower R (_root_.UniversalEnvelopingAlgebra R L) M]

variable [LieRingModule L M]

section Hom

variable [LieRingModule L N] [LieModule R L N]

variable [Module (_root_.UniversalEnvelopingAlgebra R L) N]

variable [IsScalarTower R (_root_.UniversalEnvelopingAlgebra R L) N]

section Equiv

/-- **The enveloping-algebra dictionary for equivalences**: Lie module equivalences are exactly
`U(L)`-linear equivalences when both actions are compatible with the canonical Lie generators.
The correspondence is the identity on underlying functions. -/
def lieModuleEquivEquivLinearEquiv
    (hM : ∀ (x : L) (m : M), ι R x • m = ⁅x, m⁆)
    (hN : ∀ (x : L) (n : N), ι R x • n = ⁅x, n⁆) :
    (M ≃ₗ⁅R,L⁆ N) ≃ (M ≃ₗ[U] N) where
  toFun e :=
    { lieModuleHomEquiv hM hN e.toLieModuleHom with
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv }
  invFun e :=
    { (lieModuleHomEquiv hM hN).symm e.toLinearMap with
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv }
  left_inv _ := rfl
  right_inv _ := rfl

end Equiv
end Hom
end Dictionary
end TauCeti.UniversalEnvelopingAlgebra
end
