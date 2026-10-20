public section

namespace TauCeti

universe u v w x

attribute [instance] FiniteBilinearModule.addCommGroup FiniteBilinearModule.finite

namespace FiniteBilinearModule

variable (A : FiniteBilinearModule)

/-- A morphism of finite bilinear modules is a pairing-preserving additive homomorphism. -/
structure Hom (A : FiniteBilinearModule.{u}) (B : FiniteBilinearModule.{v}) where
  /-- The underlying additive homomorphism. -/
  toAddMonoidHom : A →+ B
  /-- The homomorphism preserves the bilinear pairing. -/
  map_pairing' : ∀ x y, B.pairing (toAddMonoidHom x) (toAddMonoidHom y) = A.pairing x y

end FiniteBilinearModule
end TauCeti
end
