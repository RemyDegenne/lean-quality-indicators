public section

namespace TauCeti

universe u v w x

attribute [instance] FiniteBilinearModule.addCommGroup FiniteBilinearModule.finite

namespace FiniteBilinearModule

variable (A : FiniteBilinearModule)

/-- An isometry of finite bilinear modules is an additive equivalence preserving the pairing. -/
structure Isometry (A : FiniteBilinearModule.{u}) (B : FiniteBilinearModule.{v}) where
  /-- The underlying additive equivalence. -/
  toAddEquiv : A ≃+ B
  /-- The equivalence preserves the bilinear pairing. -/
  map_pairing' : ∀ x y, B.pairing (toAddEquiv x) (toAddEquiv y) = A.pairing x y

end FiniteBilinearModule
end TauCeti
end
