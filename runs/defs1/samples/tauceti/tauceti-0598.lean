public section

namespace TauCeti

universe u v w x

attribute [instance] FiniteBilinearModule.addCommGroup FiniteBilinearModule.finite

namespace FiniteBilinearModule

variable (A : FiniteBilinearModule)

namespace Hom

variable {A : FiniteBilinearModule.{u}} {B : FiniteBilinearModule.{v}}
  {C : FiniteBilinearModule.{w}}

/-- The identity morphism of a finite bilinear module. -/
def id (A : FiniteBilinearModule) : Hom A A where
  toAddMonoidHom := AddMonoidHom.id A
  map_pairing' _ _ := rfl

end Hom
end FiniteBilinearModule
end TauCeti
end
