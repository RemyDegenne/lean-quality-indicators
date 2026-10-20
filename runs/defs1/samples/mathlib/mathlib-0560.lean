@[expose] public section

namespace AlgebraicGeometry

universe w' w v u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

attribute [local instance] Opposite.small

namespace LocallyRingedSpace

section HasCoequalizer

variable {X Y : LocallyRingedSpace.{v}} (f g : X ⟶ Y)

/-- The explicit coequalizer cofork of locally ringed spaces. -/
noncomputable def coequalizerCofork : Cofork f g :=
  Cofork.ofπ (P := coequalizer f g)
    (homMk (coequalizer.π f.toShHom g.toShHom)
      -- Porting note: this used to be automatic
      (HasCoequalizer.coequalizer_π_stalk_isLocalHom _ _))
    (forgetToSheafedSpace.map_injective (coequalizer.condition f.toShHom g.toShHom))

end HasCoequalizer
end LocallyRingedSpace
end AlgebraicGeometry
end
