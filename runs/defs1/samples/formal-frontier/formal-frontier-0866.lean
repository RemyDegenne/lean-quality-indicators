public section

set_option warningAsError true

open CategoryTheory Order Set TopologicalSpace Topology

universe u

namespace SpectralStoneDuality

attribute [instance] SpectralCat.topology SpectralCat.spectral

namespace SpectralCat

/-- Bundle a spectral map as a morphism of spectral spaces. -/
abbrev ofHom {X Y : Type u} [TopologicalSpace X] [SpectralSpace X]
    [TopologicalSpace Y] [SpectralSpace Y] (f : SpectralMap X Y) :
    of X ⟶ of Y :=
  CategoryTheory.ConcreteCategory.ofHom (C := SpectralCat) f

end SpectralCat
end SpectralStoneDuality
end
