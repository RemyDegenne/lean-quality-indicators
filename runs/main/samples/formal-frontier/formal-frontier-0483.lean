public section

set_option warningAsError true

open CategoryTheory Order Set TopologicalSpace Topology

universe u

namespace SpectralStoneDuality

attribute [instance] SpectralCat.topology SpectralCat.spectral

namespace SpectralCat

@[ext]
theorem ext {X Y : SpectralCat} {f g : X ⟶ Y} (h : ∀ x, f.hom x = g.hom x) : f = g :=
  CategoryTheory.ConcreteCategory.hom_ext _ _ h

end SpectralCat
end SpectralStoneDuality
end
