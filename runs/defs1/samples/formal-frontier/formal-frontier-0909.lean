public section

set_option warningAsError true

open CategoryTheory Order Set TopologicalSpace Topology

universe u

namespace SpectralStoneDuality

attribute [instance] SpectralCat.topology SpectralCat.spectral

/-- The natural lattice-side unit `A ≅ QCOuv(Spec A)` in the opposite category;
Fujiwara--Kato, *Foundations of Rigid Geometry I*, Theorem 2.2.8(1)–(2). -/
noncomputable def latticeUnitIso :
    𝟭 BddDistLatᵒᵖ ≅ spectrumFunctor ⋙ compactOpenFunctor :=
  NatIso.ofComponents latticeUnitComponent fun {X Y} f ↦ by
    apply Quiver.Hom.unop_inj
    apply BddDistLat.ext
    intro U
    exact compactOpenOrderIso_symm_naturality f.unop U

end SpectralStoneDuality
end
