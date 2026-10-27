public section

set_option warningAsError true

open CategoryTheory Topology

namespace CompHausAddCommGrp

universe u

/-- Compact Hausdorff homology of a continuous three-term complex. -/
@[expose] noncomputable def homology
    {X₂ X₁ X₀ : CompHausAddCommGrp.{u}}
    (d₂ : X₂ ⟶ X₁) (d₁ : X₁ ⟶ X₀)
    (hd : ∀ x, d₁ (d₂ x) = 0) : CompHausAddCommGrp.{u} :=
  quotientRange (boundaryToKernel d₂ d₁ hd)

end CompHausAddCommGrp
end
