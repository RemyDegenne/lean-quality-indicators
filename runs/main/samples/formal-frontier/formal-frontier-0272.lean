public section

set_option warningAsError true

open CategoryTheory Topology

namespace CompHausAddCommGrp

universe u

@[simp]
lemma boundaryToKernel_apply
    {X₂ X₁ X₀ : CompHausAddCommGrp.{u}}
    (d₂ : X₂ ⟶ X₁) (d₁ : X₁ ⟶ X₀)
    (hd : ∀ x, d₁ (d₂ x) = 0) (x : X₂) :
    boundaryToKernel d₂ d₁ hd x = ⟨d₂ x, hd x⟩ :=
  rfl

end CompHausAddCommGrp
end
