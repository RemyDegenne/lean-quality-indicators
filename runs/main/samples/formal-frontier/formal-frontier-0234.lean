public section

set_option warningAsError true

open CategoryTheory Topology

namespace CompHausAddCommGrp

universe u

@[simp]
lemma homologyMap_mk
    {X₂ X₁ X₀ Y₂ Y₁ Y₀ : CompHausAddCommGrp.{u}}
    (d₂ : X₂ ⟶ X₁) (d₁ : X₁ ⟶ X₀)
    (e₂ : Y₂ ⟶ Y₁) (e₁ : Y₁ ⟶ Y₀)
    (hd : ∀ x, d₁ (d₂ x) = 0) (he : ∀ x, e₁ (e₂ x) = 0)
    (p₂ : X₂ ⟶ Y₂) (p₁ : X₁ ⟶ Y₁) (p₀ : X₀ ⟶ Y₀)
    (h₁ : ∀ x, e₁ (p₁ x) = p₀ (d₁ x))
    (h₂ : ∀ x, e₂ (p₂ x) = p₁ (d₂ x))
    (x : kernelGroup d₁) :
    homologyMap d₂ d₁ e₂ e₁ hd he p₂ p₁ p₀ h₁ h₂
        (QuotientAddGroup.mk x) =
      QuotientAddGroup.mk (kernelMap p₁ p₀ d₁ e₁ h₁ x) :=
  rfl

end CompHausAddCommGrp
end
