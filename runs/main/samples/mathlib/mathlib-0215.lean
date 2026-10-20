public section

open Set

open Filter

namespace Filter

variable {α β γ δ : Type*} {ι : Sort*}

section Coprod

variable {f : Filter α} {g : Filter β}

@[gcongr, mono]
theorem coprod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) :
    f₁.coprod g₁ ≤ f₂.coprod g₂ :=
  sup_le_sup (comap_mono hf) (comap_mono hg)

end Coprod
end Filter
end
