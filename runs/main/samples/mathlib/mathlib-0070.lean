@[expose] public section

open SignType

namespace List

variable {α : Type*} [Zero α] [LinearOrder α]

lemma signVariations_congr {β : Type*} [Zero β] [LinearOrder β] {l₁ : List α} {l₂ : List β}
    (h : l₁.map sign = l₂.map sign) : signVariations l₁ = signVariations l₂ := by
  simp only [signVariations, h]

end List
end
