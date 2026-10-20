public section

universe u

namespace EckmannHilton

variable {X : Type u}

local notation a " <" m:51 "> " b => m a b

variable {m₁ m₂ : X → X → X} {e₁ e₂ : X}

variable (h₁ : IsUnital m₁ e₁) (h₂ : IsUnital m₂ e₂)

variable (distrib : ∀ a b c d, ((a <m₂> b) <m₁> c <m₂> d) = (a <m₁> c) <m₂> b <m₁> d)

include h₁ h₂ distrib

theorem mul_assoc : Std.Associative m₂ :=
  ⟨fun a b c => by simpa [mul h₁ h₂ distrib, h₂.left_id, h₂.right_id] using distrib a b e₂ c⟩

end EckmannHilton
end
