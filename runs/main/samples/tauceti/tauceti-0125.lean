public section

noncomputable section

namespace TauCeti

universe u v

variable {k : Type u} {R : Type v} [CommSemiring k] [Semiring R] [Algebra k R]

namespace OreExtension

variable {σ : R →ₐ[k] R} {δ : SigmaDerivation σ}

@[simp] theorem ofFinsupp_zero : (⟨0⟩ : OreExtension σ δ) = 0 := rfl

end OreExtension
end TauCeti
end
end
