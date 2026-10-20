set_option autoImplicit false

universe u v w

noncomputable section

open WeierstrassCurve Polynomial

namespace ModularCurve

namespace KatzLevelPForm

variable {R : Type u} [CommRing R] {p : ℕ} {k l : ℤ}

@[simp] theorem swap_swap (F : KatzLevelPForm R p k) : F.swap.swap = F := rfl

end KatzLevelPForm
end ModularCurve
end
