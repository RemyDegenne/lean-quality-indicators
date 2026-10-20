public section

namespace Subrepresentation

variable {A G W : Type*} [Semiring A] [Monoid G] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G W}

section Splitting

variable {A G W : Type*} [Ring A] [Monoid G] [AddCommGroup W] [Module A W]
  {ρ : Representation A G W}

@[simp]
theorem equivProdOfIsCompl_apply {ρ₁ ρ₂ : Subrepresentation ρ} (h : IsCompl ρ₁ ρ₂) (v : W) :
    equivProdOfIsCompl h v =
      (Submodule.prodEquivOfIsCompl ρ₁.toSubmodule ρ₂.toSubmodule
        (isCompl_toSubmodule.mpr h)).symm v :=
  -- `(rfl)`, not `rfl`: the body of `equivProdOfIsCompl` is not `@[expose]`d, so this must not be
  -- inferred `@[defeq]`.
  (rfl)

end Splitting
end Subrepresentation
end
