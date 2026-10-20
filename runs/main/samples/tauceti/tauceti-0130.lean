public section

noncomputable section

namespace TauCeti.InternalGrading

universe uk uA uM uN uP

variable {k : Type uk} [Semiring k]
  {M : Type uM} [AddCommMonoid M] [Module k M]
  {N : Type uN} [AddCommMonoid N] [Module k N]
  (G : InternalGrading k M) (H : InternalGrading k N)

@[simp]
theorem homogeneousPart_add (f g : M →ₗ[k] N) (r : ℤ) :
    G.homogeneousPart H (f + g) r = G.homogeneousPart H f r + G.homogeneousPart H g r := by
  refine G.linearMap_ext fun p x hx ↦ ?_
  simp [G.homogeneousPart_apply_of_mem H (f + g) r hx,
    G.homogeneousPart_apply_of_mem H f r hx, G.homogeneousPart_apply_of_mem H g r hx]

end TauCeti.InternalGrading
end
end
