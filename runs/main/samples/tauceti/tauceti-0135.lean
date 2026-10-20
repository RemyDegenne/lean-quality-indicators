public section

universe uR uM uN uP

namespace TauCeti

namespace LinearSpecialContraction

variable {R : Type uR} {M : Type uM} {N : Type uN} [Semiring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {dM : Module.End R M} {dN : Module.End R N} (c : LinearSpecialContraction dM dN)
  (δ : Module.End R M) {P : Type uP} [AddCommMonoid P] [Module R P]

section Perturb

variable (hδ : (dM + δ) ∘ₗ (dM + δ) = dM ∘ₗ dM) (hU : IsUnit (1 + δ * c.homotopy))

include hδ hU

theorem perturb_proj_comp_one_add_mul :
    (c.perturb δ hδ hU).proj ∘ₗ (1 + δ * c.homotopy) = c.proj := by
  have h := congrArg (fun f ↦ c.proj ∘ₗ f ∘ₗ c.homotopy)
    (c.perturbationSeries_comp_homotopy_comp δ hU)
  simp only [LinearMap.comp_assoc, LinearMap.comp_sub, LinearMap.sub_comp] at h
  rw [perturb_proj, Module.End.mul_eq_comp, LinearMap.comp_add, Module.End.one_eq_id,
    LinearMap.comp_id]
  simp only [LinearMap.sub_comp, LinearMap.comp_assoc, h]
  abel

end Perturb
end LinearSpecialContraction
end TauCeti
end
