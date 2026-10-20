public section

universe uR uM uN uP

namespace TauCeti

variable {R : Type uR} {M : Type uM} {N : Type uN} [Semiring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace LinearSpecialContraction

variable {dM : Module.End R M} {dN : Module.End R N} (c : LinearSpecialContraction dM dN)
  {P : Type uP} [AddCommMonoid P] [Module R P]

theorem incl_proj_apply (x : M) :
    c.incl (c.proj x) = x - dM (c.homotopy x) - c.homotopy (dM x) := by
  rw [← LinearMap.comp_apply, c.incl_comp_proj]
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, sub_add_eq_sub_sub]

end LinearSpecialContraction
end TauCeti
end
