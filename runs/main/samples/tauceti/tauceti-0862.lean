public section

namespace Submodule

theorem map_eq_span_basis
    {R V W ι : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    [AddCommMonoid W] [Module R W]
    (p : Submodule R V) (b : Module.Basis ι R p) (f : V →ₗ[R] W) :
    p.map f = Submodule.span R (Set.range fun i => f (b i : V)) := by
  have h := congrArg (Submodule.map (f.comp p.subtype)) b.span_eq
  rw [Submodule.map_span, Submodule.map_top, LinearMap.range_comp,
    Submodule.range_subtype] at h
  simpa only [← Set.range_comp, Function.comp_def, LinearMap.comp_apply,
    Submodule.subtype_apply] using h.symm

end Submodule
end
