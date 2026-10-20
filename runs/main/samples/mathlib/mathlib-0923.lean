@[expose] public section

variable (R G V W U : Type*) [Monoid G] [Ring R] [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [Module R V] [AddCommGroup W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [Module R W] [AddCommGroup U] [Module R U] [TopologicalSpace U]
  [IsTopologicalAddGroup U]

variable {R G V W U}

scoped[ContRepresentation] notation:30 π₁ " →ⁱL " π₂ =>
  ContIntertwiningMap π₁ π₂

namespace ContRepresentation

namespace Equiv

variable {ρ : ContRepresentation R G V} {σ : ContRepresentation R G W}
  {τ : ContRepresentation R G U} (φ : Equiv ρ σ)

@[simp] lemma refl_apply (v : V) : refl ρ v = v := rfl

end Equiv
end ContRepresentation
end
