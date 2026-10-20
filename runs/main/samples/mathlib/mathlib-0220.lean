public section

variable {𝓕 E F : Type*}

open Filter

open scoped ENNReal NNReal Uniformity Pointwise Topology

section SeminormedGroup

variable [SeminormedGroup E] [SeminormedGroup F] {s : Set E} {a b : E} {r : ℝ}

variable [FunLike 𝓕 E F]

@[to_additive (attr := fun_prop) uniformContinuous_nnnorm]
theorem uniformContinuous_nnnorm' : UniformContinuous fun a : E => ‖a‖₊ :=
  uniformContinuous_norm'.subtype_mk _

end SeminormedGroup
end
