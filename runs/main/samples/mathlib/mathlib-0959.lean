@[expose] public section

open Set Function Metric Filter

noncomputable section

open scoped NNReal Topology

namespace BoxIntegral

variable {ι : Type*}

namespace Box

variable (I J : Box ι) {x y : ι → ℝ}

variable {I J}

theorem isSome_iff : ∀ {I : WithBot (Box ι)}, I.isSome ↔ (I : Set (ι → ℝ)).Nonempty
  | ⊥ => by
    unfold Option.isSome
    simp
  | (I : Box ι) => by
    unfold Option.isSome
    simp [I.nonempty_coe]

end Box
end BoxIntegral
end
end
