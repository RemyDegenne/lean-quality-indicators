@[expose] public noncomputable section

namespace ConwayRefinement.Standalone.CompleteHahnGerm

universe u v

variable (G : Type u) (K : Type v)

variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

variable [NoMinOrder G] [Field K]

/-- Every equation of four germs admits a four-factor refinement. -/
abbrev HasRefinement : Prop :=
  ∀ [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G]
    [Nontrivial G] [CompleteSpace G] [DenselyOrdered G] [NoMaxOrder G]
    [NoMaxOrder (FiniteArchimedeanClass G)] [CharZero K],
      ∀ a b c d : Germ G K, a * b = c * d →
        ∃ e f g h : Germ G K,
          a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h

end ConwayRefinement.Standalone.CompleteHahnGerm
end
