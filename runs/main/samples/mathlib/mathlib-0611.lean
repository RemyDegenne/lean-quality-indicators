@[expose] public section

open scoped Ring

open Topology ContinuousMap

scoped[ContinuousFunctionalCalculus]
attribute [instance] ContinuousFunctionalCalculus.compactSpace_spectrum

section Order

section Semiring

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [PartialOrder R] [StarRing R] [MetricSpace R]

variable [IsTopologicalSemiring R] [ContinuousStar R] [ContinuousSqrt R] [StarOrderedRing R]

variable [TopologicalSpace A] [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]

variable [Algebra R A] [instCFC : ContinuousFunctionalCalculus R A p]

lemma cfc_mono {f g : R → R} {a : A} (h : ∀ x ∈ spectrum R a, f x ≤ g x)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac) :
    cfc f a ≤ cfc g a := by
  by_cases ha : p a
  · rw [cfc_apply f a, cfc_apply g a]
    exact cfcHom_mono ha fun x ↦ h x.1 x.2
  · grind

end Semiring
end Order
end
