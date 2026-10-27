@[expose] public section

local notation "σₙ" => quasispectrum

open Topology ContinuousMapZero

/-- A non-unital star `R`-algebra `A` has a *continuous functional calculus* for elements
satisfying the property `p : A → Prop` if

+ for every such element `a : A` there is a non-unital star algebra homomorphism
  `cfcₙHom : C(quasispectrum R a, R)₀ →⋆ₙₐ[R] A` sending the (restriction of) the identity map
  to `a`.
+ `cfcHom` is continuous and injective and the quasispectrum of the image of function `f` is
  its range.
+ `cfcₙHom` preserves the property `p`.

The property `p` is marked as an `outParam` so that the user need not specify it. In practice,

+ for `R := ℂ`, we choose `p := IsStarNormal`,
+ for `R := ℝ`, we choose `p := IsSelfAdjoint`,
+ for `R := ℝ≥0`, we choose `p := (0 ≤ ·)`.

Instead of directly providing the data we opt instead for a `Prop` class. In all relevant cases,
the continuous functional calculus is uniquely determined, and utilizing this approach
prevents diamonds or problems arising from multiple instances. -/
class NonUnitalContinuousFunctionalCalculus (R A : Type*) (p : outParam (A → Prop))
    [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R]
    [ContinuousStar R] [NonUnitalRing A] [StarRing A] [TopologicalSpace A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : Prop where
  predicate_zero : p 0
  [compactSpace_quasispectrum : ∀ a : A, CompactSpace (σₙ R a)]
  exists_cfc_of_predicate : ∀ a, p a → ∃ φ : C(σₙ R a, R)₀ →⋆ₙₐ[R] A,
    Continuous φ ∧ Function.Injective φ ∧ φ ⟨(ContinuousMap.id R).restrict <| σₙ R a, rfl⟩ = a ∧
      (∀ f, σₙ R (φ f) = Set.range f) ∧ ∀ f, p (φ f)

end
