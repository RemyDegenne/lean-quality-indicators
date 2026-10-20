@[expose] public section

noncomputable section

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory MonObj

universe u

namespace CategoryTheory.IsMonHom.Normal

open AlgebraicGeometry AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {H G : Over S} [GrpObj H] [GrpObj G]

variable (i : H ⟶ G) [Normal i]

variable {i}

variable {Q : Over S} [GrpObj Q] (q : G ⟶ Q) [IsMonHom q]

lemma relativeFppfYonedaMapHom_isLocallySurjective
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left] :
    Presheaf.IsLocallySurjective (relativeFppfTopology S)
      (relativeFppfYonedaMapHom q) := by
  constructor
  intro U s
  rcases s with ⟨s⟩
  let R : Sieve Q := Sieve.generate (Presieve.singleton q)
  have hR : R ∈ relativeFppfTopology S Q := by
    rw [GrothendieckTopology.mem_over_iff]
    change Sieve.overEquiv Q (Sieve.generate (Presieve.singleton q)) ∈
      fppfTopology Q.left
    rw [Sieve.overEquiv_generate]
    have heq : Presieve.functorPushforward (Over.forget S)
        (Presieve.singleton q) =
        (Sieve.generate (Presieve.singleton q.left)).arrows := by
      funext Y f
      apply propext
      constructor
      · rintro ⟨Z, g, h, ⟨⟩, rfl⟩
        exact ⟨G.left, h, q.left, ⟨⟩, rfl⟩
      · rintro ⟨Z, h, g, ⟨⟩, hfac⟩
        exact ⟨G, q, h, ⟨⟩, hfac.symm⟩
    rw [heq, Sieve.generate_sieve]
    exact Precoverage.generate_mem_toGrothendieck
      q.left.singleton_mem_fppfPrecoverage
  apply (relativeFppfTopology S).superset_covering _
    ((relativeFppfTopology S).pullback_stable s hR)
  intro V g hg
  rcases hg with ⟨W, a, b, ⟨⟩, hab⟩
  refine ⟨ULift.up a, ?_⟩
  change ULift.up (a ≫ q) = ULift.up (g ≫ s)
  exact congrArg ULift.up hab

end CategoryTheory.IsMonHom.Normal
end
end
