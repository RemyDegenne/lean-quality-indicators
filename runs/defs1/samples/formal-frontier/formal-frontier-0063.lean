public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology.LevelCompact

universe uR uG uA

variable {R : Type uR} [CommRing R]

variable {G : Type uG} [Group G] [TopologicalSpace G]

variable [IsTopologicalGroup G] [CompactSpace G]

variable (A : Rep.{uA} R G) (L : LevelCompact A)

section AlgebraicComparison

universe u

variable {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G]

variable [IsTopologicalGroup G] [CompactSpace G]

variable (A : Rep.{u} R G) (L : LevelCompact A)

/-- Total invariants for the residual `G / S`-action are linearly equivalent
to the invariants of the original representation under the full open
subgroup.  The map forgets only redundant nested subtype data. -/
@[expose] def finiteNormTargetEquiv (S : OpenNormalSubgroup G) :
    Representation.invariants (A.quotientToInvariants S.toSubgroup).ρ ≃ₗ[R]
      openSubgroupInvariants A (⊤ : OpenSubgroup G) where
  toFun x := ⟨x.1.1, fun g ↦ by
    exact congrArg Subtype.val
      (x.2 (QuotientGroup.mk' S.toSubgroup (g : G)))⟩
  invFun x :=
    ⟨⟨x.1, fun s ↦ x.2 ⟨s.1, trivial⟩⟩,
      fun q ↦ QuotientGroup.induction_on q fun g ↦ by
        apply Subtype.ext
        exact x.2 ⟨g, trivial⟩⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end AlgebraicComparison
end ContinuousGroupCohomology.LevelCompact
end
end
