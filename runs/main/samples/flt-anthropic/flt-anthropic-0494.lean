namespace P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits

universe v u

p2m_open

p2m_reactivate

namespace Deformation

p2m_open

p2m_reactivate

p2m_open

namespace Deformation

p2m_open

variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]

namespace ProartinianCat

p2m_open

variable (B : ProartinianCat 𝓞)

scoped instance : PartialOrder (OpenIdx B) :=
  inferInstanceAs (PartialOrder {I : Ideal B // IsOpen (X := B) I ∧ I ≠ ⊤})

scoped instance : Nonempty (OpenIdx B) :=
  ⟨⟨maximalIdeal B, isOpen_maximalIdeal_of_isProartinian,
    (maximalIdeal.isMaximal B).ne_top⟩⟩

variable {B} (I : OpenIdx B)

scoped instance quot_nontrivial : Nontrivial (B ⧸ I.1) := Ideal.Quotient.nontrivial_iff.2 I.2.2

scoped instance quot_isLocalRing : IsLocalRing (B ⧸ I.1) :=
  .of_surjective' _ Ideal.Quotient.mk_surjective

scoped instance quot_isArtinianRing : IsArtinianRing (B ⧸ I.1) :=
  IsProartinian.isArtinianRing_quotient I.1 I.2.1

scoped instance quot_discreteTopology : DiscreteTopology (B ⧸ I.1) :=
  QuotientAddGroup.discreteTopology I.2.1

scoped instance quot_isLocalProartinianAlgebra : IsLocalProartinianAlgebra 𝓞 (B ⧸ I.1) :=
  haveI : IsLocalHom (Ideal.Quotient.mk I.1) :=
    .of_surjective _ Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (algebraMap 𝓞 (B ⧸ I.1)) := by
    have heq : algebraMap 𝓞 (B ⧸ I.1) = (Ideal.Quotient.mk I.1).comp (algebraMap 𝓞 B) := by
      rw [IsScalarTower.algebraMap_eq 𝓞 B (B ⧸ I.1), Ideal.Quotient.algebraMap_eq]
    rw [heq]
    exact RingHom.isLocalHom_comp _ _
  { }

scoped instance [Finite (ResidueField 𝓞)] : Finite (quotObj I) :=
  IsProartinian.finite_quotient_of_isOpen (R := B) I.1 I.2.1

scoped instance : DiscreteTopology (quotObj I) :=
  inferInstanceAs (DiscreteTopology (B ⧸ I.1))

@[reassoc (attr := simp)]
lemma quotMk_quotFactor {I J : OpenIdx B} (h : I ≤ J) :
    quotMk I ≫ quotFactor h = quotMk J := by
  ext b
  rfl

end ProartinianCat
end Deformation
end Deformation
end P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits
