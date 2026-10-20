public section

open DirectSum

namespace Ideal.Quotient

universe u v w

variable {A : Type u} [CommRing A]

variable {ι : Type v} [DecidableEq ι] [AddMonoid ι]

variable {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A]

variable (𝒜 : ι → σ) [GradedRing 𝒜]

variable (I : Ideal A)

theorem gradedDecompose_leftInverse (hI : I.IsHomogeneous 𝒜) :
    Function.LeftInverse (DirectSum.coeAddMonoidHom (gradedComponent 𝒜 I))
      (gradedDecompose 𝒜 I hI) := by
  intro q
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [gradedDecompose_mk, coe_gradedDecomposePre]

end Ideal.Quotient
end
