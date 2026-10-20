open Pointwise Topology

namespace TauCeti.Huber

open TauCeti.Localization

public section

variable {A : Type*} [CommRing A] [TopologicalSpace A]

namespace PairOfDefinition

/-- **The structure map `A → A⟨T/s⟩`**, the localisation map followed by the completion map. This
is the canonical ring homomorphism the universal property extends. -/
noncomputable def toCompletionLoc [IsTopologicalRing A] (P : PairOfDefinition A) (T : Set A)
    (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    A →+* UniformSpace.Completion S :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  (UniformSpace.Completion.coeRingHom).comp (algebraMap A S)

end PairOfDefinition
end
end TauCeti.Huber
