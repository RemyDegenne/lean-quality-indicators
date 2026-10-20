public section

open Topology

namespace TauCeti.Huber

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]

theorem isAdicHom_iff {f : A →+* B} : IsAdicHom f ↔
    ∃ (P : PairOfDefinition A) (Q : PairOfDefinition B)
      (h : ∀ a ∈ P.ringOfDefinition, f a ∈ Q.ringOfDefinition),
      P.idealOfDefinition.map (f.restrict _ _ h) = Q.idealOfDefinition :=
  ⟨fun h ↦ h.exists_pairOfDefinition, IsAdicHom.mk⟩

end TauCeti.Huber
end
