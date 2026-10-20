public section

namespace TauCeti.Huber

variable (A : Type*) [CommRing A]

section Topological

variable [TopologicalSpace A] [NonarchimedeanRing A]

local notation "R₁" =>
  weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight

local notation "R₂" =>
  weightedRestrictedSubring (fun _ : Fin 2 ↦ ({1} : Set A)) isWeightFamily_one_weight

local notation "R±" => R₂ ⧸ laurentIdeal A

/-- The restriction from the piece `{|f| ≤ 1}` to the overlap. -/
noncomputable def laurentCoverLeToOverlap (f : A) :
    laurentCoverLe A f →ₐ[A] laurentCoverOverlap A f :=
  Ideal.Quotient.liftₐ (laurentCoverLeIdeal A f) (laurentCoverLeMap A f)
    (laurentCoverLeIdeal_le_ker A f)

end Topological
end TauCeti.Huber
end
