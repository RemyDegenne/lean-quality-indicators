namespace OAI

noncomputable section

namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] Rep.hV2 Rep.instLinear

attribute [local instance 2300] DirectSum.instModule

variable {G ι : Type} [Group G]

theorem finiteStabilizerSum_projectiveDimension_one (H : ι → Subgroup G)
    [∀ i, Finite (H i)] :
    HasProjectiveDimensionLE
      (integralRepresentationSum (fun i => Rep.ind (H i).subtype (Rep.trivial ℤ (H i) ℚ))) 1 :=
  integralRepresentationSum_projectiveDimension_one _
    (fun i => finiteSubgroup_induced_rational_projectiveDimension_le_one (H i))

end PolycyclicRecognition
end
end OAI
