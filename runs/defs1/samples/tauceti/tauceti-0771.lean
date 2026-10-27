public section

open CategoryTheory

namespace TauCeti

/-- The Young permutation module is induction of the trivial representation of the Young
subgroup. -/
noncomputable def permutationModuleIsoIndTrivial {n : ℕ} (μ : n.Partition) :
    permutationModule μ ≅
      Rep.ind (youngSubgroup μ).subtype
        (Rep.trivial ℚ (youngSubgroup μ) ℚ) :=
  (indTrivialIso ℚ (youngSubgroup μ)).symm

end TauCeti
end
