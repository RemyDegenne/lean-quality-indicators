@[expose] public section

noncomputable section

namespace LocalInfiniteResidueExtension

universe u

open scoped Polynomial

variable (R : Type u) [CommRing R] [IsLocalRing R]

lemma faithfullyFlat : Module.FaithfullyFlat R (GenericLocalExtension R) := by
  let _ := isLocalHom_algebraMap R
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

end LocalInfiniteResidueExtension
end
end
