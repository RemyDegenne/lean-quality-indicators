namespace OAI

section

namespace PerfectCompleteness.FiniteConstraintMachine

open Turing

open UniqueGamesTheorem.Foundations.Complexity

open MetadataFreeSampler

noncomputable section

variable {branch : Nat → Nat} {n t q : Nat} {rows repeats : Nat → Nat}
    (hq : 0 < q)
    (large : CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t) ≤ q)

variable {v m : Nat}

theorem parsed_projection (data : MetadataFreeTape.Input branch n t rows repeats)
    (seed : Fin (LocalCompletionFamily.activeCount (result hq large data))) (a : Fin (2 * q)) :
    (LocalCompletionSerialization.projection (result_correct hq large data) seed).images[a] =
      LocalCompletionFamily.table (result hq large data) seed a :=
  LocalCompletionSerialization.projection_apply (result_correct hq large data) seed a

end
end PerfectCompleteness.FiniteConstraintMachine
end
end OAI
