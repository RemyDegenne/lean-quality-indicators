@[expose] public section

universe w u v

open TensorProduct MvPolynomial

variable (R : Type u) (S : Type v) (ι : Type w) [CommRing R] [CommRing S] [Algebra R S]

namespace Algebra.Generators

variable {R S ι}

variable (P : Generators R S ι)

section Construction

/-- Construct `Generators` from a family of generators of `S`. -/
noncomputable
def ofSet {s : Set S} (hs : Algebra.adjoin R s = ⊤) : Generators R S s := by
  refine ofSurjective (Subtype.val : s → S) ?_
  rwa [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval,
    Subtype.range_coe_subtype, Set.ofPred_mem_eq]

end Construction
end Algebra.Generators
end
