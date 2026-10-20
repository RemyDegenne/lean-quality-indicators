@[expose] public section

noncomputable section

open Polynomial

open Finset

universe u v w

variable {R : Type u} {S : Type*}

namespace Ideal

open Polynomial

section CommSemiring

variable [CommSemiring R] [Semiring S]

variable (I : Ideal R[X])

section leadingCoeff

@[simp]
lemma map_C_leadingCoeff (p : Ideal R) : (map C p).leadingCoeff = p := by
  ext x
  constructor
  · intro hx
    rcases ((map C p).mem_leadingCoeff x).1 hx with ⟨f, hf, rfl⟩
    exact p.mem_map_C_iff.1 hf f.natDegree
  · intro hx
    exact ((map C p).mem_leadingCoeff x).2 ⟨C x, mem_map_of_mem C hx, leadingCoeff_C x⟩

end leadingCoeff
end CommSemiring
end Ideal
end
end
