@[expose] public section

open Function (Surjective)

open Polynomial

section MonoidAlgebra

variable {R : Type*} {M : Type*}

namespace AddMonoidAlgebra

open Algebra AddSubmonoid Submodule

section Span

section Ring

variable [CommRing R] [AddMonoid M]

theorem exists_finset_adjoin_eq_top [h : FiniteType R R[M]] :
    ∃ G : Finset M, Algebra.adjoin R (of' R M '' G) = ⊤ := by
  obtain ⟨S, hS⟩ := h
  let : DecidableEq M := Classical.decEq M
  use Finset.biUnion S fun f => f.coeff.support
  have : S.biUnion (fun f => f.coeff.support) = ⋃ f ∈ S, (f.coeff.support : Set M) := by
    simp only [Finset.set_biUnion_coe, Finset.coe_biUnion]
  rw [this]
  exact support_gen_of_gen' hS

end Ring
end Span
end AddMonoidAlgebra
end MonoidAlgebra
end
