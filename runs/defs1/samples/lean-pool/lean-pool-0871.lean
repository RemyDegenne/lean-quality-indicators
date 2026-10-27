@[expose] public section

open Module

variable {K : Type*} [Field K]

variable {R : Subring K} [IsDiscreteValuationRing R]

namespace BruhatTits

open IsLocalRing

/-- If `b` is an `R`-basis of the lattice `L`, this is the induced
`R ⧸ ϖ R`-basis of `L ⧸ ϖ L`. -/
def _root_.Module.Basis.toQuotient [IsFractionRing R K] {L : Lattice R} (b : Basis (Fin 2) R L.M) :
    Basis (Fin 2) (ResidueField R) L.quotient :=
  let v (i : Fin 2) : L.quotient := L.toQuotient (b i)
  have hsp : ⊤ ≤ Submodule.span (ResidueField R) (Set.range v) := by
    rintro x -
    refine Quotient.inductionOn' x (fun x ↦ ?_)
    have hx : x ∈ Submodule.span R (Set.range b) := by
      simp_all
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro x hx
      obtain ⟨i, rfl⟩ := hx
      apply Submodule.subset_span
      use i
      rfl
    · exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      exact Submodule.add_mem _ hx hy
    · intro a x _ hx
      exact Submodule.smul_mem _ (Ideal.Quotient.mk _ a) hx
  have hli : LinearIndependent (ResidueField R) v := by
    apply linearIndependent_of_top_le_span_of_card_eq_finrank hsp
    exact L.quotient_finrank.symm
  Basis.mk hli hsp

end BruhatTits
end
