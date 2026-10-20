set_option warningAsError true

@[expose] public section

universe u v

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

universe w

universe w₁

namespace IsPrecomplete

variable {ι : Type w₁}

theorem span_finset (s : Finset R) (h : ∀ a ∈ s, IsPrecomplete (Ideal.span {a}) M) :
    IsPrecomplete (Ideal.span (s : Set R)) M := by
  classical
  have hsup := IsPrecomplete.finset_sup (fun a : R => Ideal.span {a}) s h
  rw [Finset.sup_eq_iSup] at hsup
  change IsPrecomplete (Submodule.span R (s : Set R)) M
  rw [Submodule.span_eq_iSup_of_singleton_spans]
  exact hsup

end IsPrecomplete
end
