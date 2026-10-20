set_option warningAsError true

@[expose] public section

namespace MvPolynomial

universe u v w

variable {ι : Type u} {κ : Type v} {R : Type w} [CommSemiring R]

/-- Substitute a separately tagged copy of `q` for each variable of `p`. -/
noncomputable def blockSubst (p : MvPolynomial ι R) (q : MvPolynomial κ R) :
    MvPolynomial (ι × κ) R :=
  bind₁ (fun i => rename (Prod.mk i) q) p

end MvPolynomial
end
