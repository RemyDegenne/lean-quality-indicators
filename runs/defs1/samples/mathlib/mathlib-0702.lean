@[expose] public section

universe t w u v

open TensorProduct MvPolynomial

variable (R : Type u) (S : Type v) (ι : Type w) (σ : Type t) [CommRing R] [CommRing S] [Algebra R S]

namespace Algebra.Presentation

variable {R S ι σ}

variable (P : Presentation R S ι σ)

variable (R S) in
/-- An arbitrary choice of a finite presentation of a finitely presented algebra. -/
noncomputable
def ofFinitePresentation [FinitePresentation R S] :
    Presentation R S (Fin (ofFinitePresentationVars R S)) (Fin (ofFinitePresentationRels R S)) :=
  (exists_presentation_fin R S).choose_spec.choose_spec.some

end Algebra.Presentation
end
